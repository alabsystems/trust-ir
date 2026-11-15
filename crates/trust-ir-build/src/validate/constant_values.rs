// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Module-aware constant checking without recursive descent or copied types.
//! Every descent consumes a real constant child, including when its type is
//! reached through a cyclic module table. Refine aliases are not followed.

use super::{PointerConstantRefusal, ValidationError, push_const_type_mismatch};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use trust_ir::constant::{ConstantChildren, UniformElementLists};
use trust_ir::imports::ty_structurally_eq_across;
use trust_ir::ty::FieldDef;
use trust_ir::{Constant, FatPtrKind, Global, LayoutTable, Module, ModuleFunctionCatalog, Ty};

/// The module's link-time symbol tables the typed constant walk consults,
/// built once per module rather than rescanned per constant, and the pass's
/// layout table (an element's size, a variant's inhabitedness).
pub(super) struct ConstantSymbols<'a> {
    /// The pass's one layout table, over the module the symbols name.
    layouts: &'a LayoutTable<'a>,
    /// F-058: the link-time symbols of bodyless `ExternalWeak` declarations,
    /// whose `SymbolAddr` spelling the walk restricts.
    weak: BTreeSet<&'a str>,
    /// WS3.8: every module global, by name (a name can repeat; the pointer
    /// constant rule then refuses it as ambiguous).
    globals: BTreeMap<&'a str, Vec<&'a Global>>,
    /// WS3.8: how many module functions carry each name.
    functions: BTreeMap<&'a str, usize>,
}

impl<'a> ConstantSymbols<'a> {
    pub(super) fn new(layouts: &'a LayoutTable<'a>) -> Self {
        let module = layouts.module();
        let mut globals: BTreeMap<&str, Vec<&Global>> = BTreeMap::new();
        for global in &module.globals {
            globals
                .entry(global.name.as_str())
                .or_default()
                .push(global);
        }
        let mut functions: BTreeMap<&str, usize> = BTreeMap::new();
        for func in &module.functions {
            *functions.entry(func.name.as_str()).or_default() += 1;
        }
        Self {
            layouts,
            weak: module
                .functions
                .iter()
                .filter(|func| func.is_weak_declaration())
                .map(|func| func.name.as_str())
                .collect(),
            globals,
            functions,
        }
    }
}

/// WS3.8: the two non-null pointer-constant spellings whose admission needs
/// the module tables — `SymbolAddr` at `Ref`/`PtrConst`/`PtrMut`, and
/// `Aggregate[SymbolAddr, _]` at `FatPtr(Str | Slice)`. The table-free
/// [`Constant::shape_matches_ty`] refuses both, so a pass that only has that
/// authority (the closure-capture pass) must leave the verdict to
/// [`validate_constant_against_ty`], which decides them.
pub(super) fn is_module_checked_pointer_constant(constant: &Constant, ty: &Ty) -> bool {
    match (constant, ty) {
        (Constant::SymbolAddr { .. }, Ty::Ref(_) | Ty::PtrConst(_) | Ty::PtrMut(_)) => true,
        (Constant::Aggregate(values), Ty::FatPtr(FatPtrKind::Str | FatPtrKind::Slice(_))) => {
            matches!(values.as_slice(), [Constant::SymbolAddr { .. }, _])
        }
        _ => false,
    }
}

#[derive(Clone, Copy)]
enum PathElement<'a> {
    Index(usize),
    Field(&'a str),
}

fn location(base: &str, path: &[PathElement<'_>]) -> String {
    let mut result = base.to_owned();
    for element in path {
        match element {
            PathElement::Index(index) => write!(&mut result, "[{index}]").unwrap(),
            PathElement::Field(name) => write!(&mut result, ".{name}").unwrap(),
        }
    }
    result
}

enum ChildTypes<'a> {
    Repeated(&'a Ty),
    Positional(&'a [Ty]),
    Fields(&'a [FieldDef]),
}

struct Children<'a> {
    constants: ConstantChildren<'a>,
    types: ChildTypes<'a>,
    // Named records additionally check label identity at each child, in order.
    names: Option<&'a [(String, Constant)]>,
    index: usize,
    indexed: bool,
}

struct Item<'a> {
    constant: &'a Constant,
    ty: &'a Ty,
    path: Option<PathElement<'a>>,
    wrong_name: Option<(&'a str, &'a str, usize)>,
}

impl<'a> Children<'a> {
    fn next(&mut self) -> Option<Item<'a>> {
        let index = self.index;
        let (ty, field) = match &self.types {
            ChildTypes::Repeated(ty) => (*ty, None),
            ChildTypes::Positional(types) => (types.get(index)?, None),
            ChildTypes::Fields(fields) => {
                let field = fields.get(index)?;
                (&field.ty, Some(field.name.as_str()))
            }
        };
        let constant = self.constants.next()?;
        self.index += 1;
        let wrong_name = self.names.and_then(|names| {
            let actual = names[index].0.as_str();
            let expected = field.expect("record field type");
            (actual != expected).then_some((actual, expected, index))
        });
        let path = if self.names.is_some() {
            field.map(PathElement::Field)
        } else {
            self.indexed.then_some(PathElement::Index(index))
        };
        Some(Item {
            constant,
            ty,
            path,
            wrong_name,
        })
    }
}

/// The existing typed constant walk, with one iterator frame per unfinished
/// sibling list and one shared diagnostic path. Scalar/unary paths need no
/// sibling frames; wide arrays do not enqueue their individual elements.
///
/// `symbols` names the module's bodyless `ExternalWeak` declarations
/// (F-058): a `SymbolAddr` naming one is admitted only as `addend: 0` at a
/// `Ty::Ptr` position, and an `FnDef` / closure code pointer naming one is
/// refused wherever it occurs. It also indexes the module globals a WS3.8
/// non-null pointer constant must name.
pub(super) fn validate_constant_against_ty(
    module: &Module,
    functions: &ModuleFunctionCatalog<'_>,
    symbols: &ConstantSymbols<'_>,
    constant: &Constant,
    declared_ty: &Ty,
    base: &str,
    errors: &mut Vec<ValidationError>,
) -> bool {
    let before = errors.len();
    // SPEC_RATIFICATIONS §3.1 (v50): which list nodes of this constant hold two
    // or more EQUAL elements — one bottom-up pass over the constant as
    // written (exact hash-consing), so the canonicality check below costs
    // time proportional to the text, never a length and never a re-read per
    // nesting level.
    let uniform = constant.uniform_element_lists();
    let mut current = Item {
        constant,
        ty: declared_ty,
        path: None,
        wrong_name: None,
    };
    let mut path = Vec::new();
    let mut pending = Vec::new();
    // The walk's first node is the constant itself. Placement (§27 rule C1)
    // reads this, never the path: an enum payload and a closure capture add
    // no path element, yet are not the whole value.
    let mut root = true;
    loop {
        if let Some(element) = current.path {
            path.push(element);
        }
        let children = if let Some((actual, expected, index)) = current.wrong_name {
            errors.push(ValidationError::ConstTypeMismatch {
                location: location(base, &path),
                expected: format!("field '{expected}'"),
                actual: format!("field '{actual}' at index {index}"),
            });
            None
        } else {
            check_node(
                module,
                functions,
                symbols,
                &uniform,
                current.constant,
                current.ty,
                base,
                &path,
                root,
                errors,
            )
        };
        root = false;
        if let Some(mut children) = children
            && let Some(first) = children.next()
        {
            if children.constants.len() != 0 {
                pending.push((children, path.len()));
            }
            current = first;
            continue;
        }
        loop {
            let Some((children, parent_depth)) = pending.last_mut() else {
                return errors.len() == before;
            };
            path.truncate(*parent_depth);
            if let Some(next) = children.next() {
                current = next;
                break;
            }
            pending.pop();
        }
    }
}

/// F-058: a bodyless `ExternalWeak` declaration's address is NULLABLE. A
/// `FnDef` or closure code pointer claims a callable non-null function, so it
/// may never name one (regardless of the type it sits at); a `SymbolAddr` may,
/// but only as `addend: 0` typed `Ty::Ptr` — the one spelling a producer can
/// compare against `NullPtr` before calling through it.
fn check_weak_declaration_spelling(
    functions: &ModuleFunctionCatalog<'_>,
    weak_symbols: &BTreeSet<&str>,
    constant: &Constant,
    ty: &Ty,
    here: &dyn Fn() -> String,
    errors: &mut Vec<ValidationError>,
) {
    match constant {
        Constant::FnDef(target) | Constant::Closure { func: target, .. } => {
            if let Some(function) = functions.unique(*target)
                && function.is_weak_declaration()
            {
                errors.push(ValidationError::WeakDeclarationAsFnDef {
                    location: here(),
                    function: target.index(),
                    name: function.name.clone(),
                });
            }
        }
        Constant::SymbolAddr { symbol, addend } if weak_symbols.contains(symbol.as_str()) => {
            let detail = match (ty, *addend) {
                (Ty::Ptr, 0) => return,
                (Ty::Ptr, addend) => format!("ptr with nonzero addend {addend}"),
                (ty, 0) => format!("type {ty}"),
                (ty, addend) => format!("type {ty} with nonzero addend {addend}"),
            };
            errors.push(ValidationError::WeakDeclarationAddressNotNullable {
                location: here(),
                symbol: symbol.clone(),
                detail,
            });
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)] // The walk's shared context, spelled out.
fn check_node<'a>(
    module: &'a Module,
    functions: &ModuleFunctionCatalog<'_>,
    symbols: &ConstantSymbols<'_>,
    uniform: &UniformElementLists,
    constant: &'a Constant,
    ty: &'a Ty,
    base: &str,
    path: &[PathElement<'_>],
    root: bool,
    errors: &mut Vec<ValidationError>,
) -> Option<Children<'a>> {
    let here = || location(base, path);
    let missing_type = |errors: &mut Vec<ValidationError>, type_ref| {
        errors.push(ValidationError::ConstTypeReferenceNotFound {
            location: here(),
            type_ref,
        });
    };
    let mismatch = |errors: &mut Vec<ValidationError>| {
        push_const_type_mismatch(constant, ty, &here(), errors);
    };
    check_weak_declaration_spelling(functions, &symbols.weak, constant, ty, &here, errors);
    // v25 `Char` range (moved here by the WS2.17 review): a `char` leaf is an
    // `Int` whose value must be a Unicode SCALAR value — `0..=0x10FFFF` minus
    // the surrogate block `0xD800..=0xDFFF`. It lives on THIS per-node funnel
    // rather than on the top-level declared type, so a surrogate nested in a
    // tuple / struct / record / array / enum / closure-capture constant is
    // refused too. Lowering-target subset v4 admits `Const` as one of the two
    // `Char` ORIGINS (structural condition 6) precisely because this holds:
    // before the move, `const (char, i32) = (0xD800, 0)` validated clean and
    // the subset called the module conforming.
    if let (Constant::Int(v), Ty::Char) = (constant, ty)
        && !((0..=0x10FFFF).contains(v) && !(0xD800..=0xDFFF).contains(v))
    {
        errors.push(ValidationError::ConstTypeMismatch {
            location: here(),
            expected: "a Unicode scalar value (0..=0x10FFFF minus 0xD800..=0xDFFF)".to_string(),
            actual: format!("char constant {v}"),
        });
    }
    let mut children = constant.children();
    let mut indexed = true;
    let mut names = None;
    let types = match (constant, ty) {
        // Crystal lane (E3b): an unwritten lane inhabits every lane type -- it is the absence of a
        // value, not a value of some type. WHERE it may stand (a direct lane of an
        // `Inst::Const` struct/tuple aggregate, nowhere else) is `validate_uninit_lanes`'s rule,
        // not this typed walk's.
        (Constant::Uninit, _) => return None,
        (Constant::FnDef(target), Ty::Func(signature)) => {
            let Some(function) = functions.unique(*target) else {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: here(),
                    expected: "a unique module-owned function item".into(),
                    actual: format!("missing or ambiguous func.{}", target.index()),
                });
                return None;
            };
            if function.ty != *signature {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: here(),
                    expected: format!("functy.{} for func.{}", function.ty.index(), target.index()),
                    actual: format!("functy.{}", signature.index()),
                });
            }
            return None;
        }
        (Constant::Bytes { data, utf8 }, Ty::Array(id, len)) => {
            match module.ty(*id) {
                Some(Ty::U8) => {}
                Some(other) => errors.push(ValidationError::ConstTypeMismatch {
                    location: here(),
                    expected: format!("[u8; {len}] (bytes constant)"),
                    actual: format!("array element {other}"),
                }),
                None => missing_type(errors, format!("ty.{}", id.index())),
            }
            if data.len() as u64 != *len {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: here(),
                    expected: format!("{len} bytes"),
                    actual: format!("{} bytes", data.len()),
                });
            }
            if *utf8 && std::str::from_utf8(data).is_err() {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: here(),
                    expected: "valid UTF-8 under the utf8 claim".into(),
                    actual: "invalid UTF-8 byte sequence".into(),
                });
            }
            // §3.1 (v50): raw bytes that are all one value are the uniform
            // array. A `utf8` payload carries a string claim that is part of
            // its identity, so it is not a spelling of the uniform array.
            if Constant::is_uniform_bytes(data, *utf8) {
                errors.push(ValidationError::NonCanonicalUniformArray {
                    location: here(),
                    spelling: format!(
                        "a bytes constant of {} equal bytes is spelled `splat[ {}; {} ]`",
                        data.len(),
                        data[0],
                        data.len()
                    ),
                });
            }
            return None;
        }
        (Constant::Array(values) | Constant::Aggregate(values), Ty::Array(id, len)) => {
            if values.len() as u64 != *len {
                mismatch(errors);
                return None;
            }
            let Some(ty) = module.ty(*id) else {
                missing_type(errors, format!("ty.{}", id.index()));
                return None;
            };
            // §3.1 (v50): two or more equal elements are the uniform array,
            // whose one spelling is `Constant::Splat` (decided by the one
            // bottom-up pass above, not by re-comparing subtrees here).
            if uniform.contains(constant) {
                // A scalar element is printed; a composite one by its shape
                // label, so a nest of refused lists never prints a subtree
                // once per level.
                let element = if values[0].children().len() == 0 {
                    values[0].to_string()
                } else {
                    values[0].shape_label()
                };
                errors.push(ValidationError::NonCanonicalUniformArray {
                    location: here(),
                    spelling: format!(
                        "an array of {} equal elements is spelled `splat[ {element}; {} ]`",
                        values.len(),
                        values.len()
                    ),
                });
            }
            ChildTypes::Repeated(ty)
        }
        // v50: `len` copies of ONE element — the element is checked once,
        // against the element type, and `len` is compared, never walked.
        (Constant::Splat { len: count, .. }, Ty::Array(id, len)) => {
            if count != len {
                mismatch(errors);
                return None;
            }
            let Some(ty) = module.ty(*id) else {
                missing_type(errors, format!("ty.{}", id.index()));
                return None;
            };
            if *count < 2 {
                errors.push(ValidationError::NonCanonicalUniformArray {
                    location: here(),
                    spelling: format!(
                        "a splat of {count} element(s) is spelled as the list `array[ .. ]`"
                    ),
                });
            }
            ChildTypes::Repeated(ty)
        }
        (Constant::Sequence(_), Ty::Sequence(id)) | (Constant::Set(_), Ty::Set(id, _)) => {
            let Some(ty) = module.ty(*id) else {
                missing_type(errors, format!("ty.{}", id.index()));
                return None;
            };
            ChildTypes::Repeated(ty)
        }
        (Constant::Vector(values), Ty::Vector(elem, lanes)) => {
            if values.len() != *lanes as usize {
                mismatch(errors);
                return None;
            }
            ChildTypes::Repeated(elem)
        }
        (Constant::Aggregate(values), Ty::Tuple(types)) => {
            if values.len() != types.len() {
                mismatch(errors);
                return None;
            }
            ChildTypes::Positional(types)
        }
        (Constant::Aggregate(values), Ty::Struct(id)) => {
            let Some(def) = module.struct_def(*id) else {
                missing_type(errors, format!("struct.{}", id.index()));
                return None;
            };
            if values.len() != def.fields.len() {
                mismatch(errors);
                return None;
            }
            ChildTypes::Fields(&def.fields)
        }
        (Constant::Aggregate(values), Ty::Record(id)) => {
            let Some(def) = module.record_def(*id) else {
                missing_type(errors, format!("record.{}", id.index()));
                return None;
            };
            if values.len() != def.fields.len() {
                mismatch(errors);
                return None;
            }
            ChildTypes::Fields(&def.fields)
        }
        (Constant::Record(values), Ty::Record(id)) => {
            let Some(def) = module.record_def(*id) else {
                missing_type(errors, format!("record.{}", id.index()));
                return None;
            };
            if values.len() != def.fields.len() {
                mismatch(errors);
                return None;
            }
            names = Some(values.as_slice());
            ChildTypes::Fields(&def.fields)
        }
        (Constant::Aggregate(values), Ty::Enum(id)) => {
            let Some(def) = module.enum_def(*id) else {
                missing_type(errors, format!("enum.{}", id.index()));
                return None;
            };
            let Some(discriminants) = def.effective_discriminants() else {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: here(),
                    expected: format!("enum {} with resolvable discriminants", def.name),
                    actual: "ill-formed discriminant assignment".into(),
                });
                return None;
            };
            let Some((head, payload)) = values.split_first() else {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: here(),
                    expected: "enum constant with a leading discriminant element".into(),
                    actual: "empty aggregate".into(),
                });
                return None;
            };
            let Constant::Int(discriminant) = head else {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: here(),
                    expected: "integer discriminant at element 0".into(),
                    actual: head.shape_label(),
                });
                return None;
            };
            let Some(index) = discriminants.iter().position(|value| value == discriminant) else {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: here(),
                    expected: format!("a discriminant of enum {}", def.name),
                    actual: format!("{discriminant}"),
                });
                return None;
            };
            let variant = &def.variants[index];
            // WS3.14: an uninhabited variant has no value to construct, and a
            // niche descriptor may give it no encoding at all. Refused by name,
            // before any payload check could report it as a type mismatch.
            if symbols.layouts.variant_is_uninhabited(variant) {
                errors.push(ValidationError::UninhabitedVariantConstructed {
                    location: here(),
                    enum_name: def.name.clone(),
                    variant: u32::try_from(index).unwrap_or(u32::MAX),
                    variant_name: variant.name.clone(),
                });
                return None;
            }
            if payload.len() != variant.fields.len() {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: here(),
                    expected: format!(
                        "{} payload field(s) for variant {}",
                        variant.fields.len(),
                        variant.name
                    ),
                    actual: format!("{} field(s)", payload.len()),
                });
                return None;
            }
            children.next(); // Discriminant is not a payload field.
            indexed = false;
            ChildTypes::Positional(&variant.fields)
        }
        (Constant::Closure { captures, .. }, Ty::Closure(id)) => {
            // This typed walk retains container member types. The legacy
            // closure-only pass intentionally does not; it cannot establish
            // arity for a closure nested inside a sequence/array/tuple.
            let Some(def) = module.closure_type(*id) else {
                missing_type(errors, format!("closure.{}", id.index()));
                return None;
            };
            if captures.len() != def.captures.len() {
                errors.push(ValidationError::ConstTypeMismatch {
                    location: here(),
                    expected: format!("{} captures for closure.{}", def.captures.len(), id.index()),
                    actual: format!("{} captures", captures.len()),
                });
                return None;
            }
            indexed = false;
            ChildTypes::Positional(&def.captures)
        }
        // WS3.8 (F-049): a non-null pointer constant at a typed-reference
        // position — the address of one module-defined global.
        (
            Constant::SymbolAddr { symbol, addend },
            Ty::Ref(pointee) | Ty::PtrConst(pointee) | Ty::PtrMut(pointee),
        ) => {
            if let Err(reason) =
                check_thin_pointer_constant(module, symbols, symbol, *addend, ty, pointee)
            {
                errors.push(ValidationError::PointerConstantRefused {
                    location: here(),
                    symbol: symbol.clone(),
                    ty: ty.to_string(),
                    reason,
                });
            }
            return None;
        }
        // WS3.8 (F-049): a non-null `&str` / `&[T]` constant — a window of one
        // immutable module-defined array global. `TraitObject` /
        // `ContainerLen` / `ContainerVtable` are NOT matched: their vtable or
        // container header is not checkable from the format, so the null pair
        // stays their only constant (the fallback below).
        (
            Constant::Aggregate(values),
            Ty::FatPtr(kind @ (FatPtrKind::Str | FatPtrKind::Slice(_))),
        ) if matches!(values.as_slice(), [Constant::SymbolAddr { .. }, _]) => {
            let [Constant::SymbolAddr { symbol, addend }, length] = values.as_slice() else {
                unreachable!("guarded by the arm");
            };
            if let Err(reason) =
                check_fat_pointer_constant(module, symbols, symbol, *addend, length, kind)
            {
                errors.push(ValidationError::PointerConstantRefused {
                    location: here(),
                    symbol: symbol.clone(),
                    ty: ty.to_string(),
                    reason,
                });
            }
            return None;
        }
        // PKG-U13e (§27): a content-addressed tensor, rules C1-C4. The row's
        // own digest rule (B2) is the table's (`InvalidBlobTable`).
        (Constant::TensorBlob { digest, dims }, Ty::Tensor(elem, rank)) => {
            if let Some(reason) = tensor_blob_refusal(module, root, digest, dims, elem, *rank) {
                errors.push(reason.into_error(here(), digest));
            }
            return None;
        }
        _ => {
            // Vector containers were handled above; this fallback does not
            // recursively compare any aggregate constant/type pair. A
            // pointer-width integer is checked at THIS module's pointer width
            // (`Module::pointer_bits`: the target's, or the documented 64-bit
            // default), never at a fixed 64 (SPEC_RATIFICATIONS §3.3).
            if !constant.value_matches_ty(ty, module.pointer_bits()) {
                mismatch(errors);
            }
            return None;
        }
    };
    Some(Children {
        constants: children,
        types,
        names,
        index: 0,
        indexed,
    })
}

/// Why a `Constant::TensorBlob` at `Ty::Tensor(elem, rank)` is refused, by
/// rule (§27): C1 placement (the walk's root only; a global initializer is
/// refused before the walk), C2 rank, C3 extents and element count, a
/// missing row, and C4 the row's length. A non-integer element is the
/// type's refusal (`InvalidTensorType`), not this constant's.
pub(super) enum TensorBlobRefusal {
    Rule(String),
    Missing,
}

impl TensorBlobRefusal {
    pub(super) fn into_error(
        self,
        location: String,
        digest: &trust_ir::blob::BlobDigest,
    ) -> ValidationError {
        match self {
            Self::Rule(reason) => ValidationError::InvalidTensorBlob { location, reason },
            Self::Missing => ValidationError::MissingBlob {
                location,
                digest: digest.to_hex(),
            },
        }
    }
}

pub(super) fn tensor_blob_refusal(
    module: &Module,
    root: bool,
    digest: &trust_ir::blob::BlobDigest,
    dims: &[u64],
    elem: &Ty,
    rank: u32,
) -> Option<TensorBlobRefusal> {
    if !root {
        return Some(TensorBlobRefusal::Rule(
            "(C1) nested in an aggregate, an enum payload or a closure capture: a content-addressed tensor \
             stands only as the whole value of an `Inst::Const`"
                .to_string(),
        ));
    }
    let pointer_bits = module.pointer_bits();
    if !elem.is_integer() {
        return None;
    }
    let bits = elem.bit_width_with(pointer_bits)?;
    if dims.len() as u64 != u64::from(rank) {
        return Some(TensorBlobRefusal::Rule(format!(
            "(C2) {} extents for a rank-{rank} tensor",
            dims.len()
        )));
    }
    let limit = 1u128.checked_shl(pointer_bits).unwrap_or(u128::MAX);
    if let Some(dim) = dims.iter().find(|dim| u128::from(**dim) >= limit) {
        return Some(TensorBlobRefusal::Rule(format!(
            "(C3) extent {dim} does not fit the target's {pointer_bits}-bit usize"
        )));
    }
    let count = if dims.contains(&0) {
        Some(0)
    } else {
        dims.iter()
            .try_fold(1u128, |product, dim| product.checked_mul(u128::from(*dim)))
            .filter(|count| *count < limit)
    };
    let Some(count) = count else {
        return Some(TensorBlobRefusal::Rule(format!(
            "(C3) the extents {dims:?} hold 2^{pointer_bits} elements or more"
        )));
    };
    let Some(row) = module.blob(digest) else {
        return Some(TensorBlobRefusal::Missing);
    };
    let want = count.checked_mul(u128::from(bits / 8));
    if want != Some(row.data.len() as u128) {
        return Some(TensorBlobRefusal::Rule(format!(
            "(C4) the extents {dims:?} of {elem} need {} bytes, but blob {digest} holds {}",
            want.map_or_else(|| "more than 2^128".to_string(), |n| n.to_string()),
            row.data.len()
        )));
    }
    None
}

/// WS3.8: resolve the ONE module global a non-null pointer constant names,
/// and the properties every such constant needs of it, whatever its type.
///
/// * exactly one module item carries the symbol, and it is a global — an
///   undeclared (external) symbol or a function is not an object this module
///   can type, and a symbol shared with another item has no single referent;
/// * the global is DEFINED here (`initializer: Some`): the linked walk reads
///   an initializer-less global as an extern data declaration
///   (`linked.rs`, `Export::Data`), whose memory this module cannot see;
/// * it is not thread-local: a TLS global's address is per-thread, not a
///   link-time constant;
/// * its linkage is not interposable (`trust_ir::Linkage::is_interposable`:
///   `Weak` / `LinkOnce` / `ExternalWeak`, the one table import
///   authentication also reads, proved cell by cell in gate 13): the linker
///   may bind the symbol to another definition, whose type, mutability and
///   bytes this module cannot vouch for (the WS8.14 rule for far functions;
///   the `*Odr` / `AvailableExternally` linkages stay admitted under the
///   one-definition premise).
fn target_global<'a>(
    symbols: &ConstantSymbols<'a>,
    symbol: &str,
) -> Result<&'a Global, PointerConstantRefusal> {
    let globals = symbols.globals.get(symbol).map_or(&[][..], Vec::as_slice);
    let functions = symbols.functions.get(symbol).copied().unwrap_or(0);
    let global = match globals {
        [] => return Err(PointerConstantRefusal::NotAModuleGlobal),
        [global] if functions == 0 => *global,
        _ => {
            return Err(PointerConstantRefusal::AmbiguousSymbol {
                globals: globals.len(),
                functions,
            });
        }
    };
    if global.initializer.is_none() {
        return Err(PointerConstantRefusal::GlobalNotDefined);
    }
    if global.tls.is_some() {
        return Err(PointerConstantRefusal::ThreadLocal);
    }
    if global.linkage.is_interposable() {
        return Err(PointerConstantRefusal::InterposableLinkage {
            linkage: global.linkage,
        });
    }
    Ok(global)
}

/// Test-only bridge to the complete actual ordinary symbol rule, not a copy.
#[cfg(test)]
pub(super) fn target_global_test_oracle<'a>(
    layouts: &'a LayoutTable<'a>,
    symbol: &str,
) -> Result<&'a Global, PointerConstantRefusal> {
    target_global(&ConstantSymbols::new(layouts), symbol)
}

/// WS3.8 rule 1: `SymbolAddr { symbol, addend: 0 }` at `Ref(T)` /
/// `PtrConst(T)` / `PtrMut(T)` is the address of one module global whose type
/// is structurally `T`. At `Ref(T)` the global must be immutable (a shared
/// reference tells every verifier the memory is frozen); at `PtrMut(T)` it
/// must be mutable; `PtrConst(T)` accepts either. `Rc` / `RefMut` never reach
/// here: a static is not an RC allocation, and `&'static mut` needs a
/// uniqueness proof the format lacks.
fn check_thin_pointer_constant(
    module: &Module,
    symbols: &ConstantSymbols<'_>,
    symbol: &str,
    addend: i64,
    ty: &Ty,
    pointee: &Ty,
) -> Result<(), PointerConstantRefusal> {
    let global = target_global(symbols, symbol)?;
    if addend != 0 {
        return Err(PointerConstantRefusal::NonzeroAddend { addend });
    }
    if !ty_structurally_eq_across(module, &global.ty, module, pointee) {
        return Err(PointerConstantRefusal::PointeeTypeMismatch {
            global_ty: global.ty.to_string(),
        });
    }
    let mutability_ok = match ty {
        Ty::Ref(_) => !global.mutable,
        Ty::PtrMut(_) => global.mutable,
        _ => true,
    };
    if !mutability_ok {
        return Err(PointerConstantRefusal::MutabilityMismatch {
            global_mutable: global.mutable,
        });
    }
    Ok(())
}

/// WS3.8 rule 2: `Aggregate[SymbolAddr { G, addend: k }, Int(n)]` at
/// `FatPtr(Str)` / `FatPtr(Slice(t))` is the window `[k, k + n)` (in bytes for
/// `str`, in elements for `[t]`) of one IMMUTABLE module array global.
///
/// * `Str`: `G: Array(U8, m)`, `k + n <= m`, and `G`'s initializer is
///   `Constant::Bytes { utf8: true, .. }` whose bytes `[k, k + n)` are valid
///   UTF-8 — so both ends fall on char boundaries.
/// * `Slice(t)`: `G: Array(t', m)` with `t'` structurally `t`, `k` a multiple
///   of `size_of(t)`, and `k / size_of(t) + n <= m` (a zero-sized `t` needs
///   `k == 0`).
///
/// A `&mut [T]` constant has no spelling here, so the global must be
/// immutable.
fn check_fat_pointer_constant(
    module: &Module,
    symbols: &ConstantSymbols<'_>,
    symbol: &str,
    addend: i64,
    length: &Constant,
    kind: &FatPtrKind,
) -> Result<(), PointerConstantRefusal> {
    let global = target_global(symbols, symbol)?;
    if global.mutable {
        return Err(PointerConstantRefusal::MutabilityMismatch {
            global_mutable: true,
        });
    }
    let Constant::Int(length) = length else {
        return Err(PointerConstantRefusal::InvalidLength {
            length: length.shape_label(),
        });
    };
    let Ok(length) = u64::try_from(*length) else {
        return Err(PointerConstantRefusal::InvalidLength {
            length: length.to_string(),
        });
    };
    let not_an_array = || PointerConstantRefusal::ArrayTypeMismatch {
        global_ty: global.ty.to_string(),
    };
    let Ty::Array(element, capacity) = &global.ty else {
        return Err(not_an_array());
    };
    let capacity = *capacity;
    let out_of_bounds = || PointerConstantRefusal::WindowOutOfBounds {
        offset: addend,
        length,
        capacity,
    };
    let Ok(offset) = u64::try_from(addend) else {
        return Err(out_of_bounds());
    };
    let element_ty = module.ty(*element).ok_or_else(not_an_array)?;
    match kind {
        FatPtrKind::Str => {
            if *element_ty != Ty::U8 {
                return Err(not_an_array());
            }
            if u128::from(offset) + u128::from(length) > u128::from(capacity) {
                return Err(out_of_bounds());
            }
            let Some(Constant::Bytes { data, utf8: true }) = &global.initializer else {
                return Err(PointerConstantRefusal::NotUtf8Bytes);
            };
            // `offset + length <= capacity == data.len()` (the initializer is
            // checked against the global's type by the same walk), but a
            // mismatched initializer must not panic here.
            let window = usize::try_from(offset)
                .ok()
                .zip(usize::try_from(offset + length).ok())
                .and_then(|(start, end)| data.get(start..end))
                .ok_or_else(out_of_bounds)?;
            if std::str::from_utf8(window).is_err() {
                return Err(PointerConstantRefusal::NotOnCharBoundary);
            }
            Ok(())
        }
        FatPtrKind::Slice(slice_element) => {
            let Some(slice_element_ty) = module.ty(*slice_element) else {
                return Err(not_an_array());
            };
            if !ty_structurally_eq_across(module, element_ty, module, slice_element_ty) {
                return Err(not_an_array());
            }
            let size = symbols
                .layouts
                .ty_layout(element_ty)
                .map_err(|_| PointerConstantRefusal::ElementLayoutUnknown)?
                .size_bits
                / 8;
            let start = match size {
                0 if offset == 0 => 0,
                0 => return Err(out_of_bounds()),
                size if offset % size == 0 => offset / size,
                size => {
                    return Err(PointerConstantRefusal::MisalignedOffset {
                        offset: addend,
                        element_size: size,
                    });
                }
            };
            if u128::from(start) + u128::from(length) > u128::from(capacity) {
                return Err(out_of_bounds());
            }
            Ok(())
        }
        _ => unreachable!("only Str and Slice reach the fat pointer-constant rule"),
    }
}
