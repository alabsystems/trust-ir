// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `trust-ir run` — execute a (multi-module) TrustIr image under the reference
//! interpreter (`trust_ir::interpret`) and print the entry function's return
//! value(s).
//!
//! The reference interpreter executes exactly ONE `Module`, resolving calls by
//! `FuncId` inside it, so a program emitted one-module-per-function
//! ("emit-each") must first be LINKED into a single executable image. The
//! linker here merges modules at the semantic level the interpreter needs:
//!
//!   * functions are keyed by NAME; a bodied definition wins over a bodyless
//!     declaration; duplicate bodied definitions must be structurally
//!     identical after ID remapping (they are deduped); conflicting bodies
//!     are an error;
//!   * every per-module arena reference (`TyId`, `FuncTyId`, `StructId`,
//!     `EnumId`, `RecordId`, `ClosureTyId`, `PredId`, `UnivId`, `GlobalId`,
//!     `FuncId`, file indices) is remapped into merged,
//!     structurally-deduplicated arenas;
//!   * globals are keyed by name and must agree structurally;
//!   * proof obligations/certificates are NOT carried over — the linked
//!     image is an execution artifact, not a verification artifact.
//!
//! Functions that remain bodyless after linking are true externs. A small,
//! name-classified set is synthesized as executable builtin bodies in plain
//! TrustIr (so the interpreter itself is untouched):
//!
//!   * Rust allocator shims `__rust_alloc` / `__rust_alloc_zeroed` /
//!     `__rust_realloc` / `__rust_dealloc` mapped onto `HeapAlloc`/`Dealloc`
//!     over the interpreter's own memory model, plus the C `memcpy` /
//!     `memmove` / `memset` / `memcmp` byte loops;
//!   * `core::intrinsics` compute leaves the frontend declares but does not
//!     define: `ctpop`, `ctlz(_nonzero)`, `cttz(_nonzero)`,
//!     `unchecked_funnel_shl` — synthesized as branch-free bit ladders;
//!   * everything else becomes a TRAP STUB: a body whose single block lives
//!     in the reserved id range starting at [`TRAP_BLOCK_BASE`] and executes
//!     `Unreachable`. When the interpreter reports an error in that range the
//!     CLI maps the block id back to the extern's name — a pure program
//!     reaching one is a finding (panic path taken, or emitted IR diverging
//!     from the native binary).

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use trust_ir::constant::Constant;
use trust_ir::inst::{
    AllocOrigin, BinOp, BindingFrameDef, BindingSlot, CastOp, ICmpOp, Inst, SwitchCase, UnOp,
};
use trust_ir::interpret::{
    InterpretError, InterpretOptions, InterpretOutcome, InterpretValue, InterpretValueKind,
    Interpreter,
};
use trust_ir::node::InstrNode;
use trust_ir::ty::{ClosureTy, FatPtrKind, FuncTy, Ty};
use trust_ir::value::{
    BlockId, ClosureTyId, EnumId, FuncId, FuncTyId, GlobalId, PredId, RecordId, SourceSpan,
    StructId, TyId, UnivId, ValueId,
};
use trust_ir::{Block, Function, Global, Linkage, Module, Pred};

use crate::{EXIT_IO, EXIT_OK, EXIT_USER, Format, decode_module, read_input};

/// First block id of the reserved trap-stub range. A synthesized trap stub's
/// single block gets id `TRAP_BLOCK_BASE + k`; an interpreter error located in
/// that range is mapped back to stub `k`'s extern name for the diagnostic.
/// Real producer blocks are small dense indices, far below this.
const TRAP_BLOCK_BASE: u32 = 0xF000_0000;

/// Host stack for the interpreter thread. `execute_function_inner` recurses on
/// the Rust stack per interpreted call frame, so deep IR recursion (Ackermann,
/// Collatz chains) needs more than the default main-thread allowance.
const RUN_STACK_BYTES: usize = 512 * 1024 * 1024;

// ---------------------------------------------------------------------------
// Input collection
// ---------------------------------------------------------------------------

/// Expand the argument list into concrete module paths. A directory expands
/// to its `*.trust_ir` files in sorted order; files pass through unchanged.
fn collect_module_paths(paths: &[PathBuf]) -> Result<Vec<PathBuf>, String> {
    let mut out = Vec::new();
    for path in paths {
        if path.is_dir() {
            let mut entries: Vec<PathBuf> = fs::read_dir(path)
                .map_err(|e| format!("read dir {}: {e}", path.display()))?
                .filter_map(|entry| entry.ok().map(|e| e.path()))
                .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("trust_ir"))
                .collect();
            entries.sort();
            if entries.is_empty() {
                return Err(format!(
                    "{}: directory contains no .trust_ir modules",
                    path.display()
                ));
            }
            out.extend(entries);
        } else {
            out.push(path.clone());
        }
    }
    if out.is_empty() {
        return Err("no input modules".to_string());
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Linker: merge N modules into one executable image
// ---------------------------------------------------------------------------

/// Memoization state for one source-module arena entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Memo<T> {
    Unvisited,
    /// Currently being remapped (cycle guard for recursive arenas).
    Visiting,
    Done(T),
}

/// Per-source-module remap context. All tables map LOCAL arena indices to
/// MERGED ids.
struct ModuleCtx<'a> {
    source: &'a Module,
    /// Diagnostic label (the module's file path).
    label: String,
    /// Local function index -> merged `FuncId` (assigned by name, phase A).
    func_map: Vec<FuncId>,
    ty_memo: Vec<Memo<TyId>>,
    pred_memo: Vec<Memo<PredId>>,
    univ_memo: Vec<Memo<UnivId>>,
    functy_memo: Vec<Memo<FuncTyId>>,
    struct_memo: Vec<Memo<StructId>>,
    enum_memo: Vec<Memo<EnumId>>,
    record_memo: Vec<Memo<RecordId>>,
    closure_memo: Vec<Memo<ClosureTyId>>,
    global_memo: Vec<Memo<GlobalId>>,
    /// Local file index -> merged file index.
    file_map: Vec<u32>,
}

impl<'a> ModuleCtx<'a> {
    fn new(label: String, source: &'a Module, func_map: Vec<FuncId>) -> Self {
        Self {
            source,
            label,
            func_map,
            ty_memo: vec![Memo::Unvisited; source.types.len()],
            pred_memo: vec![Memo::Unvisited; source.predicates.len()],
            univ_memo: vec![Memo::Unvisited; source.universes.len()],
            functy_memo: vec![Memo::Unvisited; source.func_types.len()],
            struct_memo: vec![Memo::Unvisited; source.structs.len()],
            enum_memo: vec![Memo::Unvisited; source.enums.len()],
            record_memo: vec![Memo::Unvisited; source.records.len()],
            closure_memo: vec![Memo::Unvisited; source.closure_types.len()],
            global_memo: vec![Memo::Unvisited; source.globals.len()],
            file_map: Vec::new(),
        }
    }

    fn err(&self, message: impl std::fmt::Display) -> String {
        format!("link {}: {message}", self.label)
    }
}

/// The linker: merged arenas plus structural dedup tables.
struct Linker {
    merged: Module,
    /// Function name -> merged id (phase A).
    func_ids: HashMap<String, FuncId>,
    /// Merged function slots, parallel to the `FuncId` space. Filled in
    /// phase B; every slot is `Some` once all modules are placed.
    functions: Vec<Option<Function>>,
    functy_dedup: HashMap<(Vec<Ty>, Vec<Ty>, bool), FuncTyId>,
    type_dedup: HashMap<Ty, TyId>,
    global_ids: HashMap<String, GlobalId>,
    struct_ids: HashMap<String, StructId>,
    enum_ids: HashMap<String, EnumId>,
    record_ids: HashMap<String, RecordId>,
}

impl Linker {
    fn new() -> Self {
        Self {
            merged: Module::new("linked"),
            func_ids: HashMap::new(),
            functions: Vec::new(),
            functy_dedup: HashMap::new(),
            type_dedup: HashMap::new(),
            global_ids: HashMap::new(),
            struct_ids: HashMap::new(),
            enum_ids: HashMap::new(),
            record_ids: HashMap::new(),
        }
    }

    // -- arena remaps (memoized per source module, deduped in merged) -------

    fn intern_type(&mut self, ty: Ty) -> TyId {
        if let Some(id) = self.type_dedup.get(&ty) {
            return *id;
        }
        let id = TyId::new(self.merged.types.len() as u32);
        self.merged.types.push(ty.clone());
        self.type_dedup.insert(ty, id);
        id
    }

    fn ty_id(&mut self, ctx: &mut ModuleCtx<'_>, id: TyId) -> Result<TyId, String> {
        let i = id.as_usize();
        match ctx.ty_memo.get(i) {
            Some(Memo::Done(mapped)) => return Ok(*mapped),
            Some(Memo::Visiting) => {
                return Err(ctx.err(format!("ty.{i} participates in a type-arena cycle")));
            }
            Some(Memo::Unvisited) => {}
            None => return Err(ctx.err(format!("ty.{i} is out of range"))),
        }
        ctx.ty_memo[i] = Memo::Visiting;
        let ty = ctx.source.types[i].clone();
        let remapped = self.ty(ctx, &ty)?;
        let mapped = self.intern_type(remapped);
        ctx.ty_memo[i] = Memo::Done(mapped);
        Ok(mapped)
    }

    fn univ_id(&mut self, ctx: &mut ModuleCtx<'_>, id: UnivId) -> Result<UnivId, String> {
        let i = id.as_usize();
        match ctx.univ_memo.get(i) {
            Some(Memo::Done(mapped)) => return Ok(*mapped),
            Some(Memo::Visiting) => {
                return Err(ctx.err(format!("univ.{i} participates in a universe-arena cycle")));
            }
            Some(Memo::Unvisited) => {}
            None => return Err(ctx.err(format!("univ.{i} is out of range"))),
        }
        ctx.univ_memo[i] = Memo::Visiting;
        let universe = ctx.source.universes[i].clone();
        if !universe.is_canonical() {
            return Err(ctx.err(format!("univ.{i} is not canonical")));
        }
        if ctx.source.universes[..i].contains(&universe) {
            return Err(ctx.err(format!("univ.{i} duplicates an earlier universe")));
        }
        let mapped = self
            .merged
            .intern_universe(universe)
            .ok_or_else(|| ctx.err(format!("univ.{i} cannot be interned")))?;
        ctx.univ_memo[i] = Memo::Done(mapped);
        Ok(mapped)
    }

    fn pred_id(&mut self, ctx: &mut ModuleCtx<'_>, id: PredId) -> Result<PredId, String> {
        let i = id.as_usize();
        match ctx.pred_memo.get(i) {
            Some(Memo::Done(mapped)) => return Ok(*mapped),
            Some(Memo::Visiting) => {
                return Err(ctx.err(format!("pred.{i} participates in a predicate-arena cycle")));
            }
            Some(Memo::Unvisited) => {}
            None => return Err(ctx.err(format!("pred.{i} is out of range"))),
        }
        ctx.pred_memo[i] = Memo::Visiting;
        let pred = ctx.source.predicates[i].clone();
        if !pred.is_canonical() {
            return Err(ctx.err(format!("pred.{i} is not canonical")));
        }
        if ctx.source.predicates[..i].contains(&pred) {
            return Err(ctx.err(format!("pred.{i} duplicates an earlier predicate")));
        }
        let remapped = match pred {
            Pred::InUniverse(universe, space) => {
                Pred::InUniverse(self.univ_id(ctx, universe)?, space)
            }
            Pred::Conj(children) => {
                if children.iter().any(|child| child.as_usize() >= i) {
                    return Err(ctx.err(format!("pred.{i} cites a non-antecedent predicate")));
                }
                Pred::Conj(
                    children
                        .into_iter()
                        .map(|child| self.pred_id(ctx, child))
                        .collect::<Result<_, _>>()?,
                )
            }
            Pred::Disj(children) => {
                if children.iter().any(|child| child.as_usize() >= i) {
                    return Err(ctx.err(format!("pred.{i} cites a non-antecedent predicate")));
                }
                Pred::Disj(
                    children
                        .into_iter()
                        .map(|child| self.pred_id(ctx, child))
                        .collect::<Result<_, _>>()?,
                )
            }
            other => other,
        };
        let mapped = self
            .merged
            .intern_pred(remapped)
            .ok_or_else(|| ctx.err(format!("pred.{i} cannot be interned")))?;
        ctx.pred_memo[i] = Memo::Done(mapped);
        Ok(mapped)
    }

    fn functy_id(&mut self, ctx: &mut ModuleCtx<'_>, id: FuncTyId) -> Result<FuncTyId, String> {
        let i = id.as_usize();
        match ctx.functy_memo.get(i) {
            Some(Memo::Done(mapped)) => return Ok(*mapped),
            Some(Memo::Visiting) => {
                return Err(ctx.err(format!("functy.{i} participates in a signature cycle")));
            }
            Some(Memo::Unvisited) => {}
            None => return Err(ctx.err(format!("functy.{i} is out of range"))),
        }
        ctx.functy_memo[i] = Memo::Visiting;
        let functy = ctx.source.func_types[i].clone();
        let params = self.tys(ctx, &functy.params)?;
        let returns = self.tys(ctx, &functy.returns)?;
        let key = (params.clone(), returns.clone(), functy.is_vararg);
        let mapped = if let Some(existing) = self.functy_dedup.get(&key) {
            *existing
        } else {
            let mapped = FuncTyId::new(self.merged.func_types.len() as u32);
            self.merged.func_types.push(FuncTy {
                params,
                returns,
                is_vararg: functy.is_vararg,
            });
            self.functy_dedup.insert(key, mapped);
            mapped
        };
        ctx.functy_memo[i] = Memo::Done(mapped);
        Ok(mapped)
    }

    /// Struct remap: reserve-then-fill so self-referential layouts (via
    /// pointer indirection) terminate; keyed by name across modules with a
    /// post-fill structural-equality check.
    fn struct_id(&mut self, ctx: &mut ModuleCtx<'_>, id: StructId) -> Result<StructId, String> {
        let i = id.as_usize();
        match ctx.struct_memo.get(i) {
            Some(Memo::Done(mapped)) => return Ok(*mapped),
            Some(Memo::Visiting) => unreachable!("struct memo is reserved before field remap"),
            Some(Memo::Unvisited) => {}
            None => return Err(ctx.err(format!("struct.{i} is out of range"))),
        }
        let def = ctx.source.structs[i].clone();
        let (mapped, fresh) = match self.struct_ids.get(&def.name) {
            Some(existing) => (*existing, false),
            None => {
                let mapped = StructId::new(self.merged.structs.len() as u32);
                let mut placeholder = def.clone();
                placeholder.id = mapped;
                placeholder.fields = Vec::new();
                self.merged.structs.push(placeholder);
                self.struct_ids.insert(def.name.clone(), mapped);
                (mapped, true)
            }
        };
        ctx.struct_memo[i] = Memo::Done(mapped);
        let mut remapped = def;
        remapped.id = mapped;
        for field in &mut remapped.fields {
            field.ty = self.ty(ctx, &field.ty)?;
        }
        if fresh {
            self.merged.structs[mapped.as_usize()] = remapped;
        } else if self.merged.structs[mapped.as_usize()] != remapped {
            return Err(ctx.err(format!(
                "conflicting definitions of struct {}",
                remapped.name
            )));
        }
        Ok(mapped)
    }

    fn enum_id(&mut self, ctx: &mut ModuleCtx<'_>, id: EnumId) -> Result<EnumId, String> {
        let i = id.as_usize();
        match ctx.enum_memo.get(i) {
            Some(Memo::Done(mapped)) => return Ok(*mapped),
            Some(Memo::Visiting) => unreachable!("enum memo is reserved before variant remap"),
            Some(Memo::Unvisited) => {}
            None => return Err(ctx.err(format!("enum.{i} is out of range"))),
        }
        let def = ctx.source.enums[i].clone();
        let (mapped, fresh) = match self.enum_ids.get(&def.name) {
            Some(existing) => (*existing, false),
            None => {
                let mapped = EnumId::new(self.merged.enums.len() as u32);
                let mut placeholder = def.clone();
                placeholder.id = mapped;
                placeholder.variants = Vec::new();
                self.merged.enums.push(placeholder);
                self.enum_ids.insert(def.name.clone(), mapped);
                (mapped, true)
            }
        };
        ctx.enum_memo[i] = Memo::Done(mapped);
        let mut remapped = def;
        remapped.id = mapped;
        for variant in &mut remapped.variants {
            variant.fields = self.tys(ctx, &variant.fields)?;
        }
        if fresh {
            self.merged.enums[mapped.as_usize()] = remapped;
        } else if self.merged.enums[mapped.as_usize()] != remapped {
            return Err(ctx.err(format!("conflicting definitions of enum {}", remapped.name)));
        }
        Ok(mapped)
    }

    fn record_id(&mut self, ctx: &mut ModuleCtx<'_>, id: RecordId) -> Result<RecordId, String> {
        let i = id.as_usize();
        match ctx.record_memo.get(i) {
            Some(Memo::Done(mapped)) => return Ok(*mapped),
            Some(Memo::Visiting) => unreachable!("record memo is reserved before field remap"),
            Some(Memo::Unvisited) => {}
            None => return Err(ctx.err(format!("record.{i} is out of range"))),
        }
        let def = ctx.source.records[i].clone();
        let (mapped, fresh) = match self.record_ids.get(&def.name) {
            Some(existing) => (*existing, false),
            None => {
                let mapped = RecordId::new(self.merged.records.len() as u32);
                let mut placeholder = def.clone();
                placeholder.id = mapped;
                placeholder.fields = Vec::new();
                self.merged.records.push(placeholder);
                self.record_ids.insert(def.name.clone(), mapped);
                (mapped, true)
            }
        };
        ctx.record_memo[i] = Memo::Done(mapped);
        let mut remapped = def;
        remapped.id = mapped;
        for field in &mut remapped.fields {
            field.ty = self.ty(ctx, &field.ty)?;
        }
        if fresh {
            self.merged.records[mapped.as_usize()] = remapped;
        } else if self.merged.records[mapped.as_usize()] != remapped {
            return Err(ctx.err(format!(
                "conflicting definitions of record {}",
                remapped.name
            )));
        }
        Ok(mapped)
    }

    /// Closure types are unnamed, so cross-module structural dedup of a
    /// CYCLIC closure type is not attempted: each module's closure type is
    /// appended (reserve-then-fill). Duplicates across modules are therefore
    /// possible; that only matters to `Ty` equality of values crossing
    /// modules, which the emit-each corpus never exercises.
    fn closure_id(
        &mut self,
        ctx: &mut ModuleCtx<'_>,
        id: ClosureTyId,
    ) -> Result<ClosureTyId, String> {
        let i = id.as_usize();
        match ctx.closure_memo.get(i) {
            Some(Memo::Done(mapped)) => return Ok(*mapped),
            Some(Memo::Visiting) => unreachable!("closure memo is reserved before capture remap"),
            Some(Memo::Unvisited) => {}
            None => return Err(ctx.err(format!("closurety.{i} is out of range"))),
        }
        let def = ctx.source.closure_types[i].clone();
        let mapped = ClosureTyId::new(self.merged.closure_types.len() as u32);
        self.merged.closure_types.push(ClosureTy {
            func: FuncTyId::new(0),
            captures: Vec::new(),
        });
        ctx.closure_memo[i] = Memo::Done(mapped);
        let func = self.functy_id(ctx, def.func)?;
        let captures = self.tys(ctx, &def.captures)?;
        self.merged.closure_types[mapped.as_usize()] = ClosureTy { func, captures };
        Ok(mapped)
    }

    /// Globals are keyed by name; a name collision requires the remapped
    /// definitions to agree exactly.
    fn global_id(&mut self, ctx: &mut ModuleCtx<'_>, id: GlobalId) -> Result<GlobalId, String> {
        let i = id.as_usize();
        match ctx.global_memo.get(i) {
            Some(Memo::Done(mapped)) => return Ok(*mapped),
            Some(Memo::Visiting) => {
                return Err(ctx.err(format!("global #{i} references itself")));
            }
            Some(Memo::Unvisited) => {}
            None => return Err(ctx.err(format!("global #{i} is out of range"))),
        }
        ctx.global_memo[i] = Memo::Visiting;
        let mut def = ctx.source.globals[i].clone();
        def.ty = self.ty(ctx, &def.ty)?;
        def.initializer = def
            .initializer
            .as_ref()
            .map(|init| self.constant(ctx, init))
            .transpose()?;
        let mapped = if let Some(existing) = self.global_ids.get(&def.name) {
            let existing = *existing;
            if self.merged.globals[existing.as_usize()] != def {
                return Err(ctx.err(format!("conflicting definitions of global @{}", def.name)));
            }
            existing
        } else {
            let mapped = GlobalId::new(self.merged.globals.len() as u32);
            self.global_ids.insert(def.name.clone(), mapped);
            self.merged.globals.push(def);
            mapped
        };
        ctx.global_memo[i] = Memo::Done(mapped);
        Ok(mapped)
    }

    fn func_id(&self, ctx: &ModuleCtx<'_>, id: FuncId) -> Result<FuncId, String> {
        ctx.func_map
            .get(id.as_usize())
            .copied()
            .ok_or_else(|| ctx.err(format!("func.{} is out of range", id.index())))
    }

    // -- structural remaps ---------------------------------------------------

    fn tys(&mut self, ctx: &mut ModuleCtx<'_>, tys: &[Ty]) -> Result<Vec<Ty>, String> {
        tys.iter().map(|ty| self.ty(ctx, ty)).collect()
    }

    fn ty(&mut self, ctx: &mut ModuleCtx<'_>, ty: &Ty) -> Result<Ty, String> {
        Ok(match ty {
            // Scalars and other id-free leaves pass through unchanged.
            Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::Error
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::Unit
            | Ty::Never => ty.clone(),
            Ty::Vector(elem, lanes) => Ty::Vector(Box::new(self.ty(ctx, elem)?), *lanes),
            Ty::FatPtr(kind) => Ty::FatPtr(match kind {
                FatPtrKind::Slice(elem) => FatPtrKind::Slice(self.ty_id(ctx, *elem)?),
                FatPtrKind::Str => FatPtrKind::Str,
                // Trait ids are producer-scoped opaque tags, not a module
                // arena index; an emit-each producer uses one numbering.
                FatPtrKind::TraitObject { trait_id } => FatPtrKind::TraitObject {
                    trait_id: *trait_id,
                },
                // Id-less, exactly like `Str`: it carries no pointee `TyId`
                // (deliberately — the tail type is not what the kind is about),
                // so there is nothing for the arena remap to rewrite.
                FatPtrKind::ContainerLen => FatPtrKind::ContainerLen,
            }),
            Ty::Struct(id) => Ty::Struct(self.struct_id(ctx, *id)?),
            Ty::Array(elem, len) => Ty::Array(self.ty_id(ctx, *elem)?, *len),
            Ty::Tuple(elems) => Ty::Tuple(self.tys(ctx, elems)?),
            Ty::Enum(id) => Ty::Enum(self.enum_id(ctx, *id)?),
            Ty::Func(id) => Ty::Func(self.functy_id(ctx, *id)?),
            Ty::Ref(inner) => Ty::Ref(Box::new(self.ty(ctx, inner)?)),
            Ty::RefMut(inner) => Ty::RefMut(Box::new(self.ty(ctx, inner)?)),
            Ty::PtrConst(inner) => Ty::PtrConst(Box::new(self.ty(ctx, inner)?)),
            Ty::PtrMut(inner) => Ty::PtrMut(Box::new(self.ty(ctx, inner)?)),
            Ty::Rc(inner) => Ty::Rc(Box::new(self.ty(ctx, inner)?)),
            Ty::Set(elem, repr) => Ty::Set(self.ty_id(ctx, *elem)?, *repr),
            Ty::Sequence(elem) => Ty::Sequence(self.ty_id(ctx, *elem)?),
            Ty::Record(id) => Ty::Record(self.record_id(ctx, *id)?),
            Ty::Closure(id) => Ty::Closure(self.closure_id(ctx, *id)?),
            // Refinement types carry a base `TyId` plus a `PredId` into the
            // module's content-interned predicate table. Reject nested
            // refinements before remapping; both accepted ids are then
            // remapped by content (`intern_pred`/`intern_universe` dedupe on
            // merge).
            Ty::Refine(base, pred) => {
                let base_index = base.as_usize();
                let Some(base_ty) = ctx.source.types.get(base_index) else {
                    return Err(ctx.err(format!("ty.{base_index} is out of range")));
                };
                if matches!(base_ty, Ty::Refine(_, _)) {
                    return Err(ctx.err(format!(
                        "refinement base ty.{base_index} is itself a Refine"
                    )));
                }
                Ty::Refine(self.ty_id(ctx, *base)?, self.pred_id(ctx, *pred)?)
            }
        })
    }

    fn constant(&mut self, ctx: &mut ModuleCtx<'_>, value: &Constant) -> Result<Constant, String> {
        Ok(match value {
            Constant::Int(_)
            | Constant::U128(_)
            | Constant::Bytes { .. }
            | Constant::Float(_)
            | Constant::Bool(_)
            | Constant::PhantomData => value.clone(),
            // Symbol addresses resolve by NAME against the linked image, so
            // the payload passes through unchanged.
            Constant::SymbolAddr { .. } => value.clone(),
            Constant::Aggregate(items) => Constant::Aggregate(self.constants(ctx, items)?),
            Constant::Array(items) => Constant::Array(self.constants(ctx, items)?),
            Constant::Vector(items) => Constant::Vector(self.constants(ctx, items)?),
            Constant::Sequence(items) => Constant::Sequence(self.constants(ctx, items)?),
            Constant::Set(items) => Constant::Set(self.constants(ctx, items)?),
            Constant::Record(fields) => Constant::Record(
                fields
                    .iter()
                    .map(|(name, value)| Ok((name.clone(), self.constant(ctx, value)?)))
                    .collect::<Result<_, String>>()?,
            ),
            Constant::Closure { func, captures } => Constant::Closure {
                func: self.func_id(ctx, *func)?,
                captures: self.constants(ctx, captures)?,
            },
            Constant::FnDef(func) => Constant::FnDef(self.func_id(ctx, *func)?),
        })
    }

    fn constants(
        &mut self,
        ctx: &mut ModuleCtx<'_>,
        values: &[Constant],
    ) -> Result<Vec<Constant>, String> {
        values
            .iter()
            .map(|value| self.constant(ctx, value))
            .collect()
    }

    fn span(&self, ctx: &ModuleCtx<'_>, span: &SourceSpan) -> SourceSpan {
        SourceSpan {
            file: ctx
                .file_map
                .get(span.file as usize)
                .copied()
                .unwrap_or(span.file),
            line: span.line,
            col: span.col,
        }
    }

    /// Remap one instruction. Exhaustive on purpose: a future `Inst` variant
    /// that carries a cross-module id must fail compilation here, not silently
    /// pass stale ids through.
    fn inst(&mut self, ctx: &mut ModuleCtx<'_>, inst: &Inst) -> Result<Inst, String> {
        Ok(match inst {
            Inst::BinOp { op, ty, lhs, rhs } => Inst::BinOp {
                op: *op,
                ty: self.ty(ctx, ty)?,
                lhs: *lhs,
                rhs: *rhs,
            },
            Inst::UnOp { op, ty, operand } => Inst::UnOp {
                op: *op,
                ty: self.ty(ctx, ty)?,
                operand: *operand,
            },
            Inst::Overflow { op, ty, lhs, rhs } => Inst::Overflow {
                op: *op,
                ty: self.ty(ctx, ty)?,
                lhs: *lhs,
                rhs: *rhs,
            },
            Inst::ICmp { op, ty, lhs, rhs } => Inst::ICmp {
                op: *op,
                ty: self.ty(ctx, ty)?,
                lhs: *lhs,
                rhs: *rhs,
            },
            Inst::FCmp { op, ty, lhs, rhs } => Inst::FCmp {
                op: *op,
                ty: self.ty(ctx, ty)?,
                lhs: *lhs,
                rhs: *rhs,
            },
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => Inst::Cast {
                op: *op,
                src_ty: self.ty(ctx, src_ty)?,
                dst_ty: self.ty(ctx, dst_ty)?,
                operand: *operand,
            },
            Inst::Load {
                ty,
                ptr,
                volatile,
                align,
            } => Inst::Load {
                ty: self.ty(ctx, ty)?,
                ptr: *ptr,
                volatile: *volatile,
                align: *align,
            },
            Inst::Store {
                ty,
                ptr,
                value,
                volatile,
                align,
            } => Inst::Store {
                ty: self.ty(ctx, ty)?,
                ptr: *ptr,
                value: *value,
                volatile: *volatile,
                align: *align,
            },
            Inst::Alloca { ty, count, align } => Inst::Alloca {
                ty: self.ty(ctx, ty)?,
                count: *count,
                align: *align,
            },
            Inst::HeapAlloc {
                ty,
                count,
                align,
                origin,
            } => Inst::HeapAlloc {
                ty: self.ty(ctx, ty)?,
                count: *count,
                align: *align,
                origin: *origin,
            },
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                inbounds,
            } => Inst::GEP {
                pointee_ty: self.ty(ctx, pointee_ty)?,
                base: *base,
                indices: indices.clone(),
                inbounds: *inbounds,
            },
            Inst::PtrData { ptr_ty, ptr } => Inst::PtrData {
                ptr_ty: self.ty(ctx, ptr_ty)?,
                ptr: *ptr,
            },
            Inst::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ptr,
            } => Inst::PtrMetadata {
                ptr_ty: self.ty(ctx, ptr_ty)?,
                metadata_ty: self.ty(ctx, metadata_ty)?,
                ptr: *ptr,
            },
            Inst::PtrFromParts {
                ptr_ty,
                metadata_ty,
                data,
                metadata,
            } => Inst::PtrFromParts {
                ptr_ty: self.ty(ctx, ptr_ty)?,
                metadata_ty: self.ty(ctx, metadata_ty)?,
                data: *data,
                metadata: *metadata,
            },
            Inst::AtomicLoad { ty, ptr, ordering } => Inst::AtomicLoad {
                ty: self.ty(ctx, ty)?,
                ptr: *ptr,
                ordering: *ordering,
            },
            Inst::AtomicStore {
                ty,
                ptr,
                value,
                ordering,
            } => Inst::AtomicStore {
                ty: self.ty(ctx, ty)?,
                ptr: *ptr,
                value: *value,
                ordering: *ordering,
            },
            Inst::AtomicRMW {
                op,
                ty,
                ptr,
                value,
                ordering,
            } => Inst::AtomicRMW {
                op: *op,
                ty: self.ty(ctx, ty)?,
                ptr: *ptr,
                value: *value,
                ordering: *ordering,
            },
            Inst::CmpXchg {
                ty,
                ptr,
                expected,
                desired,
                success,
                failure,
            } => Inst::CmpXchg {
                ty: self.ty(ctx, ty)?,
                ptr: *ptr,
                expected: *expected,
                desired: *desired,
                success: *success,
                failure: *failure,
            },
            Inst::Fence { ordering } => Inst::Fence {
                ordering: *ordering,
            },
            Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Return { .. }
            | Inst::Assume { .. }
            | Inst::Assert { .. }
            | Inst::Unreachable
            | Inst::NullPtr
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::EndBorrow { .. }
            | Inst::Retain { .. }
            | Inst::Release { .. }
            | Inst::IsUnique { .. }
            | Inst::Dealloc { .. }
            | Inst::BindSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::CoroSuspend { .. }
            | Inst::Resume { .. }
            | Inst::LandingPad { .. } => inst.clone(),
            Inst::Switch {
                value,
                default,
                default_args,
                cases,
                exhaustive_enum_unreachable,
            } => Inst::Switch {
                value: *value,
                default: *default,
                default_args: default_args.clone(),
                cases: cases
                    .iter()
                    .map(|case| {
                        Ok(SwitchCase {
                            value: self.constant(ctx, &case.value)?,
                            target: case.target,
                            args: case.args.clone(),
                        })
                    })
                    .collect::<Result<_, String>>()?,
                exhaustive_enum_unreachable: *exhaustive_enum_unreachable,
            },
            Inst::Call { callee, args } => Inst::Call {
                callee: self.func_id(ctx, *callee)?,
                args: args.clone(),
            },
            Inst::CallIndirect {
                callee,
                sig,
                args,
                calling_conv,
            } => Inst::CallIndirect {
                callee: *callee,
                sig: self.functy_id(ctx, *sig)?,
                args: args.clone(),
                calling_conv: *calling_conv,
            },
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => Inst::ExtractField {
                ty: self.ty(ctx, ty)?,
                aggregate: *aggregate,
                field: *field,
            },
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => Inst::InsertField {
                ty: self.ty(ctx, ty)?,
                aggregate: *aggregate,
                field: *field,
                value: *value,
            },
            Inst::ExtractElement { ty, array, index } => Inst::ExtractElement {
                ty: self.ty(ctx, ty)?,
                array: *array,
                index: *index,
            },
            Inst::InsertElement {
                ty,
                array,
                index,
                value,
            } => Inst::InsertElement {
                ty: self.ty(ctx, ty)?,
                array: *array,
                index: *index,
                value: *value,
            },
            Inst::Const { ty, value } => Inst::Const {
                ty: self.ty(ctx, ty)?,
                value: self.constant(ctx, value)?,
            },
            Inst::GlobalAddr { global } => Inst::GlobalAddr {
                global: self.global_id(ctx, *global)?,
            },
            Inst::Undef { ty } => Inst::Undef {
                ty: self.ty(ctx, ty)?,
            },
            Inst::Copy { ty, operand } => Inst::Copy {
                ty: self.ty(ctx, ty)?,
                operand: *operand,
            },
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => Inst::Select {
                ty: self.ty(ctx, ty)?,
                cond: *cond,
                then_val: *then_val,
                else_val: *else_val,
            },
            Inst::SeqMapAddK { ty, seq, k } => Inst::SeqMapAddK {
                ty: self.ty(ctx, ty)?,
                seq: *seq,
                k: *k,
            },
            Inst::SeqMapNot { ty, seq } => Inst::SeqMapNot {
                ty: self.ty(ctx, ty)?,
                seq: *seq,
            },
            Inst::SeqMap { ty, seq, fwd } => Inst::SeqMap {
                ty: self.ty(ctx, ty)?,
                seq: *seq,
                fwd: self.func_id(ctx, *fwd)?,
            },
            Inst::OpenFrame { def } => Inst::OpenFrame {
                def: BindingFrameDef {
                    id: def.id,
                    name: def.name.clone(),
                    slots: def
                        .slots
                        .iter()
                        .map(|slot| {
                            Ok(BindingSlot {
                                name: slot.name.clone(),
                                ty: self.ty(ctx, &slot.ty)?,
                            })
                        })
                        .collect::<Result<_, String>>()?,
                },
            },
            Inst::LoadSlot { frame, slot, ty } => Inst::LoadSlot {
                frame: *frame,
                slot: *slot,
                ty: self.ty(ctx, ty)?,
            },
            Inst::Invoke {
                callee,
                args,
                normal_dest,
                normal_args,
                unwind_dest,
            } => Inst::Invoke {
                callee: self.func_id(ctx, *callee)?,
                args: args.clone(),
                normal_dest: *normal_dest,
                normal_args: normal_args.clone(),
                unwind_dest: *unwind_dest,
            },
            Inst::DialectOp(op) => {
                let mut remapped = op.as_ref().clone();
                remapped.result_tys = self.tys(ctx, &remapped.result_tys)?;
                Inst::DialectOp(Box::new(remapped))
            }
        })
    }

    fn node(&mut self, ctx: &mut ModuleCtx<'_>, node: &InstrNode) -> Result<InstrNode, String> {
        Ok(InstrNode {
            inst: self.inst(ctx, &node.inst)?,
            results: node.results.clone(),
            // Proof annotations are claim-style metadata with no execution
            // semantics; any `ProofRef` inside points at module obligations,
            // which the run image drops, so they are inert here.
            proofs: node.proofs.clone(),
            span: node.span.as_ref().map(|span| self.span(ctx, span)),
            proof_context: node.proof_context.clone(),
            // Function-local SSA/block ids are preserved by the linker. The
            // enclosing scope table is carried by `function()` below, so this
            // index remains meaningful in the linked image.
            scope: node.scope,
        })
    }

    fn function(
        &mut self,
        ctx: &mut ModuleCtx<'_>,
        func: &Function,
        merged_id: FuncId,
    ) -> Result<Function, String> {
        let mut remapped = Function::new(
            merged_id,
            func.name.clone(),
            self.functy_id(ctx, func.ty)?,
            func.entry,
        );
        remapped.calling_conv = func.calling_conv;
        remapped.linkage = func.linkage;
        remapped.proofs = func.proofs.clone();
        remapped.attrs = func.attrs.clone();
        remapped.summary = func.summary.clone();
        remapped.producer = func.producer.clone();
        // SSA ids remain function-local and unchanged, so names copy directly.
        remapped.value_names = func.value_names.clone();
        // Scope parents/indices are function-local too; only their source-file
        // indices cross a module boundary and need the same remap as node spans.
        remapped.scopes = func.scopes.as_ref().map(|scopes| {
            scopes
                .iter()
                .map(|scope| trust_ir::ScopeData {
                    parent: scope.parent,
                    span: scope.span.as_ref().map(|span| self.span(ctx, span)),
                })
                .collect()
        });
        for block in &func.blocks {
            let mut merged_block = Block::new(block.id);
            for (value, ty) in &block.params {
                merged_block.params.push((*value, self.ty(ctx, ty)?));
            }
            for node in &block.body {
                merged_block.body.push(self.node(ctx, node)?);
            }
            remapped.blocks.push(merged_block);
        }
        Ok(remapped)
    }

    /// Merge a remapped function into its slot: a definition beats a
    /// declaration, duplicate identical definitions are deduped, and
    /// conflicting definitions are an error.
    fn place_function(
        &mut self,
        ctx: &ModuleCtx<'_>,
        merged_id: FuncId,
        func: Function,
    ) -> Result<(), String> {
        // Resolve signature relationship before taking the slot borrow.
        let existing_ty = self.functions[merged_id.as_usize()]
            .as_ref()
            .map(|existing| existing.ty);
        let same_ty = existing_ty == Some(func.ty);
        // ABI-compatible but differently-spelled signatures arise when the
        // frontend coarsens a closure-env pointer to a 64-bit integer on one
        // side (a `dyn` vtable shim declares `call_once` as `(u64, u64)` while
        // its body is `(ptr, u64)` — same registers). Tolerate this ONLY
        // between a declaration and a definition; the definition's signature
        // wins. A call site that spells the args the declaration's way lives
        // in the shim, which is dead in a monomorphized program; were one
        // reachable, the interpreter's strict per-argument type check would
        // surface it honestly rather than silently mis-execute.
        let abi_compat = match existing_ty {
            Some(existing_ty) if !same_ty => self.abi_compatible_functy(existing_ty, func.ty),
            _ => false,
        };
        let slot = &mut self.functions[merged_id.as_usize()];
        match slot {
            None => *slot = Some(func),
            Some(existing) => {
                let existing_bodied = !existing.blocks.is_empty();
                let func_bodied = !func.blocks.is_empty();
                if !same_ty {
                    if abi_compat && !(existing_bodied && func_bodied) {
                        // Keep whichever side has a body (its signature is
                        // authoritative); a bodyless declaration only adds a
                        // name. If both are bodyless, keep the first.
                        if func_bodied && !existing_bodied {
                            *slot = Some(func);
                        }
                        return Ok(());
                    }
                    return Err(ctx.err(format!(
                        "signature mismatch for @{}: functy.{} vs functy.{}",
                        func.name,
                        existing.ty.index(),
                        func.ty.index()
                    )));
                }
                match (existing_bodied, func_bodied) {
                    // Definition replaces declaration.
                    (false, true) => *slot = Some(func),
                    // Declaration adds nothing to an existing entry.
                    (true, false) | (false, false) => {}
                    (true, true) => {
                        if *existing != func {
                            return Err(
                                ctx.err(format!("conflicting definitions of @{}", func.name))
                            );
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Two function signatures are ABI-compatible when they have the same
    /// param/return arity and every corresponding lane is either identical or
    /// a 64-bit machine word under a different spelling (`Ptr` / `U64` / `I64`
    /// / `Usize` / `Isize` all occupy one integer register on the pinned
    /// 64-bit target). This is exactly the pun a real backend erases. It is
    /// used only to let a bodyless declaration merge with a definition that
    /// spells a lane differently — the definition's signature wins.
    fn abi_compatible_functy(&self, a: FuncTyId, b: FuncTyId) -> bool {
        let (Some(a), Some(b)) = (
            self.merged.func_types.get(a.as_usize()),
            self.merged.func_types.get(b.as_usize()),
        ) else {
            return false;
        };
        a.is_vararg == b.is_vararg
            && a.params.len() == b.params.len()
            && a.returns.len() == b.returns.len()
            && a.params
                .iter()
                .zip(&b.params)
                .all(|(x, y)| abi_compatible_ty(x, y))
            && a.returns
                .iter()
                .zip(&b.returns)
                .all(|(x, y)| abi_compatible_ty(x, y))
    }
}

/// The 64-bit machine-word ABI class: a `Ptr` and a pointer-width integer
/// occupy the same integer register, so a producer may spell either.
fn is_word_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Ptr | Ty::U64 | Ty::I64 | Ty::Usize | Ty::Isize)
}

/// Whether two lane types are ABI-compatible: identical, or both 64-bit words.
fn abi_compatible_ty(a: &Ty, b: &Ty) -> bool {
    a == b || (is_word_ty(a) && is_word_ty(b))
}

/// Link the given `(label, module)` pairs into one executable image.
fn link_modules(modules: &[(String, Module)]) -> Result<Module, String> {
    let mut linker = Linker::new();

    // Phase A: assign merged FuncIds by function name, first-seen order.
    for (_, module) in modules {
        for func in &module.functions {
            if !linker.func_ids.contains_key(&func.name) {
                let id = FuncId::new(linker.functions.len() as u32);
                linker.func_ids.insert(func.name.clone(), id);
                linker.functions.push(None);
            }
        }
    }

    // Phase B: remap and merge every module.
    for (label, module) in modules {
        let func_map = module
            .functions
            .iter()
            .map(|func| linker.func_ids[&func.name])
            .collect();
        let mut ctx = ModuleCtx::new(label.clone(), module, func_map);

        match (&linker.merged.target_info, &module.target_info) {
            (None, Some(target)) => linker.merged.target_info = Some(target.clone()),
            (Some(existing), Some(target)) if existing != target => {
                return Err(ctx.err(format!(
                    "target mismatch: image is {existing:?}, module declares {target:?}"
                )));
            }
            _ => {}
        }
        ctx.file_map = module
            .files
            .iter()
            .map(|file| linker.merged.intern_file(file.clone()))
            .collect();

        // Predicates and universes are type semantics, not proof sidecars.
        // Remap every entry eagerly so even an unused dangling/cyclic table is
        // refused and the linked image preserves deterministic content IDs.
        for i in 0..module.universes.len() {
            linker.univ_id(&mut ctx, UnivId::new(i as u32))?;
        }
        for i in 0..module.predicates.len() {
            linker.pred_id(&mut ctx, PredId::new(i as u32))?;
        }

        // Eagerly remap globals so name-addressed consumers (SymbolAddr) see
        // every global even if no GlobalAddr references it.
        for i in 0..module.globals.len() {
            linker.global_id(&mut ctx, GlobalId::new(i as u32))?;
        }

        for (index, func) in module.functions.iter().enumerate() {
            let merged_id = ctx.func_map[index];
            let remapped = linker.function(&mut ctx, func, merged_id)?;
            linker.place_function(&ctx, merged_id, remapped)?;
        }
    }

    let mut functions = Vec::with_capacity(linker.functions.len());
    for slot in linker.functions {
        functions.push(slot.expect("phase A created a slot per named function"));
    }
    linker.merged.functions = functions;
    Ok(linker.merged)
}

// ---------------------------------------------------------------------------
// Bool-compare legalization
// ---------------------------------------------------------------------------

/// The format allows `ICmp` over `Bool` and `Ptr` operands (the
/// `trust-ir-build` validator whitelists both, and rustc's MIR `x == false` /
/// pointer comparisons lower to exactly that), but the reference
/// interpreter's integer comparator only accepts integer payloads — a known
/// interpreter-vs-validator gap. Rather than touching the interpreter, the
/// runner legalizes both shapes into forms it executes natively:
///
/// Bool compares become `Select` chains (bool order: `false < true`; the
/// signed forms treat `true` as the all-ones `-1`, so they are the unsigned
/// forms with the roles swapped):
///
///   eq  -> a ? b : !b        ne  -> a ? !b : b
///   ult -> a ? false : b     ule -> a ? b : true
///   ugt -> a ? !b : false    uge -> a ? true : !b
///   slt = ugt, sle = uge, sgt = ult, sge = ule
///
/// Ptr compares become `PtrToInt` on both operands followed by the same
/// compare over `u64` (the interpreter's deterministic allocation addresses
/// make this exact, including null).
///
/// Returns the number of rewritten compares.
fn legalize_icmp(module: &mut Module) -> u64 {
    let mut rewritten = 0;
    for func in &mut module.functions {
        // Fresh SSA ids start after every id the function defines.
        let mut next_value = 0u32;
        for block in &func.blocks {
            for (value, _) in &block.params {
                next_value = next_value.max(value.index() + 1);
            }
            for node in &block.body {
                for result in &node.results {
                    next_value = next_value.max(result.index() + 1);
                }
            }
        }
        let mut fresh = || {
            let value = ValueId::new(next_value);
            next_value += 1;
            value
        };
        for block in &mut func.blocks {
            let body = std::mem::take(&mut block.body);
            let mut new_body = Vec::with_capacity(body.len());
            for node in body {
                let Inst::ICmp {
                    op,
                    ref ty,
                    lhs,
                    rhs,
                } = node.inst
                else {
                    new_body.push(node);
                    continue;
                };
                if !matches!(ty, Ty::Bool | Ty::Ptr) {
                    new_body.push(node);
                    continue;
                }
                let is_ptr = *ty == Ty::Ptr;
                let [result] = node.results.as_slice() else {
                    new_body.push(node);
                    continue;
                };
                let result = *result;
                let span = node.span;
                let mut emit = |inst: Inst, result: ValueId| {
                    let mut aux = InstrNode::new(inst);
                    aux.results.push(result);
                    aux.span = span;
                    new_body.push(aux);
                };
                if is_ptr {
                    let lhs_addr = fresh();
                    emit(
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            src_ty: Ty::Ptr,
                            dst_ty: Ty::U64,
                            operand: lhs,
                        },
                        lhs_addr,
                    );
                    let rhs_addr = fresh();
                    emit(
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            src_ty: Ty::Ptr,
                            dst_ty: Ty::U64,
                            operand: rhs,
                        },
                        rhs_addr,
                    );
                    emit(
                        Inst::ICmp {
                            op,
                            ty: Ty::U64,
                            lhs: lhs_addr,
                            rhs: rhs_addr,
                        },
                        result,
                    );
                    rewritten += 1;
                    continue;
                }
                let k_false = fresh();
                emit(
                    Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(false),
                    },
                    k_false,
                );
                let k_true = fresh();
                emit(
                    Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(true),
                    },
                    k_true,
                );
                let not_rhs = fresh();
                emit(
                    Inst::Select {
                        ty: Ty::Bool,
                        cond: rhs,
                        then_val: k_false,
                        else_val: k_true,
                    },
                    not_rhs,
                );
                let (then_val, else_val) = match op {
                    ICmpOp::Eq => (rhs, not_rhs),
                    ICmpOp::Ne => (not_rhs, rhs),
                    ICmpOp::Ult | ICmpOp::Sgt => (k_false, rhs),
                    ICmpOp::Ule | ICmpOp::Sge => (rhs, k_true),
                    ICmpOp::Ugt | ICmpOp::Slt => (not_rhs, k_false),
                    ICmpOp::Uge | ICmpOp::Sle => (k_true, not_rhs),
                };
                emit(
                    Inst::Select {
                        ty: Ty::Bool,
                        cond: lhs,
                        then_val,
                        else_val,
                    },
                    result,
                );
                rewritten += 1;
            }
            block.body = new_body;
        }
    }
    rewritten
}

// ---------------------------------------------------------------------------
// SymbolAddr / vtable devirtualization glue
// ---------------------------------------------------------------------------

/// Make `Constant::SymbolAddr` images executable under the interpreter.
///
/// A trait-object vtable is a constant global whose function slots are
/// `SymbolAddr` link-time relocations, and a `dyn` call loads a `ptr` from the
/// vtable and `call_indirect`s through it. The interpreter has no relocation
/// or in-memory function-pointer story, so the runner lowers the whole
/// pattern at the IR level:
///
/// 1. every function whose address is taken gets a one-byte ANCHOR global
///    (`__fnaddr.<name>`) — its deterministic allocation address stands in
///    for the function's address;
/// 2. `SymbolAddr` slots inside global initializers are zeroed (the slot's
///    tuple field is retyped `ptr` -> `u64`, same 8-byte layout) and a
///    synthesized `@__trust_ir_run_init` — called first by the entry — stores
///    each anchor's real address into the slot at startup;
/// 3. `Const ptr SymbolAddr` instructions become `GlobalAddr` of the anchor
///    (or of the named data global);
/// 4. every `call_indirect` whose callee is a plain `ptr` becomes an
///    address-compare ladder over the anchored functions with the call's
///    exact signature: `ptrtoint` the callee, compare against each anchor's
///    address, and dispatch to the matching direct `Call`; a miss traps with
///    a named stub. Fn-typed (`FnDef`) indirect calls are left untouched.
///
/// Returns `true` if the image was changed.
fn devirtualize_symbol_addrs(
    module: &mut Module,
    entry: &str,
    traps: &mut Vec<String>,
) -> Result<bool, String> {
    let has_symbol_addr = module
        .globals
        .iter()
        .any(|global| {
            global
                .initializer
                .as_ref()
                .is_some_and(constant_mentions_symbol_addr)
        })
        || module.functions.iter().any(|func| {
            func.blocks.iter().any(|block| {
                block.body.iter().any(|node| {
                    matches!(&node.inst, Inst::Const { value, .. } if constant_mentions_symbol_addr(value))
                })
            })
        });
    if !has_symbol_addr {
        return Ok(false);
    }

    let func_by_name: HashMap<String, FuncId> = module
        .functions
        .iter()
        .map(|func| (func.name.clone(), func.id))
        .collect();
    let global_by_name: HashMap<String, GlobalId> = module
        .globals
        .iter()
        .enumerate()
        .map(|(index, global)| (global.name.clone(), GlobalId::new(index as u32)))
        .collect();

    // Function name -> (function, anchor global). Anchors are created on
    // demand and double as the address key for the dispatch ladders.
    let mut anchors: HashMap<String, (FuncId, GlobalId)> = HashMap::new();
    let mut anchor_for = |module: &mut Module, name: &str| -> Option<(FuncId, GlobalId)> {
        if let Some(entry) = anchors.get(name) {
            return Some(*entry);
        }
        let func = *func_by_name.get(name)?;
        let global = GlobalId::new(module.globals.len() as u32);
        module.globals.push(Global {
            name: format!("__fnaddr.{name}"),
            ty: Ty::U8,
            mutable: false,
            initializer: Some(Constant::Int(0)),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        anchors.insert(name.to_string(), (func, global));
        Some((func, global))
    };

    // -- 1+2: global initializers -------------------------------------------
    // `(global, byte offset, address-source global)` startup patches.
    let mut patches: Vec<(GlobalId, u64, GlobalId)> = Vec::new();
    for index in 0..module.globals.len() {
        let Some(init) = module.globals[index].initializer.clone() else {
            continue;
        };
        if !constant_mentions_symbol_addr(&init) {
            continue;
        }
        let ty = module.globals[index].ty.clone();
        let (Ty::Tuple(fields), Constant::Aggregate(values)) = (&ty, &init) else {
            eprintln!(
                "note: global @{} carries SymbolAddr in an unsupported shape; leaving as-is",
                module.globals[index].name
            );
            continue;
        };
        if fields.len() != values.len() {
            return Err(format!(
                "global @{}: tuple arity {} != initializer arity {}",
                module.globals[index].name,
                fields.len(),
                values.len()
            ));
        }
        // Any tuple of scalar/pointer fields is patchable: compute the real
        // C-style field byte offsets (matching the interpreter's tuple
        // layout) rather than assuming every field is 8 bytes. This covers
        // both the flat all-pointer vtable and a `&str`-shaped `(ptr, u8×8)`
        // (a data-pointer field followed by the length spread as bytes).
        let Some(offsets) = tuple_field_offsets(fields) else {
            eprintln!(
                "note: global @{} carries SymbolAddr in a non-scalar tuple; leaving as-is",
                module.globals[index].name
            );
            continue;
        };
        // Every SymbolAddr field must be pointer-sized (8 bytes) so the
        // ptr->u64 retype preserves layout; refuse otherwise.
        let ptr_sized = fields.iter().zip(values.iter()).all(|(field, value)| {
            !matches!(value, Constant::SymbolAddr { .. })
                || scalar_size_align(field).map(|(size, _)| size) == Some(8)
        });
        if !ptr_sized {
            eprintln!(
                "note: global @{} has a non-8-byte SymbolAddr field; leaving as-is",
                module.globals[index].name
            );
            continue;
        }
        let mut new_fields = fields.clone();
        let mut new_values = values.clone();
        for (slot, (field, value)) in new_fields.iter_mut().zip(new_values.iter_mut()).enumerate() {
            let Constant::SymbolAddr { symbol, addend } = value else {
                continue;
            };
            if *addend != 0 {
                return Err(format!(
                    "global @{}: SymbolAddr with nonzero addend {} is not supported",
                    module.globals[index].name, addend
                ));
            }
            let symbol = symbol.clone();
            let source = if let Some((_, anchor)) = anchor_for(module, &symbol) {
                anchor
            } else if let Some(target) = global_by_name.get(&symbol) {
                *target
            } else {
                return Err(format!(
                    "global @{}: SymbolAddr target {symbol} is not defined in the image",
                    module.globals[index].name
                ));
            };
            patches.push((GlobalId::new(index as u32), offsets[slot], source));
            *value = Constant::Int(0);
            *field = Ty::U64;
        }
        let global = &mut module.globals[index];
        global.ty = Ty::Tuple(new_fields);
        global.initializer = Some(Constant::Aggregate(new_values));
    }

    // -- 3: Const-instruction SymbolAddr ------------------------------------
    for func_index in 0..module.functions.len() {
        for block_index in 0..module.functions[func_index].blocks.len() {
            for node_index in 0..module.functions[func_index].blocks[block_index].body.len() {
                let inst = &module.functions[func_index].blocks[block_index].body[node_index].inst;
                let Inst::Const {
                    ty: Ty::Ptr,
                    value: Constant::SymbolAddr { symbol, addend },
                } = inst
                else {
                    continue;
                };
                if *addend != 0 {
                    return Err(format!(
                        "const SymbolAddr with nonzero addend {addend} is not supported"
                    ));
                }
                let symbol = symbol.clone();
                let source = if let Some((_, anchor)) = anchor_for(module, &symbol) {
                    anchor
                } else if let Some(target) = global_by_name.get(&symbol) {
                    *target
                } else {
                    return Err(format!(
                        "const SymbolAddr target {symbol} is not defined in the image"
                    ));
                };
                module.functions[func_index].blocks[block_index].body[node_index].inst =
                    Inst::GlobalAddr { global: source };
            }
        }
    }

    // -- 4: dispatch ladders for ptr-typed call_indirect ---------------------
    let anchored: Vec<(FuncId, GlobalId)> = anchors.values().copied().collect();
    if !anchored.is_empty() {
        for func_index in 0..module.functions.len() {
            devirtualize_calls_in_function(module, func_index, &anchored, traps);
        }
    }

    // -- 2b: the startup patcher, called first by the entry ------------------
    if !patches.is_empty() {
        let init_sig = intern_functy(
            module,
            FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
            },
        );
        let init_id = FuncId::new(module.functions.len() as u32);
        let mut init = Function::new(init_id, "__trust_ir_run_init", init_sig, BlockId::new(0));
        let mut bb = BodyBuilder::new();
        let block = bb.add_block();
        bb.switch_to(block);
        for (target, offset, source) in &patches {
            let base = bb.push(Inst::GlobalAddr { global: *target });
            let off = bb.const_int(Ty::I64, i128::from(*offset));
            let slot = bb.push(Inst::GEP {
                pointee_ty: Ty::U8,
                base,
                indices: vec![off],
                inbounds: false,
            });
            let addr = bb.push(Inst::GlobalAddr { global: *source });
            bb.push_void(Inst::Store {
                ty: Ty::Ptr,
                ptr: slot,
                value: addr,
                volatile: false,
                align: None,
            });
        }
        bb.ret(Vec::new());
        init.blocks = bb.blocks;
        module.functions.push(init);

        let Some(entry_func) = module
            .functions
            .iter_mut()
            .find(|func| func.name == entry && !func.blocks.is_empty())
        else {
            return Err(format!(
                "SymbolAddr patching requires entry @{entry}, which has no body"
            ));
        };
        let entry_block = entry_func.entry;
        let Some(first) = entry_func.block_mut(entry_block) else {
            return Err(format!("entry @{entry} is missing its entry block"));
        };
        first.body.insert(
            0,
            InstrNode::new(Inst::Call {
                callee: init_id,
                args: Vec::new(),
            }),
        );
        eprintln!(
            "devirtualized {} SymbolAddr slot(s) across {} anchored function(s)",
            patches.len(),
            anchors.len()
        );
    }
    Ok(true)
}

/// Does this constant (recursively) contain a `SymbolAddr`?
fn constant_mentions_symbol_addr(constant: &Constant) -> bool {
    match constant {
        Constant::SymbolAddr { .. } => true,
        Constant::Aggregate(items)
        | Constant::Array(items)
        | Constant::Vector(items)
        | Constant::Sequence(items)
        | Constant::Set(items) => items.iter().any(constant_mentions_symbol_addr),
        Constant::Record(fields) => fields
            .iter()
            .any(|(_, value)| constant_mentions_symbol_addr(value)),
        Constant::Closure { captures, .. } => captures.iter().any(constant_mentions_symbol_addr),
        _ => false,
    }
}

/// Intern (or append) a function type in the module's arena.
fn intern_functy(module: &mut Module, functy: FuncTy) -> FuncTyId {
    for (index, existing) in module.func_types.iter().enumerate() {
        if *existing == functy {
            return FuncTyId::new(index as u32);
        }
    }
    let id = FuncTyId::new(module.func_types.len() as u32);
    module.func_types.push(functy);
    id
}

/// Rewrite every `CallIndirect` in `module.functions[func_index]` whose
/// callee is a plain `Ty::Ptr` value into an anchor-address dispatch ladder
/// over the anchored functions with the call's signature.
fn devirtualize_calls_in_function(
    module: &mut Module,
    func_index: usize,
    anchored: &[(FuncId, GlobalId)],
    traps: &mut Vec<String>,
) {
    // Value types are computed once up front: rewrites never introduce new
    // ptr-typed callees, and split-off continuations keep the original result
    // ids (as block params), so the map stays valid across rewrites.
    let value_tys: HashMap<ValueId, Ty> = {
        let func = &module.functions[func_index];
        func.typed_values(module)
            .into_iter()
            .map(|metadata| (metadata.value, metadata.ty))
            .collect()
    };

    let mut next_block = module.functions[func_index]
        .blocks
        .iter()
        .map(|block| block.id.index().saturating_add(1))
        .max()
        .unwrap_or(0);
    let mut next_value = {
        let func = &module.functions[func_index];
        let mut max = 0u32;
        for block in &func.blocks {
            for (value, _) in &block.params {
                max = max.max(value.index() + 1);
            }
            for node in &block.body {
                for result in &node.results {
                    max = max.max(result.index() + 1);
                }
            }
        }
        max
    };

    let mut block_index = 0;
    while block_index < module.functions[func_index].blocks.len() {
        // Find the first ptr-callee indirect call in this block, if any.
        let found = {
            let block = &module.functions[func_index].blocks[block_index];
            block.body.iter().position(|node| {
                matches!(
                    &node.inst,
                    Inst::CallIndirect { callee, .. }
                        if value_tys.get(callee) == Some(&Ty::Ptr)
                )
            })
        };
        let Some(node_index) = found else {
            block_index += 1;
            continue;
        };
        let (callee, sig, args, results) = {
            let node = &module.functions[func_index].blocks[block_index].body[node_index];
            let Inst::CallIndirect {
                callee, sig, args, ..
            } = &node.inst
            else {
                unreachable!("position() matched a CallIndirect");
            };
            (*callee, *sig, args.clone(), node.results.clone())
        };
        let Some(ret_tys) = module.func_type(sig).map(|ft| ft.returns.clone()) else {
            block_index += 1;
            continue;
        };
        if ret_tys.len() != results.len() {
            block_index += 1;
            continue;
        }
        let candidates: Vec<(FuncId, GlobalId)> = anchored
            .iter()
            .copied()
            .filter(|(func, _)| {
                module
                    .function_by_id(*func)
                    .is_some_and(|candidate| candidate.ty == sig)
            })
            .collect();
        if candidates.is_empty() {
            // No anchored target can inhabit this signature; leave the call
            // alone (the interpreter reports it honestly if reached).
            block_index += 1;
            continue;
        }

        fn take_value(counter: &mut u32) -> ValueId {
            let value = ValueId::new(*counter);
            *counter += 1;
            value
        }
        fn take_block(counter: &mut u32) -> BlockId {
            let id = BlockId::new(*counter);
            *counter += 1;
            id
        }

        // Split: `post` moves into the continuation block, whose params are
        // the original call results.
        let post: Vec<InstrNode> = {
            let block = &mut module.functions[func_index].blocks[block_index];
            let post = block.body.split_off(node_index + 1);
            block.body.pop();
            post
        };
        let cont_id = take_block(&mut next_block);
        let mut cont = Block::new(cont_id);
        cont.params = results
            .iter()
            .copied()
            .zip(ret_tys.iter().cloned())
            .collect();
        cont.body = post;

        let miss_id = BlockId::new(TRAP_BLOCK_BASE + traps.len() as u32);
        traps.push(format!(
            "<indirect-call dispatch miss in @{} (functy.{})>",
            module.functions[func_index].name,
            sig.index()
        ));
        let mut miss = Block::new(miss_id);
        miss.body.push(InstrNode::new(Inst::Unreachable));

        // Emit the compare ladder. The first test lives in the split block;
        // later tests get their own chain blocks.
        let mut new_blocks: Vec<Block> = Vec::new();
        let addr = take_value(&mut next_value);
        {
            let mut node = InstrNode::new(Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::U64,
                operand: callee,
            });
            node.results.push(addr);
            module.functions[func_index].blocks[block_index]
                .body
                .push(node);
        }
        let mut chain: Option<Block> = None;
        for (position, (target, anchor)) in candidates.iter().enumerate() {
            let is_last = position + 1 == candidates.len();

            // The direct-call block for this candidate.
            let call_id = take_block(&mut next_block);
            let mut call_block = Block::new(call_id);
            let mut call_results = Vec::with_capacity(results.len());
            let mut call_node = InstrNode::new(Inst::Call {
                callee: *target,
                args: args.clone(),
            });
            for _ in &results {
                let value = take_value(&mut next_value);
                call_node.results.push(value);
                call_results.push(value);
            }
            call_block.body.push(call_node);
            call_block.body.push(InstrNode::new(Inst::Br {
                target: cont_id,
                args: call_results,
            }));

            let else_target = if is_last {
                miss_id
            } else {
                let id = take_block(&mut next_block);
                new_blocks.push(Block::new(id));
                id
            };

            // The compare itself, in the current chain position.
            let emit_into = |body: &mut Vec<InstrNode>, next_value: &mut u32| {
                let mut fresh = || {
                    let value = ValueId::new(*next_value);
                    *next_value += 1;
                    value
                };
                let anchor_ptr = fresh();
                let mut node = InstrNode::new(Inst::GlobalAddr { global: *anchor });
                node.results.push(anchor_ptr);
                body.push(node);
                let anchor_addr = fresh();
                let mut node = InstrNode::new(Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::U64,
                    operand: anchor_ptr,
                });
                node.results.push(anchor_addr);
                body.push(node);
                let matches_target = fresh();
                let mut node = InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::U64,
                    lhs: addr,
                    rhs: anchor_addr,
                });
                node.results.push(matches_target);
                body.push(node);
                body.push(InstrNode::new(Inst::CondBr {
                    cond: matches_target,
                    then_target: call_id,
                    then_args: Vec::new(),
                    else_target,
                    else_args: Vec::new(),
                }));
            };
            match chain.take() {
                None => emit_into(
                    &mut module.functions[func_index].blocks[block_index].body,
                    &mut next_value,
                ),
                Some(mut block) => {
                    emit_into(&mut block.body, &mut next_value);
                    new_blocks.push(block);
                }
            }
            if !is_last {
                // The freshly created else block becomes the next chain link.
                let pending = new_blocks
                    .iter()
                    .position(|block| block.id == else_target)
                    .expect("chain block was just pushed");
                chain = Some(new_blocks.remove(pending));
            }
            new_blocks.push(call_block);
        }

        let func = &mut module.functions[func_index];
        func.blocks.push(cont);
        func.blocks.push(miss);
        func.blocks.extend(new_blocks);
        block_index += 1;
    }
}

// ---------------------------------------------------------------------------
// Builtin synthesis for bodyless externs
// ---------------------------------------------------------------------------

/// What a bodyless extern is synthesized as.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BuiltinKind {
    /// `__rust_alloc(size, align) -> ptr`
    Alloc,
    /// `__rust_alloc_zeroed(size, align) -> ptr`
    AllocZeroed,
    /// `__rust_dealloc(ptr, size, align)`
    Dealloc,
    /// `__rust_realloc(ptr, old_size, align, new_size) -> ptr`
    Realloc,
    /// Unit-returning no-ops: the `__rust_no_alloc_shim_is_unstable_v2` probe
    /// and the check/hint intrinsic family (`assert_inhabited`,
    /// `assert_zero_valid`, `assert_mem_uninitialized_valid`, `assume`,
    /// `cold_path`) — compile-time checks and optimizer hints with no runtime
    /// effect.
    NoOp,
    /// `core::intrinsics::is_val_statically_known<T>(x) -> bool`: always
    /// `false` at runtime (the same answer the native harness shims).
    ConstFalse,
    Memcpy,
    Memmove,
    Memset,
    Memcmp,
    /// `core::intrinsics::ctpop<uN>(x) -> u32`
    Ctpop,
    /// `core::intrinsics::ctlz{,_nonzero}<uN>(x) -> u32`
    Ctlz,
    /// `core::intrinsics::cttz{,_nonzero}<uN>(x) -> u32`
    Cttz,
    /// `core::intrinsics::unchecked_funnel_shl<uN>(a, b, shift: u32) -> uN`
    FunnelShl,
    /// `core::intrinsics::exact_div<T>(a, b) -> a / b` for a signed or
    /// unsigned integer `T`. UB if `b == 0` or the division is inexact; the
    /// synthesized body just emits the (signed or unsigned) `BinOp` division,
    /// matching the native harness's `a/b` shim.
    ExactDiv,
    /// `CCRandomGenerateBytes(bytes: ptr, count: u64) -> i32`: the macOS
    /// libSystem RNG seed source (`RandomState` entropy). Fills the output
    /// buffer with DETERMINISTIC bytes (zeros) and returns `kCCSuccess` (0).
    /// The battery programs that reach it are provably seed-independent
    /// (commutative value sums, key-based gets over pre-sorted probes), so a
    /// constant fill yields the native value.
    RandomBytes,
    /// Anything else: a stub that traps with the extern's name.
    Trap,
}

impl BuiltinKind {
    fn classify(name: &str) -> BuiltinKind {
        // Exact C symbol names.
        match name {
            "memcpy" => return BuiltinKind::Memcpy,
            "memmove" => return BuiltinKind::Memmove,
            "memset" => return BuiltinKind::Memset,
            "memcmp" => return BuiltinKind::Memcmp,
            _ => {}
        }
        // macOS libSystem RNG seed source (may carry a leading underscore in
        // the object symbol). Deterministic fill; see `BuiltinKind::RandomBytes`.
        if name.contains("CCRandomGenerateBytes") {
            return BuiltinKind::RandomBytes;
        }
        // Rust allocator shims (mangled `_RNv..___rustc..___rust_alloc` etc.).
        // The error handler must be checked before the `___rust_alloc` prefix.
        if name.contains("___rust_alloc_error_handler") {
            return BuiltinKind::Trap;
        }
        if name.contains("___rust_alloc_zeroed") {
            return BuiltinKind::AllocZeroed;
        }
        if name.contains("___rust_realloc") {
            return BuiltinKind::Realloc;
        }
        if name.contains("___rust_alloc") {
            return BuiltinKind::Alloc;
        }
        if name.contains("___rust_dealloc") {
            return BuiltinKind::Dealloc;
        }
        if name.contains("___rust_no_alloc_shim_is_unstable") {
            return BuiltinKind::NoOp;
        }
        match v0_intrinsic_name(name).as_deref() {
            Some("ctpop") => BuiltinKind::Ctpop,
            Some("ctlz") | Some("ctlz_nonzero") => BuiltinKind::Ctlz,
            Some("cttz") | Some("cttz_nonzero") => BuiltinKind::Cttz,
            Some("unchecked_funnel_shl") => BuiltinKind::FunnelShl,
            Some("exact_div") => BuiltinKind::ExactDiv,
            // `compare_bytes(a, b, n) -> i32` has memcmp semantics exactly.
            Some("compare_bytes") => BuiltinKind::Memcmp,
            // Check/hint intrinsics: compile-time assertions (the frontend
            // already discharged them) and optimizer hints — runtime no-ops.
            Some("assert_inhabited")
            | Some("assert_zero_valid")
            | Some("assert_mem_uninitialized_valid")
            | Some("assume")
            | Some("cold_path") => BuiltinKind::NoOp,
            Some("is_val_statically_known") => BuiltinKind::ConstFalse,
            _ => BuiltinKind::Trap,
        }
    }
}

/// Extract the length-prefixed identifier following `10intrinsics` in a Rust
/// v0-mangled `core::intrinsics::<name>` symbol, e.g.
/// `_RINvNtC..4core10intrinsics5ctpopyE..` -> `Some("ctpop")`.
fn v0_intrinsic_name(name: &str) -> Option<String> {
    let start = name.find("10intrinsics")? + "10intrinsics".len();
    let rest = name.get(start..)?;
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    let len: usize = digits.parse().ok()?;
    rest.get(digits.len()..digits.len() + len)
        .map(str::to_string)
}

/// Report of what synthesis attached to the linked image.
struct SynthesisReport {
    /// Trap names; index `k` owns block id `TRAP_BLOCK_BASE + k`. Holds both
    /// extern stub names and `<indirect-call dispatch miss …>` entries.
    traps: Vec<String>,
    /// (name, builtin) pairs for the executable builtins.
    builtins: Vec<(String, &'static str)>,
    /// How many bodyless externs became trap STUB functions (a subset of
    /// `traps`, which also carries dispatch-miss blocks).
    stub_count: usize,
}

impl SynthesisReport {
    /// Resolve an interpreter error block id back to a trap-stub name.
    fn trap_name(&self, block: BlockId) -> Option<&str> {
        let index = block.index().checked_sub(TRAP_BLOCK_BASE)? as usize;
        self.traps.get(index).map(String::as_str)
    }
}

/// Small function-body assembler for synthesized builtins.
struct BodyBuilder {
    blocks: Vec<Block>,
    cur: usize,
    next_value: u32,
}

impl BodyBuilder {
    fn new() -> Self {
        Self {
            blocks: Vec::new(),
            cur: 0,
            next_value: 0,
        }
    }

    fn add_block(&mut self) -> BlockId {
        let id = BlockId::new(self.blocks.len() as u32);
        self.blocks.push(Block::new(id));
        id
    }

    fn switch_to(&mut self, block: BlockId) {
        self.cur = block.as_usize();
    }

    fn fresh(&mut self) -> ValueId {
        let value = ValueId::new(self.next_value);
        self.next_value += 1;
        value
    }

    fn param(&mut self, block: BlockId, ty: Ty) -> ValueId {
        let value = self.fresh();
        self.blocks[block.as_usize()].params.push((value, ty));
        value
    }

    fn push_void(&mut self, inst: Inst) {
        self.blocks[self.cur].body.push(InstrNode::new(inst));
    }

    fn push(&mut self, inst: Inst) -> ValueId {
        let value = self.fresh();
        let mut node = InstrNode::new(inst);
        node.results.push(value);
        self.blocks[self.cur].body.push(node);
        value
    }

    fn const_int(&mut self, ty: Ty, value: i128) -> ValueId {
        self.push(Inst::Const {
            ty,
            value: Constant::Int(value),
        })
    }

    fn binop(&mut self, op: BinOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.push(Inst::BinOp { op, ty, lhs, rhs })
    }

    fn icmp(&mut self, op: ICmpOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.push(Inst::ICmp { op, ty, lhs, rhs })
    }

    fn br(&mut self, target: BlockId, args: Vec<ValueId>) {
        self.push_void(Inst::Br { target, args });
    }

    fn cond_br(&mut self, cond: ValueId, then_target: BlockId, else_target: BlockId) {
        self.push_void(Inst::CondBr {
            cond,
            then_target,
            then_args: Vec::new(),
            else_target,
            else_args: Vec::new(),
        });
    }

    fn ret(&mut self, values: Vec<ValueId>) {
        self.push_void(Inst::Return { values });
    }

    /// Byte-granular heap allocation of `count` bytes, 16-aligned. The static
    /// 16-byte alignment stands in for the runtime `align` argument of the
    /// Rust allocator ABI; it covers every scalar the interpreter can store.
    fn heap_alloc_bytes(&mut self, count: ValueId) -> ValueId {
        self.push(Inst::HeapAlloc {
            ty: Ty::U8,
            count: Some(count),
            align: Some(16),
            origin: AllocOrigin::RustHeap,
        })
    }

    fn gep_u8(&mut self, base: ValueId, index: ValueId) -> ValueId {
        self.push(Inst::GEP {
            pointee_ty: Ty::U8,
            base,
            indices: vec![index],
            inbounds: false,
        })
    }

    fn load_u8(&mut self, ptr: ValueId) -> ValueId {
        self.push(Inst::Load {
            ty: Ty::U8,
            ptr,
            volatile: false,
            align: None,
        })
    }

    fn store_u8(&mut self, ptr: ValueId, value: ValueId) {
        self.push_void(Inst::Store {
            ty: Ty::U8,
            ptr,
            value,
            volatile: false,
            align: None,
        });
    }

    /// Width-adjust an integer value between integer types (bit-level:
    /// `Trunc` down, `ZExt` up, pass-through when equal).
    fn adjust_int(&mut self, value: ValueId, from: &Ty, to: &Ty) -> Option<ValueId> {
        if from == to {
            return Some(value);
        }
        let from_bits = int_bits(from)?;
        let to_bits = int_bits(to)?;
        let op = match to_bits.cmp(&from_bits) {
            std::cmp::Ordering::Less => CastOp::Trunc,
            std::cmp::Ordering::Greater => CastOp::ZExt,
            std::cmp::Ordering::Equal => CastOp::Bitcast,
        };
        Some(self.push(Inst::Cast {
            op,
            src_ty: from.clone(),
            dst_ty: to.clone(),
            operand: value,
        }))
    }
}

/// Bit width of an integer type under the 64-bit target this runner pins.
fn int_bits(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::I8 | Ty::U8 => Some(8),
        Ty::I16 | Ty::U16 => Some(16),
        Ty::I32 | Ty::U32 => Some(32),
        Ty::I64 | Ty::U64 | Ty::Isize | Ty::Usize => Some(64),
        Ty::I128 | Ty::U128 => Some(128),
        _ => None,
    }
}

/// Whether an integer type is signed under the 64-bit target this runner pins.
fn int_is_signed(ty: &Ty) -> Option<bool> {
    match ty {
        Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128 | Ty::Isize => Some(true),
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 | Ty::Usize => Some(false),
        _ => None,
    }
}

/// `(byte size, byte alignment)` of a scalar/pointer type under the 64-bit
/// little-endian target this runner pins — matching the interpreter's own
/// `byte_size`/`byte_align`. `None` for a non-scalar (which the tuple
/// field-offset computation refuses rather than guessing a layout).
fn scalar_size_align(ty: &Ty) -> Option<(u64, u64)> {
    match ty {
        Ty::Bool | Ty::I8 | Ty::U8 => Some((1, 1)),
        Ty::I16 | Ty::U16 | Ty::F16 => Some((2, 2)),
        Ty::I32 | Ty::U32 | Ty::F32 | Ty::Char => Some((4, 4)),
        Ty::I64 | Ty::U64 | Ty::F64 | Ty::Isize | Ty::Usize | Ty::Ptr => Some((8, 8)),
        Ty::I128 | Ty::U128 => Some((16, 16)),
        _ => None,
    }
}

/// C-style byte offsets of each field of a scalar/pointer tuple, matching the
/// interpreter's `aggregate_layout` (each field aligned up to its natural
/// alignment; no reordering). `None` if any field is not a scalar/pointer, so
/// the caller falls back to leaving the initializer as-is.
fn tuple_field_offsets(fields: &[Ty]) -> Option<Vec<u64>> {
    let mut offset: u64 = 0;
    let mut offsets = Vec::with_capacity(fields.len());
    for field in fields {
        let (size, align) = scalar_size_align(field)?;
        offset = offset.div_ceil(align) * align;
        offsets.push(offset);
        offset = offset.checked_add(size)?;
    }
    Some(offsets)
}

/// Synthesize bodies for every function that is still bodyless after linking.
/// Returns the trap table (continuing `trap_names` from earlier passes) and
/// the builtin census. Never fails: an extern whose signature does not fit
/// its classified builtin falls back to a trap stub (with a note on stderr).
fn synthesize_builtins(module: &mut Module, trap_names: Vec<String>) -> SynthesisReport {
    let mut report = SynthesisReport {
        traps: trap_names,
        builtins: Vec::new(),
        stub_count: 0,
    };
    for index in 0..module.functions.len() {
        if !module.functions[index].blocks.is_empty() {
            continue;
        }
        let name = module.functions[index].name.clone();
        let Some(sig) = module.func_type(module.functions[index].ty).cloned() else {
            // Dangling signature: leave bodyless; the interpreter reports it
            // if the function is ever called.
            continue;
        };
        let kind = BuiltinKind::classify(&name);
        let body = match kind {
            BuiltinKind::Trap => None,
            _ => build_builtin_body(kind, &sig),
        };
        match body {
            Some((entry, blocks)) => {
                let label = builtin_label(kind);
                report.builtins.push((name, label));
                let func = &mut module.functions[index];
                func.entry = entry;
                func.blocks = blocks;
            }
            None => {
                if kind != BuiltinKind::Trap {
                    eprintln!(
                        "note: extern @{name} matched builtin {:?} but its signature {} does \
                         not fit; using a trap stub",
                        kind,
                        render_sig(&sig)
                    );
                }
                let trap_index = report.traps.len() as u32;
                let block_id = BlockId::new(TRAP_BLOCK_BASE + trap_index);
                let mut block = Block::new(block_id);
                for (next_value, ty) in (0u32..).zip(&sig.params) {
                    block.params.push((ValueId::new(next_value), ty.clone()));
                }
                block.body.push(InstrNode::new(Inst::Unreachable));
                let func = &mut module.functions[index];
                func.entry = block_id;
                func.blocks = vec![block];
                report.traps.push(func.name.clone());
                report.stub_count += 1;
            }
        }
    }
    report
}

fn builtin_label(kind: BuiltinKind) -> &'static str {
    match kind {
        BuiltinKind::Alloc => "__rust_alloc",
        BuiltinKind::AllocZeroed => "__rust_alloc_zeroed",
        BuiltinKind::Dealloc => "__rust_dealloc",
        BuiltinKind::Realloc => "__rust_realloc",
        BuiltinKind::NoOp => "no-op",
        BuiltinKind::ConstFalse => "const-false",
        BuiltinKind::Memcpy => "memcpy",
        BuiltinKind::Memmove => "memmove",
        BuiltinKind::Memset => "memset",
        BuiltinKind::Memcmp => "memcmp",
        BuiltinKind::Ctpop => "ctpop",
        BuiltinKind::Ctlz => "ctlz",
        BuiltinKind::Cttz => "cttz",
        BuiltinKind::FunnelShl => "funnel_shl",
        BuiltinKind::ExactDiv => "exact_div",
        BuiltinKind::RandomBytes => "CCRandomGenerateBytes",
        BuiltinKind::Trap => "trap",
    }
}

fn render_sig(sig: &FuncTy) -> String {
    let params: Vec<String> = sig.params.iter().map(|ty| ty.to_string()).collect();
    let returns: Vec<String> = sig.returns.iter().map(|ty| ty.to_string()).collect();
    format!("({}) -> ({})", params.join(", "), returns.join(", "))
}

/// Build the block list for one builtin against its declared signature.
/// Returns `None` when the signature does not fit the builtin's shape.
fn build_builtin_body(kind: BuiltinKind, sig: &FuncTy) -> Option<(BlockId, Vec<Block>)> {
    let mut bb = BodyBuilder::new();
    match kind {
        BuiltinKind::Trap => None,
        BuiltinKind::NoOp => {
            if !sig.returns.is_empty() {
                return None;
            }
            let entry = bb.add_block();
            for ty in &sig.params {
                bb.param(entry, ty.clone());
            }
            bb.switch_to(entry);
            bb.ret(Vec::new());
            Some((entry, bb.blocks))
        }
        BuiltinKind::ConstFalse => {
            if sig.returns.as_slice() != [Ty::Bool] {
                return None;
            }
            let entry = bb.add_block();
            for ty in &sig.params {
                bb.param(entry, ty.clone());
            }
            bb.switch_to(entry);
            let result = bb.push(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(false),
            });
            bb.ret(vec![result]);
            Some((entry, bb.blocks))
        }
        BuiltinKind::Ctpop | BuiltinKind::Ctlz | BuiltinKind::Cttz => {
            let [param_ty] = sig.params.as_slice() else {
                return None;
            };
            let [ret_ty] = sig.returns.as_slice() else {
                return None;
            };
            let bits = int_bits(param_ty)?;
            int_bits(ret_ty)?;
            let param_ty = param_ty.clone();
            let ret_ty = ret_ty.clone();
            let entry = bb.add_block();
            let x = bb.param(entry, param_ty.clone());
            bb.switch_to(entry);
            let counted = match kind {
                BuiltinKind::Ctpop => bb.push(Inst::UnOp {
                    op: UnOp::CtPop,
                    ty: param_ty.clone(),
                    operand: x,
                }),
                BuiltinKind::Ctlz => {
                    // Smear the leading one downward, then count the ones:
                    // ctlz(x) = bits - ctpop(smear(x)); handles x == 0.
                    let mut smeared = x;
                    let mut shift = 1u32;
                    while shift < bits {
                        let amount = bb.const_int(param_ty.clone(), i128::from(shift));
                        let shifted = bb.binop(BinOp::LShr, param_ty.clone(), smeared, amount);
                        smeared = bb.binop(BinOp::Or, param_ty.clone(), smeared, shifted);
                        shift *= 2;
                    }
                    let pop = bb.push(Inst::UnOp {
                        op: UnOp::CtPop,
                        ty: param_ty.clone(),
                        operand: smeared,
                    });
                    let width = bb.const_int(param_ty.clone(), i128::from(bits));
                    bb.binop(BinOp::Sub, param_ty.clone(), width, pop)
                }
                BuiltinKind::Cttz => {
                    // cttz(x) = ctpop((x - 1) & !x); handles x == 0 (wraps to
                    // all-ones & all-ones = all-ones, ctpop = bits).
                    let one = bb.const_int(param_ty.clone(), 1);
                    let minus_one = bb.binop(BinOp::Sub, param_ty.clone(), x, one);
                    let inverted = bb.push(Inst::UnOp {
                        op: UnOp::Not,
                        ty: param_ty.clone(),
                        operand: x,
                    });
                    let mask = bb.binop(BinOp::And, param_ty.clone(), minus_one, inverted);
                    bb.push(Inst::UnOp {
                        op: UnOp::CtPop,
                        ty: param_ty.clone(),
                        operand: mask,
                    })
                }
                _ => unreachable!(),
            };
            let result = bb.adjust_int(counted, &param_ty, &ret_ty)?;
            bb.ret(vec![result]);
            Some((entry, bb.blocks))
        }
        BuiltinKind::FunnelShl => {
            let [a_ty, b_ty, c_ty] = sig.params.as_slice() else {
                return None;
            };
            let [ret_ty] = sig.returns.as_slice() else {
                return None;
            };
            if a_ty != b_ty {
                return None;
            }
            let bits = int_bits(a_ty)?;
            int_bits(c_ty)?;
            int_bits(ret_ty)?;
            let word = a_ty.clone();
            let entry = bb.add_block();
            let a = bb.param(entry, word.clone());
            let b = bb.param(entry, word.clone());
            let c = bb.param(entry, c_ty.clone());
            bb.switch_to(entry);
            // fshl(a, b, c): sh = c & (bits-1);
            // result = (a << sh) | ((b >> 1) >> ((bits-1) - sh)).
            // Branch-free and shift-in-range for every c (sh == 0 included).
            let c_word = bb.adjust_int(c, c_ty, &word)?;
            let mask = bb.const_int(word.clone(), i128::from(bits - 1));
            let sh = bb.binop(BinOp::And, word.clone(), c_word, mask);
            let hi = bb.binop(BinOp::Shl, word.clone(), a, sh);
            let one = bb.const_int(word.clone(), 1);
            let b_half = bb.binop(BinOp::LShr, word.clone(), b, one);
            let inv = bb.binop(BinOp::Sub, word.clone(), mask, sh);
            let lo = bb.binop(BinOp::LShr, word.clone(), b_half, inv);
            let combined = bb.binop(BinOp::Or, word.clone(), hi, lo);
            let result = bb.adjust_int(combined, &word, ret_ty)?;
            bb.ret(vec![result]);
            Some((entry, bb.blocks))
        }
        BuiltinKind::ExactDiv => {
            let [a_ty, b_ty] = sig.params.as_slice() else {
                return None;
            };
            let [ret_ty] = sig.returns.as_slice() else {
                return None;
            };
            if a_ty != b_ty || a_ty != ret_ty {
                return None;
            }
            let signed = int_is_signed(a_ty)?;
            let word = a_ty.clone();
            let entry = bb.add_block();
            let a = bb.param(entry, word.clone());
            let b = bb.param(entry, word.clone());
            bb.switch_to(entry);
            // exact_div is precondition-guarded (b != 0, a % b == 0) at the
            // Rust level; the runtime value is just the quotient.
            let op = if signed { BinOp::SDiv } else { BinOp::UDiv };
            let quotient = bb.binop(op, word.clone(), a, b);
            bb.ret(vec![quotient]);
            Some((entry, bb.blocks))
        }
        BuiltinKind::Alloc => {
            let [size_ty, _align_ty] = sig.params.as_slice() else {
                return None;
            };
            if sig.returns.as_slice() != [Ty::Ptr] {
                return None;
            }
            int_bits(size_ty)?;
            let entry = bb.add_block();
            let size = bb.param(entry, size_ty.clone());
            bb.param(entry, sig.params[1].clone());
            bb.switch_to(entry);
            let ptr = bb.heap_alloc_bytes(size);
            bb.ret(vec![ptr]);
            Some((entry, bb.blocks))
        }
        BuiltinKind::AllocZeroed => {
            let [size_ty, _align_ty] = sig.params.as_slice() else {
                return None;
            };
            if sig.returns.as_slice() != [Ty::Ptr] {
                return None;
            }
            int_bits(size_ty)?;
            let size_ty = size_ty.clone();
            let entry = bb.add_block();
            let loop_head = bb.add_block();
            let loop_body = bb.add_block();
            let exit = bb.add_block();
            let size = bb.param(entry, size_ty.clone());
            bb.param(entry, sig.params[1].clone());
            let i = bb.param(loop_head, size_ty.clone());
            bb.switch_to(entry);
            let ptr = bb.heap_alloc_bytes(size);
            let zero = bb.const_int(size_ty.clone(), 0);
            bb.br(loop_head, vec![zero]);
            bb.switch_to(loop_head);
            let in_range = bb.icmp(ICmpOp::Ult, size_ty.clone(), i, size);
            bb.cond_br(in_range, loop_body, exit);
            bb.switch_to(loop_body);
            let slot = bb.gep_u8(ptr, i);
            let zero_byte = bb.const_int(Ty::U8, 0);
            bb.store_u8(slot, zero_byte);
            let one = bb.const_int(size_ty.clone(), 1);
            let next = bb.binop(BinOp::Add, size_ty.clone(), i, one);
            bb.br(loop_head, vec![next]);
            bb.switch_to(exit);
            bb.ret(vec![ptr]);
            Some((entry, bb.blocks))
        }
        BuiltinKind::Dealloc => {
            let [Ty::Ptr, size_ty, align_ty] = sig.params.as_slice() else {
                return None;
            };
            if !sig.returns.is_empty() {
                return None;
            }
            let (size_ty, align_ty) = (size_ty.clone(), align_ty.clone());
            let entry = bb.add_block();
            let ptr = bb.param(entry, Ty::Ptr);
            bb.param(entry, size_ty);
            bb.param(entry, align_ty);
            bb.switch_to(entry);
            bb.push_void(Inst::Dealloc { ptr });
            bb.ret(Vec::new());
            Some((entry, bb.blocks))
        }
        BuiltinKind::Realloc => {
            let [Ty::Ptr, old_ty, align_ty, new_ty] = sig.params.as_slice() else {
                return None;
            };
            if sig.returns.as_slice() != [Ty::Ptr] || old_ty != new_ty {
                return None;
            }
            int_bits(old_ty)?;
            let size_ty = old_ty.clone();
            let align_ty = align_ty.clone();
            let entry = bb.add_block();
            let loop_head = bb.add_block();
            let loop_body = bb.add_block();
            let exit = bb.add_block();
            let old_ptr = bb.param(entry, Ty::Ptr);
            let old_size = bb.param(entry, size_ty.clone());
            bb.param(entry, align_ty);
            let new_size = bb.param(entry, size_ty.clone());
            let i = bb.param(loop_head, size_ty.clone());
            bb.switch_to(entry);
            let new_ptr = bb.heap_alloc_bytes(new_size);
            let shrinking = bb.icmp(ICmpOp::Ult, size_ty.clone(), old_size, new_size);
            let copy_len = bb.push(Inst::Select {
                ty: size_ty.clone(),
                cond: shrinking,
                then_val: old_size,
                else_val: new_size,
            });
            let zero = bb.const_int(size_ty.clone(), 0);
            bb.br(loop_head, vec![zero]);
            bb.switch_to(loop_head);
            let in_range = bb.icmp(ICmpOp::Ult, size_ty.clone(), i, copy_len);
            bb.cond_br(in_range, loop_body, exit);
            bb.switch_to(loop_body);
            let src = bb.gep_u8(old_ptr, i);
            let byte = bb.load_u8(src);
            let dst = bb.gep_u8(new_ptr, i);
            bb.store_u8(dst, byte);
            let one = bb.const_int(size_ty.clone(), 1);
            let next = bb.binop(BinOp::Add, size_ty.clone(), i, one);
            bb.br(loop_head, vec![next]);
            bb.switch_to(exit);
            bb.push_void(Inst::Dealloc { ptr: old_ptr });
            bb.ret(vec![new_ptr]);
            Some((entry, bb.blocks))
        }
        BuiltinKind::Memcpy | BuiltinKind::Memmove => {
            let [Ty::Ptr, Ty::Ptr, len_ty] = sig.params.as_slice() else {
                return None;
            };
            let returns_dst = match sig.returns.as_slice() {
                [] => false,
                [Ty::Ptr] => true,
                _ => return None,
            };
            int_bits(len_ty)?;
            let len_ty = len_ty.clone();
            let entry = bb.add_block();
            let dst = bb.param(entry, Ty::Ptr);
            let src = bb.param(entry, Ty::Ptr);
            let len = bb.param(entry, len_ty.clone());
            let finish = |bb: &mut BodyBuilder, dst| {
                if returns_dst {
                    bb.ret(vec![dst]);
                } else {
                    bb.ret(Vec::new());
                }
            };
            if kind == BuiltinKind::Memcpy {
                // Forward byte loop (the regions must not overlap, per the
                // memcpy contract).
                let loop_head = bb.add_block();
                let loop_body = bb.add_block();
                let exit = bb.add_block();
                let i = bb.param(loop_head, len_ty.clone());
                bb.switch_to(entry);
                let zero = bb.const_int(len_ty.clone(), 0);
                bb.br(loop_head, vec![zero]);
                bb.switch_to(loop_head);
                let in_range = bb.icmp(ICmpOp::Ult, len_ty.clone(), i, len);
                bb.cond_br(in_range, loop_body, exit);
                bb.switch_to(loop_body);
                let from = bb.gep_u8(src, i);
                let byte = bb.load_u8(from);
                let to = bb.gep_u8(dst, i);
                bb.store_u8(to, byte);
                let one = bb.const_int(len_ty.clone(), 1);
                let next = bb.binop(BinOp::Add, len_ty.clone(), i, one);
                bb.br(loop_head, vec![next]);
                bb.switch_to(exit);
                finish(&mut bb, dst);
            } else {
                // Overlap-safe: bounce through a temporary buffer. The
                // temporary needs `len > 0` (a zero-byte allocation is
                // rejected by the interpreter), so branch around it.
                let empty_exit = bb.add_block();
                let copy_in = bb.add_block();
                let in_head = bb.add_block();
                let in_body = bb.add_block();
                let out_start = bb.add_block();
                let out_head = bb.add_block();
                let out_body = bb.add_block();
                let done = bb.add_block();
                let i = bb.param(in_head, len_ty.clone());
                let j = bb.param(out_head, len_ty.clone());
                bb.switch_to(entry);
                let zero = bb.const_int(len_ty.clone(), 0);
                let is_empty = bb.icmp(ICmpOp::Eq, len_ty.clone(), len, zero);
                bb.cond_br(is_empty, empty_exit, copy_in);
                bb.switch_to(empty_exit);
                finish(&mut bb, dst);
                bb.switch_to(copy_in);
                let tmp = bb.heap_alloc_bytes(len);
                let zero_in = bb.const_int(len_ty.clone(), 0);
                bb.br(in_head, vec![zero_in]);
                bb.switch_to(in_head);
                let in_range = bb.icmp(ICmpOp::Ult, len_ty.clone(), i, len);
                bb.cond_br(in_range, in_body, out_start);
                bb.switch_to(in_body);
                let from = bb.gep_u8(src, i);
                let byte = bb.load_u8(from);
                let to = bb.gep_u8(tmp, i);
                bb.store_u8(to, byte);
                let one = bb.const_int(len_ty.clone(), 1);
                let next = bb.binop(BinOp::Add, len_ty.clone(), i, one);
                bb.br(in_head, vec![next]);
                bb.switch_to(out_start);
                let zero_out = bb.const_int(len_ty.clone(), 0);
                bb.br(out_head, vec![zero_out]);
                bb.switch_to(out_head);
                let out_range = bb.icmp(ICmpOp::Ult, len_ty.clone(), j, len);
                bb.cond_br(out_range, out_body, done);
                bb.switch_to(out_body);
                let from = bb.gep_u8(tmp, j);
                let byte = bb.load_u8(from);
                let to = bb.gep_u8(dst, j);
                bb.store_u8(to, byte);
                let one = bb.const_int(len_ty.clone(), 1);
                let next = bb.binop(BinOp::Add, len_ty.clone(), j, one);
                bb.br(out_head, vec![next]);
                bb.switch_to(done);
                bb.push_void(Inst::Dealloc { ptr: tmp });
                finish(&mut bb, dst);
            }
            Some((entry, bb.blocks))
        }
        BuiltinKind::Memset => {
            let [Ty::Ptr, fill_ty, len_ty] = sig.params.as_slice() else {
                return None;
            };
            let returns_dst = match sig.returns.as_slice() {
                [] => false,
                [Ty::Ptr] => true,
                _ => return None,
            };
            int_bits(fill_ty)?;
            int_bits(len_ty)?;
            let (fill_ty, len_ty) = (fill_ty.clone(), len_ty.clone());
            let entry = bb.add_block();
            let loop_head = bb.add_block();
            let loop_body = bb.add_block();
            let exit = bb.add_block();
            let dst = bb.param(entry, Ty::Ptr);
            let fill = bb.param(entry, fill_ty.clone());
            let len = bb.param(entry, len_ty.clone());
            let i = bb.param(loop_head, len_ty.clone());
            bb.switch_to(entry);
            let byte = bb.adjust_int(fill, &fill_ty, &Ty::U8)?;
            let zero = bb.const_int(len_ty.clone(), 0);
            bb.br(loop_head, vec![zero]);
            bb.switch_to(loop_head);
            let in_range = bb.icmp(ICmpOp::Ult, len_ty.clone(), i, len);
            bb.cond_br(in_range, loop_body, exit);
            bb.switch_to(loop_body);
            let slot = bb.gep_u8(dst, i);
            bb.store_u8(slot, byte);
            let one = bb.const_int(len_ty.clone(), 1);
            let next = bb.binop(BinOp::Add, len_ty.clone(), i, one);
            bb.br(loop_head, vec![next]);
            bb.switch_to(exit);
            if returns_dst {
                bb.ret(vec![dst]);
            } else {
                bb.ret(Vec::new());
            }
            Some((entry, bb.blocks))
        }
        BuiltinKind::RandomBytes => {
            // CCRandomGenerateBytes(bytes: ptr, count: len_ty) -> ret_ty:
            // deterministically zero-fill `count` bytes at `bytes`, then
            // return kCCSuccess (0). Same byte loop shape as `memset`.
            let [Ty::Ptr, len_ty] = sig.params.as_slice() else {
                return None;
            };
            let [ret_ty] = sig.returns.as_slice() else {
                return None;
            };
            int_bits(len_ty)?;
            int_bits(ret_ty)?;
            let (len_ty, ret_ty) = (len_ty.clone(), ret_ty.clone());
            let entry = bb.add_block();
            let loop_head = bb.add_block();
            let loop_body = bb.add_block();
            let exit = bb.add_block();
            let dst = bb.param(entry, Ty::Ptr);
            let len = bb.param(entry, len_ty.clone());
            let i = bb.param(loop_head, len_ty.clone());
            bb.switch_to(entry);
            let zero = bb.const_int(len_ty.clone(), 0);
            bb.br(loop_head, vec![zero]);
            bb.switch_to(loop_head);
            let in_range = bb.icmp(ICmpOp::Ult, len_ty.clone(), i, len);
            bb.cond_br(in_range, loop_body, exit);
            bb.switch_to(loop_body);
            let slot = bb.gep_u8(dst, i);
            let zero_byte = bb.const_int(Ty::U8, 0);
            bb.store_u8(slot, zero_byte);
            let one = bb.const_int(len_ty.clone(), 1);
            let next = bb.binop(BinOp::Add, len_ty.clone(), i, one);
            bb.br(loop_head, vec![next]);
            bb.switch_to(exit);
            let success = bb.const_int(ret_ty, 0);
            bb.ret(vec![success]);
            Some((entry, bb.blocks))
        }
        BuiltinKind::Memcmp => {
            let [Ty::Ptr, Ty::Ptr, len_ty] = sig.params.as_slice() else {
                return None;
            };
            let [ret_ty] = sig.returns.as_slice() else {
                return None;
            };
            int_bits(len_ty)?;
            int_bits(ret_ty)?;
            let (len_ty, ret_ty) = (len_ty.clone(), ret_ty.clone());
            let entry = bb.add_block();
            let loop_head = bb.add_block();
            let loop_body = bb.add_block();
            let advance = bb.add_block();
            let differ = bb.add_block();
            let equal = bb.add_block();
            let lhs = bb.param(entry, Ty::Ptr);
            let rhs = bb.param(entry, Ty::Ptr);
            let len = bb.param(entry, len_ty.clone());
            let i = bb.param(loop_head, len_ty.clone());
            let byte_l = bb.param(differ, Ty::U8);
            let byte_r = bb.param(differ, Ty::U8);
            bb.switch_to(entry);
            let zero = bb.const_int(len_ty.clone(), 0);
            bb.br(loop_head, vec![zero]);
            bb.switch_to(loop_head);
            let in_range = bb.icmp(ICmpOp::Ult, len_ty.clone(), i, len);
            bb.cond_br(in_range, loop_body, equal);
            bb.switch_to(loop_body);
            let lp = bb.gep_u8(lhs, i);
            let lv = bb.load_u8(lp);
            let rp = bb.gep_u8(rhs, i);
            let rv = bb.load_u8(rp);
            let same = bb.icmp(ICmpOp::Eq, Ty::U8, lv, rv);
            bb.push_void(Inst::CondBr {
                cond: same,
                then_target: advance,
                then_args: Vec::new(),
                else_target: differ,
                else_args: vec![lv, rv],
            });
            bb.switch_to(advance);
            let one = bb.const_int(len_ty.clone(), 1);
            let next = bb.binop(BinOp::Add, len_ty.clone(), i, one);
            bb.br(loop_head, vec![next]);
            bb.switch_to(differ);
            let below = bb.icmp(ICmpOp::Ult, Ty::U8, byte_l, byte_r);
            let minus_one = bb.const_int(ret_ty.clone(), -1);
            let plus_one = bb.const_int(ret_ty.clone(), 1);
            let verdict = bb.push(Inst::Select {
                ty: ret_ty.clone(),
                cond: below,
                then_val: minus_one,
                else_val: plus_one,
            });
            bb.ret(vec![verdict]);
            bb.switch_to(equal);
            let same_result = bb.const_int(ret_ty.clone(), 0);
            bb.ret(vec![same_result]);
            Some((entry, bb.blocks))
        }
    }
}

// ---------------------------------------------------------------------------
// Execution
// ---------------------------------------------------------------------------

fn render_return(value: &InterpretValue) -> String {
    match &value.kind {
        InterpretValueKind::Int(int) => {
            if int.signed {
                int.as_signed().to_string()
            } else {
                int.as_unsigned().to_string()
            }
        }
        InterpretValueKind::Bool(b) => u8::from(*b).to_string(),
        InterpretValueKind::FloatBits(bits) => match value.ty {
            Ty::F32 => format!("{:?}", f32::from_bits(*bits as u32)),
            _ => format!("{:?}", f64::from_bits(*bits)),
        },
        InterpretValueKind::NullPtr => "null".to_string(),
        InterpretValueKind::Ptr(ptr) => {
            format!("ptr(alloc {}, offset {})", ptr.allocation, ptr.offset)
        }
        InterpretValueKind::Unit => "()".to_string(),
        other => format!("{other:?}"),
    }
}

fn report_interpret_error(error: &InterpretError, synthesis: &SynthesisReport) {
    if let Some(name) = error.block.and_then(|block| synthesis.trap_name(block)) {
        eprintln!(
            "trap: reached extern builtin stub @{name} — the program called a bodyless \
             extern. For a pure battery program this is a FINDING: either a panic path \
             was taken or the emitted IR diverges from the native binary."
        );
        return;
    }
    eprintln!("interpreter error: {error}");
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn cmd_run(
    paths: &[PathBuf],
    fmt: Option<Format>,
    entry: &str,
    fuel: u64,
    max_call_depth: u64,
    mem_budget: u64,
    do_validate: bool,
) -> u8 {
    // 1. Load every module.
    let module_paths = match collect_module_paths(paths) {
        Ok(paths) => paths,
        Err(message) => {
            eprintln!("error: {message}");
            return EXIT_USER;
        }
    };
    let mut modules = Vec::with_capacity(module_paths.len());
    for path in &module_paths {
        let module = match load_one(path, fmt) {
            Ok(module) => module,
            Err((code, message)) => {
                eprintln!("error: {message}");
                return code;
            }
        };
        modules.push((path.display().to_string(), module));
    }

    // 2. Link into one executable image.
    let mut image = match link_modules(&modules) {
        Ok(image) => image,
        Err(message) => {
            eprintln!("error: {message}");
            return EXIT_USER;
        }
    };
    drop(modules);

    // 3. Devirtualize SymbolAddr vtables (dyn dispatch), legalize bool/ptr
    //    compares (interpreter-vs-validator gap; see the pass docs), then
    //    synthesize builtins / trap stubs for remaining externs. The trap
    //    table is shared: dispatch-miss blocks and extern stubs both map an
    //    error block id back to a name.
    let mut trap_names = Vec::new();
    if let Err(message) = devirtualize_symbol_addrs(&mut image, entry, &mut trap_names) {
        eprintln!("error: {message}");
        return EXIT_USER;
    }
    let legalized = legalize_icmp(&mut image);
    if legalized > 0 {
        eprintln!("legalized {legalized} bool/ptr icmp(s)");
    }
    let synthesis = synthesize_builtins(&mut image, trap_names);
    let defined = image.functions.len() - synthesis.stub_count - synthesis.builtins.len();
    eprintln!(
        "linked {} module(s): {} function(s) ({} defined, {} builtin, {} trap stub(s)), \
         {} global(s)",
        module_paths.len(),
        image.functions.len(),
        defined,
        synthesis.builtins.len(),
        synthesis.stub_count,
        image.globals.len()
    );
    if !synthesis.builtins.is_empty() {
        let listed: Vec<String> = synthesis
            .builtins
            .iter()
            .map(|(name, label)| format!("{label} <- @{name}"))
            .collect();
        eprintln!("builtins: {}", listed.join(", "));
    }

    // 4. Optional validation of the linked image.
    if do_validate {
        let report = trust_ir_build::validate::validate_module_report(&image);
        let errors = report.errors();
        if !errors.is_empty() {
            eprintln!(
                "validation of linked image failed ({} errors):",
                errors.len()
            );
            for (i, error) in errors.iter().enumerate() {
                eprintln!("  [{i}] {error:?}");
            }
            return EXIT_USER;
        }
        eprintln!("linked image is well-formed");
    }

    // 5. Resolve the entry point.
    let Some(func) = image.function_by_name(entry) else {
        eprintln!("error: no function named @{entry} in the linked image");
        return EXIT_USER;
    };
    let func_id = func.id;
    if func.blocks.is_empty() {
        eprintln!("error: entry @{entry} has no body in any input module");
        return EXIT_USER;
    }
    match image.func_type(func.ty) {
        Some(sig) if !sig.params.is_empty() => {
            eprintln!(
                "error: entry @{entry} takes {} parameter(s) ({}); `run` only executes \
                 nullary entry points",
                sig.params.len(),
                render_sig(sig)
            );
            return EXIT_USER;
        }
        Some(_) => {}
        None => {
            eprintln!("error: entry @{entry} references an undefined signature");
            return EXIT_USER;
        }
    }

    // 6. Execute on a dedicated big-stack thread (the interpreter recurses on
    //    the host stack per interpreted call).
    let options = InterpretOptions {
        fuel,
        max_call_depth,
        mem_budget,
    };
    let worker = std::thread::Builder::new()
        .name("trust-ir-run".to_string())
        .stack_size(RUN_STACK_BYTES)
        .spawn(move || -> Result<InterpretOutcome, InterpretError> {
            let interpreter = Interpreter::with_module(&image).with_options(options);
            interpreter.execute_func(func_id, [])
        });
    let worker = match worker {
        Ok(handle) => handle,
        Err(error) => {
            eprintln!("error: spawn interpreter thread: {error}");
            return EXIT_IO;
        }
    };
    match worker.join() {
        Ok(Ok(outcome)) => {
            for value in &outcome.returns {
                println!("{}", render_return(value));
            }
            eprintln!("executed {} step(s)", outcome.steps);
            EXIT_OK
        }
        Ok(Err(error)) => {
            report_interpret_error(&error, &synthesis);
            EXIT_USER
        }
        Err(_) => {
            eprintln!("error: interpreter thread panicked");
            EXIT_IO
        }
    }
}

/// Load one module file: explicit `--format` wins, otherwise the extension
/// decides (matching the rest of the CLI).
fn load_one(path: &Path, fmt: Option<Format>) -> Result<Module, (u8, String)> {
    let format = Format::resolve(fmt, path).map_err(|message| (EXIT_USER, message))?;
    let bytes = read_input(path).map_err(|e| (EXIT_IO, format!("read {}: {e}", path.display())))?;
    decode_module(format, &bytes)
        .map_err(|message| (EXIT_IO, format!("{}: {message}", path.display())))
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{ScopeData, Space, Universe};

    fn test_global(name: &str, ty: Ty) -> Global {
        Global {
            name: name.to_string(),
            ty,
            mutable: false,
            initializer: None,
            linkage: Linkage::External,
            tls: None,
            align: None,
        }
    }

    fn refined_array_module(name: &str, global_name: &str) -> Module {
        let mut module = Module::new(name);
        let universe = module
            .intern_universe(Universe::range(10, 20).expect("canonical range"))
            .expect("universe interns");
        let member = module
            .intern_pred(Pred::InUniverse(universe, Space::Member))
            .expect("membership predicate interns");
        let nonzero = module
            .intern_pred(Pred::NonZero)
            .expect("nonzero predicate interns");
        let both = module
            .intern_pred(Pred::Conj(vec![member, nonzero]))
            .expect("conjunction interns");
        let base = module.add_type(Ty::I32);
        let refined = module.add_type(Ty::Refine(base, both));
        module
            .globals
            .push(test_global(global_name, Ty::Array(refined, 4)));
        module
    }

    #[test]
    fn linker_remaps_refinement_tables_deterministically_and_roundtrips() {
        let modules = vec![
            ("a".to_string(), refined_array_module("a", "ga")),
            ("b".to_string(), refined_array_module("b", "gb")),
        ];
        let linked = link_modules(&modules).expect("refined modules link");
        let linked_again = link_modules(&modules).expect("repeat link succeeds");
        assert_eq!(linked, linked_again, "linking must be deterministic");
        assert_eq!(linked.universes.len(), 1, "equal universes are shared");
        assert_eq!(linked.predicates.len(), 3, "equal predicates are shared");
        assert_eq!(linked.types.len(), 2, "base and refined types are shared");
        assert_eq!(linked.globals[0].ty, linked.globals[1].ty);

        let Ty::Array(refined, 4) = linked.globals[0].ty else {
            panic!("linked global did not preserve the nested refined array")
        };
        let Ty::Refine(base, pred) = linked.types[refined.as_usize()] else {
            panic!("array element did not remap to a refinement")
        };
        assert_eq!(linked.types[base.as_usize()], Ty::I32);
        assert_eq!(
            linked.predicates[pred.as_usize()],
            Pred::Conj(vec![PredId::new(0), PredId::new(1)])
        );

        let bytes = trust_ir::binary::serialize_module(&linked);
        let roundtrip = trust_ir::binary::deserialize_module(&bytes).expect("linked image decodes");
        assert_eq!(
            roundtrip, linked,
            "refinement tables survive binary round-trip"
        );
        let report = trust_ir_build::validate::validate_module_report(&roundtrip);
        let errors = report.errors();
        assert!(
            errors.is_empty(),
            "linked refinement image must validate: {errors:?}"
        );
    }

    #[test]
    fn linker_preserves_debug_metadata_and_remaps_scope_files() {
        let mut prefix = Module::new("prefix");
        prefix.intern_file("src/prefix.rs");

        let mut source = Module::new("source");
        let source_file = source.intern_file("src/source.rs");
        let signature = source.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "identity", signature, BlockId::new(0));
        function.value_names = Some(vec![(ValueId::new(7), "input".to_string())]);
        function.scopes = Some(vec![ScopeData {
            parent: None,
            span: Some(SourceSpan {
                file: source_file,
                line: 1,
                col: 0,
            }),
        }]);
        let mut entry = Block::new(BlockId::new(0));
        entry.params.push((ValueId::new(7), Ty::I32));
        entry.body.push(
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(7)],
            })
            .with_span(SourceSpan {
                file: source_file,
                line: 2,
                col: 4,
            })
            .with_scope(0),
        );
        function.blocks.push(entry);
        source.add_function(function);

        let linked = link_modules(&[
            ("prefix".to_string(), prefix),
            ("source".to_string(), source),
        ])
        .expect("debug-bearing modules link");
        assert_eq!(
            linked.files,
            vec!["src/prefix.rs".to_string(), "src/source.rs".to_string()]
        );
        let function = &linked.functions[0];
        assert_eq!(
            function.value_names.as_deref(),
            Some(&[(ValueId::new(7), "input".to_string())][..])
        );
        assert_eq!(function.scopes.as_ref().unwrap()[0].span.unwrap().file, 1);
        assert_eq!(function.blocks[0].body[0].span.unwrap().file, 1);
        assert_eq!(function.blocks[0].body[0].scope, Some(0));

        let errors = trust_ir_build::validate_module(&linked);
        assert!(
            errors.is_empty(),
            "linked debug metadata must remain referentially valid: {errors:#?}"
        );
    }

    #[test]
    fn linker_rejects_dangling_refinement_table_ids() {
        let mut bad_base = Module::new("bad-base");
        let pred = bad_base
            .intern_pred(Pred::NonZero)
            .expect("predicate interns");
        bad_base
            .globals
            .push(test_global("bad_base", Ty::Refine(TyId::new(99), pred)));
        let err = link_modules(&[("bad-base".to_string(), bad_base)])
            .expect_err("dangling base must fail closed");
        assert!(
            err.contains("ty.99 is out of range"),
            "unexpected error: {err}"
        );

        let mut bad_universe = Module::new("bad-universe");
        bad_universe
            .predicates
            .push(Pred::InUniverse(UnivId::new(99), Space::Member));
        let err = link_modules(&[("bad-universe".to_string(), bad_universe)])
            .expect_err("unused dangling universe must fail closed");
        assert!(
            err.contains("univ.99 is out of range"),
            "unexpected error: {err}"
        );

        let mut bad_pred = Module::new("bad-pred");
        let base = bad_pred.add_type(Ty::I32);
        bad_pred
            .globals
            .push(test_global("bad_pred", Ty::Refine(base, PredId::new(99))));
        let err = link_modules(&[("bad-pred".to_string(), bad_pred)])
            .expect_err("dangling predicate must fail closed");
        assert!(
            err.contains("pred.99 is out of range"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn linker_rejects_refinement_whose_base_is_refined() {
        let mut module = Module::new("nested-refine");
        let pred = module
            .intern_pred(Pred::NonZero)
            .expect("predicate interns");
        let base = module.add_type(Ty::I32);
        let inner = module.add_type(Ty::Refine(base, pred));
        module
            .globals
            .push(test_global("nested", Ty::Refine(inner, pred)));
        let err = link_modules(&[("nested-refine".to_string(), module)])
            .expect_err("Refine-on-Refine must fail closed");
        assert!(
            err.contains("refinement base ty.1 is itself a Refine"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn v0_intrinsic_name_extracts_length_prefixed_ident() {
        assert_eq!(
            v0_intrinsic_name("_RINvNtCsbu97CrmFxuv_4core10intrinsics5ctpopyECs_7fc_bits"),
            Some("ctpop".to_string())
        );
        assert_eq!(
            v0_intrinsic_name(
                "_RINvNtCsbu97CrmFxuv_4core10intrinsics20unchecked_funnel_shlyECs_8fc_float"
            ),
            Some("unchecked_funnel_shl".to_string())
        );
        assert_eq!(
            v0_intrinsic_name("_RNvNtCsbu97CrmFxuv_4core10intrinsics15caller_locationCs_8fc"),
            Some("caller_location".to_string())
        );
        assert_eq!(
            v0_intrinsic_name("_RNvCsoF1AqU8Qvp_7___rustc17rust_begin_unwind"),
            None
        );
    }

    #[test]
    fn classify_matches_the_battery_externs() {
        use BuiltinKind::*;
        assert_eq!(
            BuiltinKind::classify("_RNvCsoF1AqU8Qvp_7___rustc12___rust_alloc"),
            Alloc
        );
        assert_eq!(
            BuiltinKind::classify("_RNvCsoF1AqU8Qvp_7___rustc19___rust_alloc_zeroed"),
            AllocZeroed
        );
        assert_eq!(
            BuiltinKind::classify("_RNvCsoF1AqU8Qvp_7___rustc14___rust_dealloc"),
            Dealloc
        );
        assert_eq!(
            BuiltinKind::classify("_RNvCsoF1AqU8Qvp_7___rustc26___rust_alloc_error_handler"),
            Trap
        );
        assert_eq!(
            BuiltinKind::classify(
                "_RNvCsoF1AqU8Qvp_7___rustc35___rust_no_alloc_shim_is_unstable_v2"
            ),
            NoOp
        );
        assert_eq!(
            BuiltinKind::classify(
                "_RINvNtCsbu97CrmFxuv_4core10intrinsics12ctlz_nonzeroyECs_7fc_bits"
            ),
            Ctlz
        );
        // The check/hint no-op family: the 16-char length prefix must not
        // swallow the trailing generic-args mangling (`Acj3_E…`).
        assert_eq!(
            BuiltinKind::classify(
                "_RINvNtCsbu97CrmFxuv_4core10intrinsics16assert_inhabitedAcj3_ECs_9fc_strops"
            ),
            NoOp
        );
        assert_eq!(
            BuiltinKind::classify(
                "_RINvNtCsbu97CrmFxuv_4core10intrinsics23is_val_statically_knownyECs_6fc_fmt"
            ),
            ConstFalse
        );
        assert_eq!(
            BuiltinKind::classify("_RNvNtCsbu97CrmFxuv_4core10intrinsics9cold_pathCs_6fc_fmt"),
            NoOp
        );
        assert_eq!(
            BuiltinKind::classify("_RNvCsoF1AqU8Qvp_7___rustc17rust_begin_unwind"),
            Trap
        );
        assert_eq!(BuiltinKind::classify("memmove"), Memmove);
        // The macOS RNG seed source, with and without the leading underscore
        // the object symbol may carry.
        assert_eq!(BuiltinKind::classify("CCRandomGenerateBytes"), RandomBytes);
        assert_eq!(BuiltinKind::classify("_CCRandomGenerateBytes"), RandomBytes);
        // `compare_bytes` is memcmp; `exact_div` is its own division builtin.
        assert_eq!(
            BuiltinKind::classify(
                "_RNvNtCsbu97CrmFxuv_4core10intrinsics13compare_bytesCs_12fc_sortdedup"
            ),
            Memcmp
        );
        assert_eq!(
            BuiltinKind::classify(
                "_RINvNtCsbu97CrmFxuv_4core10intrinsics9exact_divjECs_11fc_strbuild"
            ),
            ExactDiv
        );
    }

    /// `exact_div(a, b)` lowers to an unsigned `UDiv` (`u64`) or signed
    /// `SDiv` (`i64`) per its lane, and its body executes to `a / b`.
    #[test]
    fn exact_div_body_divides_by_lane_signedness() {
        for (word, dividend, divisor, expected) in [
            (Ty::U64, 84_i128, 4, 21_i128),
            (Ty::I64, -84_i128, 4, -21_i128),
        ] {
            let sig = FuncTy {
                params: vec![word.clone(), word.clone()],
                returns: vec![word.clone()],
                is_vararg: false,
            };
            let (entry, blocks) =
                build_builtin_body(BuiltinKind::ExactDiv, &sig).expect("exact_div body builds");
            let mut module = Module::new("exact_div_test");
            let ft = FuncTyId::new(0);
            module.func_types.push(sig);
            let mut func = Function::new(FuncId::new(0), "exact_div", ft, entry);
            func.blocks = blocks;
            module.functions.push(func);

            let a = InterpretValue::int(word.clone(), dividend).unwrap();
            let b = InterpretValue::int(word.clone(), divisor).unwrap();
            let outcome = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [a, b])
                .expect("exact_div executes");
            let got = outcome.returns[0].as_int().unwrap();
            let got = if int_is_signed(&word).unwrap() {
                got.as_signed()
            } else {
                got.as_unsigned() as i128
            };
            assert_eq!(got, expected, "exact_div {word} lane");
        }
    }

    /// `compare_bytes(a, b, n)` returns the sign of the first differing byte
    /// (memcmp semantics), 0 when the prefixes are equal.
    #[test]
    fn compare_bytes_body_has_memcmp_semantics() {
        let sig = FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr, Ty::U64],
            returns: vec![Ty::I32],
            is_vararg: false,
        };
        let (entry, blocks) =
            build_builtin_body(BuiltinKind::Memcmp, &sig).expect("compare_bytes body builds");
        // Two 3-byte buffers written into interpreter memory, compared.
        let mut module = Module::new("compare_bytes_test");
        let cmp_ft = FuncTyId::new(0);
        module.func_types.push(sig);
        let harness_ft = FuncTyId::new(1);
        module.func_types.push(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut cmp = Function::new(FuncId::new(0), "compare_bytes", cmp_ft, entry);
        cmp.blocks = blocks;

        // harness(): a=[1,2,3], b=[1,2,4] -> compare_bytes returns -1.
        let mut bb = BodyBuilder::new();
        let hb = bb.add_block();
        bb.switch_to(hb);
        let three = bb.const_int(Ty::U64, 3);
        let a = bb.heap_alloc_bytes(three);
        let b = bb.heap_alloc_bytes(three);
        for (i, (av, bv)) in [(1, 1), (2, 2), (3, 4)].into_iter().enumerate() {
            let off = bb.const_int(Ty::U64, i as i128);
            let ap = bb.gep_u8(a, off);
            let abyte = bb.const_int(Ty::U8, av);
            bb.store_u8(ap, abyte);
            let bp = bb.gep_u8(b, off);
            let bbyte = bb.const_int(Ty::U8, bv);
            bb.store_u8(bp, bbyte);
        }
        let n = bb.const_int(Ty::U64, 3);
        let res = bb.push(Inst::Call {
            callee: FuncId::new(0),
            args: vec![a, b, n],
        });
        bb.ret(vec![res]);
        let mut harness = Function::new(FuncId::new(1), "harness", harness_ft, hb);
        harness.blocks = bb.blocks;

        module.functions.push(cmp);
        module.functions.push(harness);

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(1), [])
            .expect("compare_bytes harness executes");
        assert_eq!(outcome.returns[0].as_int().unwrap().as_signed(), -1);
    }

    /// `CCRandomGenerateBytes(bytes, count)` zero-fills the buffer and
    /// returns `kCCSuccess` (0). A harness pre-seeds the buffer with `0xFF`s,
    /// calls the builtin, then reads a byte back to prove it was overwritten.
    #[test]
    fn random_bytes_body_zero_fills_and_returns_success() {
        let sig = FuncTy {
            params: vec![Ty::Ptr, Ty::U64],
            returns: vec![Ty::I32],
            is_vararg: false,
        };
        let (entry, blocks) =
            build_builtin_body(BuiltinKind::RandomBytes, &sig).expect("random_bytes body builds");
        let mut module = Module::new("random_bytes_test");
        let rng_ft = FuncTyId::new(0);
        module.func_types.push(sig);
        let harness_ft = FuncTyId::new(1);
        module.func_types.push(FuncTy {
            params: Vec::new(),
            // (return code, first output byte)
            returns: vec![Ty::I32, Ty::U8],
            is_vararg: false,
        });

        let mut rng = Function::new(FuncId::new(0), "random_bytes", rng_ft, entry);
        rng.blocks = blocks;

        // harness(): buf=[0xFF; 4]; rc = random_bytes(buf, 4); return (rc, buf[0]).
        let mut bb = BodyBuilder::new();
        let hb = bb.add_block();
        bb.switch_to(hb);
        let four = bb.const_int(Ty::U64, 4);
        let buf = bb.heap_alloc_bytes(four);
        for i in 0..4i128 {
            let off = bb.const_int(Ty::U64, i);
            let slot = bb.gep_u8(buf, off);
            let ff = bb.const_int(Ty::U8, 0xFF);
            bb.store_u8(slot, ff);
        }
        let count = bb.const_int(Ty::U64, 4);
        let rc = bb.push(Inst::Call {
            callee: FuncId::new(0),
            args: vec![buf, count],
        });
        let zero_off = bb.const_int(Ty::U64, 0);
        let first_slot = bb.gep_u8(buf, zero_off);
        let first = bb.load_u8(first_slot);
        bb.ret(vec![rc, first]);
        let mut harness = Function::new(FuncId::new(1), "harness", harness_ft, hb);
        harness.blocks = bb.blocks;

        module.functions.push(rng);
        module.functions.push(harness);

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(1), [])
            .expect("random_bytes harness executes");
        assert_eq!(
            outcome.returns[0].as_int().unwrap().as_signed(),
            0,
            "kCCSuccess"
        );
        assert_eq!(
            outcome.returns[1].as_int().unwrap().as_unsigned(),
            0,
            "buffer byte was overwritten to zero"
        );
    }

    #[test]
    fn tuple_field_offsets_match_c_layout() {
        // (ptr, u8×8): a &str-shaped tuple — ptr at 0, bytes at 8..16.
        let str_shape = [
            Ty::Ptr,
            Ty::U8,
            Ty::U8,
            Ty::U8,
            Ty::U8,
            Ty::U8,
            Ty::U8,
            Ty::U8,
            Ty::U8,
        ];
        assert_eq!(
            tuple_field_offsets(&str_shape),
            Some(vec![0, 8, 9, 10, 11, 12, 13, 14, 15])
        );
        // (u8, ptr): the pointer field is aligned up to offset 8.
        assert_eq!(tuple_field_offsets(&[Ty::U8, Ty::Ptr]), Some(vec![0, 8]));
        // A non-scalar field aborts the computation.
        assert_eq!(tuple_field_offsets(&[Ty::Ptr, Ty::Tuple(vec![])]), None);
    }

    #[test]
    fn abi_compatible_ty_treats_pointer_and_word_ints_alike() {
        assert!(abi_compatible_ty(&Ty::Ptr, &Ty::U64));
        assert!(abi_compatible_ty(&Ty::Usize, &Ty::Ptr));
        assert!(abi_compatible_ty(&Ty::I64, &Ty::Ptr));
        assert!(abi_compatible_ty(&Ty::U32, &Ty::U32));
        assert!(!abi_compatible_ty(&Ty::U32, &Ty::Ptr));
        assert!(!abi_compatible_ty(&Ty::F64, &Ty::U64));
    }
}
