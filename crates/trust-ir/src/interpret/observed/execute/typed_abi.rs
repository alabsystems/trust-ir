// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private observed source/register/carrier transport. All signature records
//! remain attached. No ordinary ABI, image, layout or execution fallback is
//! permitted. A plan is borrowed interpreter DATA, never target/proof authority.
use super::*;
use crate::signature_abi::{
    AbiArgument, AbiAttributes, AbiBinding, AbiBindingPlace, AbiCapture, AbiExtension, AbiPassMode,
    AbiRegister, AbiScalar, SignatureAbi,
};
use core::mem::size_of;

pub(super) struct Plan<'m> {
    signature: &'m FuncTy,
    abi: &'m SignatureAbi,
}

fn mismatch(block: BlockId, detail: &'static str) -> Fault {
    Fault::Semantic(signature_mismatch(block, detail))
}

/// Perform the actual canonical paid validation before observing transport
/// DATA. Every descriptor, including unused/FnPtr-only records, participates;
/// every actual function's legacy facts are independently reconciled.
pub(super) fn preflight<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    supplied: &Function,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<()> {
    let module = interpreter
        .module
        .ok_or(Fault::Unsupported("observed ABI module"))?;
    for signature in &module.func_types {
        event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
        let Some(abi) = &signature.abi else { continue };
        abi.validate_observed(signature, session, site)?
            .map_err(|detail| Fault::Semantic(signature_mismatch(supplied.entry, detail)))?;
        abi.validate_target_observed(module.target_info.as_ref(), session, site)?
            .map_err(|detail| Fault::Semantic(signature_mismatch(supplied.entry, detail)))?;
        check_plan(interpreter, signature, abi, session, site, supplied.entry)?;
    }
    for function in module.functions.iter().chain(core::iter::once(supplied)) {
        event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
        let signature = module
            .func_types
            .get(function.ty.as_usize())
            .ok_or_else(|| mismatch(supplied.entry, "observed ABI function signature is absent"))?;
        if let Some(abi) = &signature.abi {
            abi.reconcile_function_observed(function, session, site)?
                .map_err(|detail| Fault::Semantic(signature_mismatch(supplied.entry, detail)))?;
        }
    }
    check_module_types(module, session, site)?;
    Ok(())
}

/// The ordinary interpreter refuses whole-module storage/value violations.
/// Do not call its opaque layout/type visitor under an observer. Inspect the
/// complete actual type-bearing population through paid borrowed projections;
/// nominal, storage and non-byte aggregate families remain explicit debt.
pub(super) fn check_module_types<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<()> {
    for ty in &module.types {
        startup::check_type(module, ty, session, site)?;
    }
    for signature in &module.func_types {
        event(session, site, ExecutionPhase::Validation, 1, 0)?;
        for ty in signature.params.iter().chain(&signature.returns) {
            startup::check_type(module, ty, session, site)?;
        }
    }
    for definition in &module.structs {
        event(session, site, ExecutionPhase::Validation, 1, 0)?;
        for field in &definition.fields {
            startup::check_type(module, &field.ty, session, site)?;
        }
    }
    for definition in &module.records {
        event(session, site, ExecutionPhase::Validation, 1, 0)?;
        for field in &definition.fields {
            startup::check_type(module, &field.ty, session, site)?;
        }
    }
    for definition in &module.enums {
        event(session, site, ExecutionPhase::Validation, 1, 0)?;
        for variant in &definition.variants {
            event(session, site, ExecutionPhase::Validation, 1, 0)?;
            for ty in &variant.fields {
                startup::check_type(module, ty, session, site)?;
            }
        }
    }
    for closure in &module.closure_types {
        event(session, site, ExecutionPhase::Validation, 1, 0)?;
        for ty in &closure.captures {
            startup::check_type(module, ty, session, site)?;
        }
    }
    for global in &module.globals {
        startup::check_type(module, &global.ty, session, site)?;
    }
    for row in &module.drop_glue {
        startup::check_type(module, &row.ty, session, site)?;
    }
    for function in &module.functions {
        event(session, site, ExecutionPhase::Validation, 1, 0)?;
        for block in &function.blocks {
            event(session, site, ExecutionPhase::Validation, 1, 0)?;
            for (_, ty) in &block.params {
                startup::check_type(module, ty, session, site)?;
            }
            for node in &block.body {
                event(session, site, ExecutionPhase::Validation, 1, 0)?;
                // Dialect type-valued attributes need their own paid complete
                // visitor. They cannot hide storage behind the inline header.
                if matches!(node.inst, Inst::DialectOp(_)) {
                    return Err(Fault::Unsupported(
                        "observed ABI whole-module dialect type attributes",
                    ));
                }
                let roots = node.inst.inline_types_observed(session, site)?;
                let checked: RunResult<()> = (|| {
                    for ty in &roots {
                        startup::check_type(module, ty, session, site)?;
                    }
                    Ok(())
                })();
                session.retirement_step(site, roots.len().saturating_add(1));
                drop(roots);
                checked?;
            }
        }
    }
    event(session, site, ExecutionPhase::Validation, 0, 0)
}

/// Borrow the signature already selected and checked by actual startup; no
/// repeated module lookup, layout query, cloned record or public constructor.
pub(super) fn plan(signature: &FuncTy) -> Option<Plan<'_>> {
    signature.abi.as_ref().map(|abi| Plan { signature, abi })
}

fn check_attributes(attributes: &AbiAttributes, scalar: bool) -> RunResult<()> {
    if attributes.capture != AbiCapture::Any
        || attributes.no_alias
        || attributes.nonnull
        || attributes.readonly
        || attributes.writable
        || attributes.no_free
        || attributes.pointee_size != 0
        || attributes.pointee_align.is_some()
    {
        return Err(Fault::Unsupported(
            "observed ABI pointer access/provenance contract",
        ));
    }
    if !scalar && attributes.extension != AbiExtension::None {
        return Err(Fault::Unsupported(
            "observed ABI cast extension without defined scalar bits",
        ));
    }
    Ok(())
}

fn check_plan<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    signature: &FuncTy,
    abi: &SignatureAbi,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    block: BlockId,
) -> RunResult<()> {
    if abi.target.pointer_bytes != 8 || !abi.target.little_endian {
        return Err(Fault::Unsupported(
            "noncanonical observed ABI pointer layout",
        ));
    }
    if !abi.can_unwind && interpreter.options.panic_strategy == PanicStrategy::Unwind {
        return Err(Fault::Unsupported("observed typed no-unwind crossing"));
    }
    for (result, argument) in abi
        .arguments
        .iter()
        .map(|arg| (false, arg))
        .chain(core::iter::once((true, &abi.result)))
    {
        event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
        match &argument.mode {
            AbiPassMode::Ignore => {}
            AbiPassMode::Direct(scalar) => {
                check_scalar(signature, argument, scalar, session, site)?
            }
            AbiPassMode::Pair(a, b) => {
                check_scalar(signature, argument, a, session, site)?;
                check_scalar(signature, argument, b, session, site)?;
            }
            AbiPassMode::Cast {
                rest, attributes, ..
            } => {
                check_attributes(attributes, false)?;
                if rest.total.div_ceil(rest.unit.bytes) > 4096 {
                    return Err(Fault::Unsupported(
                        "observed ABI cast register population exceeds reference capacity",
                    ));
                }
            }
            AbiPassMode::Indirect {
                attributes,
                metadata_attributes,
                on_stack,
                caller_copy,
            } => {
                if result || *on_stack || !*caller_copy || metadata_attributes.is_some() {
                    return Err(Fault::Unsupported(
                        "observed ABI stack/hidden/borrowed/metadata indirect transport",
                    ));
                }
                if attributes != &AbiAttributes::default() {
                    return Err(Fault::Unsupported(
                        "observed byval attributes/provenance contract",
                    ));
                }
                // The canonical validator also checks this complete binding.
                // Reconcile the actual carrier, not just its descriptor bytes.
                let [binding] = argument.bindings.as_slice() else {
                    return Err(mismatch(
                        block,
                        "observed byval needs one complete pointer binding",
                    ));
                };
                if !matches!(binding.place, AbiBindingPlace::Parameter(_))
                    || signature.params.get(index(binding)) != Some(&Ty::Ptr)
                    || binding.source_offset != 0
                    || binding.source_bytes != argument.size
                    || binding.carrier_offset != 0
                    || binding.carrier_bytes != 8
                {
                    return Err(mismatch(
                        block,
                        "observed byval actual pointer binding differs",
                    ));
                }
            }
        }
        for binding in &argument.bindings {
            event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
            let types = match binding.place {
                AbiBindingPlace::Parameter(_) | AbiBindingPlace::HiddenResult(_) => {
                    &signature.params
                }
                AbiBindingPlace::Result(_) => &signature.returns,
            };
            let ty = types
                .get(index(binding))
                .ok_or_else(|| mismatch(block, "observed ABI carrier is absent"))?;
            let (size, _) = memory::shape(interpreter, ty, session, site)?;
            if binding
                .carrier_offset
                .checked_add(binding.carrier_bytes)
                .is_none_or(|end| end > size)
            {
                return Err(mismatch(
                    block,
                    "observed ABI binding exceeds actual carrier layout",
                ));
            }
        }
    }
    // Scalar and flat-U8 layouts have no padding fields. Check EVERY live
    // actual carrier byte using compressed images, never logical-size loops.
    for (result, types) in [(false, &signature.params), (true, &signature.returns)] {
        for (at, ty) in types.iter().enumerate() {
            event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
            let (size, _) = memory::shape(interpreter, ty, session, site)?;
            let mut census =
                ByteStore::new_observed(size, None, &mut session.structural_owned(site))?;
            let checked = (|| {
                for argument in abi.arguments.iter().chain(core::iter::once(&abi.result)) {
                    event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
                    for binding in &argument.bindings {
                        event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
                        let here = match binding.place {
                            AbiBindingPlace::Parameter(i) | AbiBindingPlace::HiddenResult(i) => {
                                !result && i as usize == at
                            }
                            AbiBindingPlace::Result(i) => result && i as usize == at,
                        };
                        if here {
                            let image = Image::uniform_observed(
                                Some(0),
                                binding.carrier_bytes,
                                &mut session.structural_owned(site),
                            )?;
                            let written = census.write_observed(
                                binding.carrier_offset,
                                &image,
                                &mut session.structural_owned(site),
                            );
                            retire_image(image, session, site);
                            written?;
                        }
                    }
                }
                let image = census.read_observed(0, size, &mut session.structural_owned(site))?;
                let checked = initialized(&image, session, site).and_then(|valid| {
                    if valid {
                        Ok(())
                    } else {
                        Err(mismatch(
                            block,
                            "observed ABI omits live bytes of an actual carrier",
                        ))
                    }
                });
                retire_image(image, session, site);
                checked
            })();
            retire_store(census, session, site);
            checked?;
        }
    }
    event(session, site, ExecutionPhase::AbiScan, 0, 0)
}

fn check_scalar<O: ExecutionObserver>(
    signature: &FuncTy,
    argument: &AbiArgument,
    scalar: &AbiScalar,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<()> {
    event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
    check_attributes(&scalar.attributes, true)?;
    if scalar.attributes.extension == AbiExtension::None && scalar.value_bits % 8 != 0 {
        let mut exact_bool = false;
        for binding in &argument.bindings {
            event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
            let types = match binding.place {
                AbiBindingPlace::Parameter(_) | AbiBindingPlace::HiddenResult(_) => {
                    &signature.params
                }
                AbiBindingPlace::Result(_) => &signature.returns,
            };
            exact_bool |= scalar.value_bits == 1
                && scalar.source_bytes == 1
                && types.get(index(binding)) == Some(&Ty::Bool)
                && binding.source_offset == scalar.source_offset
                && binding.source_bytes == 1
                && binding.carrier_offset == 0
                && binding.carrier_bytes == 1;
        }
        if !exact_bool {
            return Err(Fault::Unsupported(
                "observed ABI partially defined byte needs per-bit poison",
            ));
        }
    }
    Ok(())
}

fn index(binding: &AbiBinding) -> usize {
    match binding.place {
        AbiBindingPlace::Parameter(i)
        | AbiBindingPlace::Result(i)
        | AbiBindingPlace::HiddenResult(i) => i as usize,
    }
}

fn initialized<O: ExecutionObserver>(
    image: &Image,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<bool> {
    let mut poison = false;
    image.try_for_each_stored_observed(&mut session.structural_owned(site), |byte, progress| {
        progress.admit(ExecutionPhase::AbiScan, 1, 0)?;
        poison |= byte.is_none();
        Ok(())
    })?;
    Ok(!poison)
}
fn defined<O: ExecutionObserver>(
    image: &Image,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    block: BlockId,
) -> RunResult<()> {
    if !initialized(image, session, site)? {
        return Err(Fault::Semantic(ub(
            block,
            "observed ABI has uninitialized live bytes",
        )));
    }
    Ok(())
}

/// Cleanup remains with the original observer after any first refusal.
fn retire_image<O: ExecutionObserver>(
    image: Image,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    image.retire_observed(&mut session.structural_owned(site));
}
fn retire_store<O: ExecutionObserver>(
    store: ByteStore,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    store.retire_observed(&mut session.structural_owned(site));
}

struct RegisterImage {
    offset: Option<u64>,
    live: u64,
    image: Image,
}
#[derive(Default)]
struct Scratch {
    source: Option<ByteStore>,
    transported: Option<ByteStore>,
    registers: Vec<RegisterImage>,
    carriers: Vec<(usize, ByteStore)>,
}
impl Scratch {
    fn retire<O: ExecutionObserver>(
        mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        if let Some(store) = self.source.take() {
            retire_store(store, session, site);
        }
        if let Some(store) = self.transported.take() {
            retire_store(store, session, site);
        }
        while let Some(register) = self.registers.pop() {
            session.retirement_step(site, 1);
            retire_image(register.image, session, site);
        }
        while let Some((_, store)) = self.carriers.pop() {
            session.retirement_step(site, 1);
            retire_store(store, session, site);
        }
        session.retirement_step(site, 2);
    }
}

impl Plan<'_> {
    pub(super) fn arguments<O: ExecutionObserver>(
        &self,
        interpreter: &Interpreter<'_>,
        values: &mut [InterpretValue],
        state: &mut ExecState,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
        block: BlockId,
    ) -> RunResult<byval::Scope> {
        event(session, site, ExecutionPhase::EntryArguments, 1, 0)?;
        check_values(
            interpreter,
            values,
            &self.signature.params,
            session,
            site,
            block,
        )?;
        // Validate ALL original indirect operands before replacing any carrier
        // or allocating copies. A later malformed source cannot observe an
        // earlier argument as if transport had already modified it.
        for argument in &self.abi.arguments {
            event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
            if matches!(argument.mode, AbiPassMode::Indirect { .. }) {
                if !state.provenance.observed_inert() {
                    return Err(Fault::Unsupported(
                        "observed byval nonempty lineage/shadow state",
                    ));
                }
                let binding = argument.bindings.first().ok_or(Fault::Representation)?;
                let value = values.get(index(binding)).ok_or(Fault::Representation)?;
                let source = expect_pointer(value, block, "typed ABI indirect argument")?;
                byval::validate(
                    &state.memory,
                    source,
                    byval::Layout::new(argument.size, argument.align),
                    session,
                    site,
                    block,
                )?;
            }
        }
        let mut owned = byval::Scope::default();
        let result: RunResult<()> = (|| {
            for argument in &self.abi.arguments {
                event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
                if matches!(argument.mode, AbiPassMode::Indirect { .. }) {
                    let at = index(argument.bindings.first().ok_or(Fault::Representation)?);
                    let source = expect_pointer(
                        values.get(at).ok_or(Fault::Representation)?,
                        block,
                        "typed ABI byval",
                    )?;
                    let copy = owned.copy(
                        &mut state.memory,
                        source,
                        byval::Layout::new(argument.size, argument.align),
                        session,
                        site,
                        block,
                    )?;
                    let original = core::mem::replace(&mut values[at], copy);
                    BindOrigin::OwnedCall.retire_value(original, session, site);
                    if session.first_refusal().is_some() {
                        return Err(Fault::Admission);
                    }
                } else {
                    transport(interpreter, argument, values, state, session, site, block)?;
                }
            }
            event(session, site, ExecutionPhase::AbiScan, 0, 0)
        })();
        match result {
            Ok(()) => Ok(owned),
            Err(error) => {
                owned.retire(&mut state.memory, session, site).ok();
                Err(error)
            }
        }
    }
    pub(super) fn returns<O: ExecutionObserver>(
        &self,
        interpreter: &Interpreter<'_>,
        values: &mut [InterpretValue],
        state: &ExecState,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
        block: BlockId,
    ) -> RunResult<()> {
        check_values(
            interpreter,
            values,
            &self.signature.returns,
            session,
            site,
            block,
        )?;
        transport(
            interpreter,
            &self.abi.result,
            values,
            state,
            session,
            site,
            block,
        )
    }
}

fn check_values<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    values: &[InterpretValue],
    types: &[Ty],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    block: BlockId,
) -> RunResult<()> {
    event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
    if values.len() != types.len() {
        return Err(mismatch(block, "observed ABI actual carrier arity differs"));
    }
    for (value, ty) in values.iter().zip(types) {
        check_value(interpreter, value, ty, session, site, block)?;
    }
    Ok(())
}

pub(super) fn check_value<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    value: &InterpretValue,
    ty: &Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    block: BlockId,
) -> RunResult<()> {
    let (size, _) = memory::shape(interpreter, ty, session, site)?;
    if !flat_type(&value.ty) || value.ty != *ty {
        return Err(mismatch(block, "observed ABI actual carrier type differs"));
    }
    if let InterpretValueKind::PartialBytes(bytes) = &value.kind {
        if !scalar_type(ty) || bytes.len() as u64 != size {
            return Err(Fault::Unsupported("observed ABI partial scalar shape"));
        }
        Ok(())
    } else {
        // Typed logical Char values retain the ordinary dynamic Unicode UB
        // check; physical carrier padding is a separate byte obligation.
        if *ty == Ty::Char {
            check_char_validity(value, block)?;
        }
        let module = interpreter
            .module
            .ok_or(Fault::Unsupported("observed ABI module"))?;
        startup::check_value(module, value, ty, session, site)
    }
}

fn transport<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    argument: &AbiArgument,
    values: &mut [InterpretValue],
    state: &ExecState,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    block: BlockId,
) -> RunResult<()> {
    if matches!(argument.mode, AbiPassMode::Ignore) {
        return event(session, site, ExecutionPhase::AbiScan, 1, 0);
    }
    if matches!(argument.mode, AbiPassMode::Indirect { .. }) {
        return Err(Fault::Unsupported("observed ABI indirect transport"));
    }
    let mut scratch = Scratch::default();
    let result = (|| {
        scratch.source = Some(ByteStore::new_observed(
            argument.size,
            None,
            &mut session.structural_owned(site),
        )?);
        for binding in &argument.bindings {
            event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
            let at = index(binding);
            let value = values
                .get(at)
                .ok_or_else(|| mismatch(block, "observed ABI actual carrier absent"))?;
            let image = memory::encode_at(interpreter, state, value, session, site, block)?;
            let written: RunResult<()> = (|| {
                let live = binding.source_bytes.min(binding.carrier_bytes);
                let slice = image.slice_observed(
                    binding.carrier_offset,
                    live,
                    &mut session.structural_owned(site),
                )?;
                let write = scratch
                    .source
                    .as_mut()
                    .ok_or(Fault::Representation)?
                    .write_observed(
                        binding.source_offset,
                        &slice,
                        &mut session.structural_owned(site),
                    );
                retire_image(slice, session, site);
                write?;
                let mut found = false;
                for (actual, _) in &scratch.carriers {
                    event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
                    found |= *actual == at;
                }
                if !found {
                    reserve(&mut scratch.carriers, 1, session, site)?;
                    let carrier = ByteStore::new_observed(
                        image.len(),
                        None,
                        &mut session.structural_owned(site),
                    )?;
                    scratch.carriers.push((at, carrier));
                }
                Ok(())
            })();
            retire_image(image, session, site);
            written?;
        }
        registers(
            argument,
            scratch.source.as_ref().ok_or(Fault::Representation)?,
            &mut scratch.registers,
            session,
            site,
            block,
        )?;
        scratch.transported = Some(ByteStore::new_observed(
            argument.size,
            None,
            &mut session.structural_owned(site),
        )?);
        for register in &scratch.registers {
            event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
            if let Some(offset) = register.offset {
                let image = register.image.slice_observed(
                    0,
                    register.live,
                    &mut session.structural_owned(site),
                )?;
                let result = scratch
                    .transported
                    .as_mut()
                    .ok_or(Fault::Representation)?
                    .write_observed(offset, &image, &mut session.structural_owned(site));
                retire_image(image, session, site);
                result?;
            }
        }
        for binding in &argument.bindings {
            event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
            let mut single = None;
            for register in &scratch.registers {
                event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
                if register.offset.is_some_and(|offset| {
                    offset <= binding.source_offset
                        && binding.source_offset - offset + binding.source_bytes <= register.live
                }) {
                    single = Some(register);
                    break;
                }
            }
            let image = if let Some(register) = single {
                let offset =
                    binding.source_offset - register.offset.ok_or(Fault::Representation)?;
                let bytes = binding.carrier_bytes.min(register.image.len() - offset);
                let image = register.image.slice_observed(
                    offset,
                    bytes,
                    &mut session.structural_owned(site),
                )?;
                padded(image, binding.carrier_bytes, session, site)?
            } else {
                let bytes = binding.source_bytes.min(binding.carrier_bytes);
                let image = scratch
                    .transported
                    .as_ref()
                    .ok_or(Fault::Representation)?
                    .read_observed(
                        binding.source_offset,
                        bytes,
                        &mut session.structural_owned(site),
                    )?;
                padded(image, binding.carrier_bytes, session, site)?
            };
            let written = (|| {
                for (at, carrier) in &mut scratch.carriers {
                    event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
                    if *at == index(binding) {
                        carrier.write_observed(
                            binding.carrier_offset,
                            &image,
                            &mut session.structural_owned(site),
                        )?;
                        return Ok(());
                    }
                }
                Err(Fault::Representation)
            })();
            retire_image(image, session, site);
            written?;
        }
        for (at, carrier) in &scratch.carriers {
            event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
            let value = values.get(*at).ok_or(Fault::Representation)?;
            let (size, _) = memory::shape(interpreter, &value.ty, session, site)?;
            let mut whole =
                ByteStore::new_observed(size, None, &mut session.structural_owned(site))?;
            let decoded = (|| {
                let image = memory::encode_at(interpreter, state, value, session, site, block)?;
                let written = whole.write_observed(0, &image, &mut session.structural_owned(site));
                retire_image(image, session, site);
                written?;
                for binding in &argument.bindings {
                    event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
                    if index(binding) == *at {
                        let image = carrier.read_observed(
                            binding.carrier_offset,
                            binding.carrier_bytes,
                            &mut session.structural_owned(site),
                        )?;
                        let written = whole.write_observed(
                            binding.carrier_offset,
                            &image,
                            &mut session.structural_owned(site),
                        );
                        retire_image(image, session, site);
                        written?;
                    }
                }
                let image = whole.read_observed(0, size, &mut session.structural_owned(site))?;
                let decoded = (|| {
                    if value.ty == Ty::Bool {
                        let byte = image
                            .get_observed(0, &mut session.structural_owned(site))?
                            .copied()
                            .flatten()
                            .ok_or_else(|| {
                                Fault::Semantic(ub(
                                    block,
                                    "observed ABI Bool value bit is uninitialized",
                                ))
                            });
                        byte.map(|byte| InterpretValue::bool(byte & 1 != 0))
                    } else {
                        memory::decode_at(
                            interpreter,
                            state,
                            &value.ty,
                            &image,
                            false,
                            session,
                            memory::DecodeLocation::new(site, block),
                        )
                    }
                })();
                retire_image(image, session, site);
                decoded
            })();
            retire_store(whole, session, site);
            let decoded = decoded?;
            if let Err(error) = check_char_validity(&decoded, block) {
                decoded.retire_observed(session, site).ok();
                return Err(Fault::Semantic(error));
            }
            let old = core::mem::replace(&mut values[*at], decoded);
            old.retire_observed(session, site).ok();
        }
        event(session, site, ExecutionPhase::AbiScan, 0, 0)
    })();
    scratch.retire(session, site);
    result.and_then(|()| event(session, site, ExecutionPhase::AbiScan, 0, 0))
}

fn padded<O: ExecutionObserver>(
    image: Image,
    len: u64,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<Image> {
    let mut parts = Vec::new();
    let result = (|| {
        reserve(&mut parts, 2, session, site)?;
        let padding = len.checked_sub(image.len()).ok_or(Fault::Representation)?;
        let tail = Image::uniform_observed(None, padding, &mut session.structural_owned(site))?;
        Ok(tail)
    })();
    match result {
        Ok(tail) => {
            parts.push(image);
            parts.push(tail);
            Ok(Image::concat_observed(
                parts,
                &mut session.structural_owned(site),
            )?)
        }
        Err(error) => {
            retire_image(image, session, site);
            Err(error)
        }
    }
}

fn registers<O: ExecutionObserver>(
    argument: &AbiArgument,
    source: &ByteStore,
    output: &mut Vec<RegisterImage>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    block: BlockId,
) -> RunResult<()> {
    match &argument.mode {
        AbiPassMode::Direct(scalar) => push_scalar(scalar, source, output, session, site, block)?,
        AbiPassMode::Pair(a, b) => {
            push_scalar(a, source, output, session, site, block)?;
            push_scalar(b, source, output, session, site, block)?;
        }
        AbiPassMode::Cast {
            pad_i32,
            prefix,
            rest_offset,
            rest,
            attributes,
        } => {
            if *pad_i32 {
                reserve(output, 1, session, site)?;
                let image = Image::uniform_observed(None, 4, &mut session.structural_owned(site))?;
                output.push(RegisterImage {
                    offset: None,
                    live: 0,
                    image,
                });
            }
            let mut offset = 0;
            for register in prefix {
                event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
                push_cast(
                    CastChunk::new(register, offset, register.bytes),
                    source,
                    attributes,
                    output,
                    session,
                    site,
                    block,
                )?;
                offset += register.bytes;
            }
            offset = rest_offset.unwrap_or(offset);
            let mut left = rest.total;
            while left != 0 {
                event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
                let live = left.min(rest.unit.bytes);
                push_cast(
                    CastChunk::new(&rest.unit, offset, live),
                    source,
                    attributes,
                    output,
                    session,
                    site,
                    block,
                )?;
                offset += live;
                left -= live;
            }
        }
        AbiPassMode::Ignore => {}
        AbiPassMode::Indirect { .. } => {
            return Err(Fault::Unsupported("observed ABI indirect registers"));
        }
    }
    Ok(())
}

struct CastChunk<'a> {
    register: &'a AbiRegister,
    offset: u64,
    live: u64,
}

impl<'a> CastChunk<'a> {
    fn new(register: &'a AbiRegister, offset: u64, live: u64) -> Self {
        Self {
            register,
            offset,
            live,
        }
    }
}

fn push_cast<O: ExecutionObserver>(
    chunk: CastChunk<'_>,
    source: &ByteStore,
    attributes: &AbiAttributes,
    output: &mut Vec<RegisterImage>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    block: BlockId,
) -> RunResult<()> {
    let CastChunk {
        register,
        offset,
        live,
    } = chunk;
    reserve(output, 1, session, site)?;
    let image = source.read_observed(offset, live, &mut session.structural_owned(site))?;
    if attributes.no_undef {
        let checked = defined(&image, session, site, block);
        if let Err(error) = checked {
            retire_image(image, session, site);
            return Err(error);
        }
    }
    let image = padded(image, register.bytes, session, site)?;
    output.push(RegisterImage {
        offset: Some(offset),
        live,
        image,
    });
    Ok(())
}
fn push_scalar<O: ExecutionObserver>(
    scalar: &AbiScalar,
    source: &ByteStore,
    output: &mut Vec<RegisterImage>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    block: BlockId,
) -> RunResult<()> {
    reserve(output, 1, session, site)?;
    let image = source.read_observed(
        scalar.source_offset,
        scalar.source_bytes,
        &mut session.structural_owned(site),
    )?;
    let mut bytes = Vec::new();
    let result = (|| {
        defined(&image, session, site, block)?;
        let count = usize::try_from(scalar.register.bytes).map_err(|_| Fault::Representation)?;
        reserve(&mut bytes, count, session, site)?;
        for at in 0..scalar.source_bytes {
            event(
                session,
                site,
                ExecutionPhase::AbiScan,
                1,
                size_of::<Option<u8>>(),
            )?;
            let byte = image
                .get_observed(at, &mut session.structural_owned(site))?
                .copied()
                .ok_or(Fault::Representation)?;
            bytes.push(byte);
        }
        let bits = usize::from(scalar.value_bits);
        let last = (bits - 1) / 8;
        let value = bytes
            .get(last)
            .copied()
            .flatten()
            .ok_or(Fault::Representation)?;
        let mask = u8::MAX >> (7 - (bits - 1) % 8);
        let sign = value & (1 << ((bits - 1) % 8)) != 0;
        let extension = match scalar.attributes.extension {
            AbiExtension::Sign => Some(if sign { 255 } else { 0 }),
            AbiExtension::Zero => Some(0),
            AbiExtension::None => None,
        };
        event(
            session,
            site,
            ExecutionPhase::AbiScan,
            1,
            size_of::<Option<u8>>(),
        )?;
        bytes[last] = Some((value & mask) | (extension.unwrap_or(0) & !mask));
        for byte in bytes.iter_mut().skip(last + 1) {
            event(
                session,
                site,
                ExecutionPhase::AbiScan,
                1,
                size_of::<Option<u8>>(),
            )?;
            *byte = extension;
        }
        while bytes.len() < count {
            event(
                session,
                site,
                ExecutionPhase::AbiScan,
                1,
                size_of::<Option<u8>>(),
            )?;
            bytes.push(extension);
        }
        Ok(())
    })();
    retire_image(image, session, site);
    if let Err(error) = result {
        session.retirement_record(site, bytes.len().saturating_add(1), 0);
        return Err(error);
    }
    let image = Image::dense_observed(bytes, &mut session.structural_owned(site))?;
    output.push(RegisterImage {
        offset: Some(scalar.source_offset),
        live: scalar.source_bytes,
        image,
    });
    Ok(())
}
