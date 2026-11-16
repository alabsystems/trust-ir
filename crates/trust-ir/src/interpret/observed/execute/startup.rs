// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn prepare<'m, O: ExecutionObserver>(
    interpreter: &Interpreter<'m>,
    id: FuncId,
    arguments: &[InterpretValue],
    session: &mut ObservedSession<'_, O>,
) -> RunResult<(&'m Function, Option<typed_abi::Plan<'m>>)> {
    let site = ExecutionSite::Entry(id);
    event(session, site, ExecutionPhase::ModuleLookup, 1, 0)?;
    if interpreter.options != session.options
        || session.options.panic_strategy != PanicStrategy::Abort
    {
        return Err(Fault::Unsupported("observed options or unwind mode"));
    }
    if session.options.max_call_depth == 0 {
        return Err(Fault::Semantic(InterpretError::new(
            InterpretErrorCode::OutOfFuel,
            "observed call depth exhausted before entry",
        )));
    }
    if interpreter.host.is_some() {
        return Err(Fault::Unsupported("host-assisted observed execution"));
    }
    let module = interpreter.module.ok_or_else(|| {
        Fault::Semantic(InterpretError::new(
            InterpretErrorCode::MissingFunction,
            "observed execution requires a module",
        ))
    })?;
    let mut found = None;
    if let Some(function) = module.functions.get(id.as_usize()).filter(|f| f.id == id) {
        found = Some(function);
    } else {
        for function in &module.functions {
            event(session, site, ExecutionPhase::ModuleLookup, 1, 0)?;
            if function.id == id {
                found = Some(function);
                break;
            }
        }
    }
    let function = found.ok_or_else(|| {
        Fault::Semantic(InterpretError::new(
            InterpretErrorCode::MissingFunction,
            "observed entry function is absent",
        ))
    })?;
    let mut recorded = false;
    for signature in &module.func_types {
        event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
        recorded |= signature.abi.is_some();
    }
    if recorded {
        typed_abi::preflight(interpreter, function, session, site)?;
    }
    check_layout(module, session, site)?;
    // The observed capability has no Drop/DropInvoke dispatcher. Its startup
    // still visits the actual table and every inline type node under the
    // owner, without invoking the legacy unobserved clone/hash constructor.
    for row in &module.drop_glue {
        event(session, site, ExecutionPhase::DropGlueIndex, 1, 0)?;
        walk_type(&row.ty, session, site, ExecutionPhase::DropGlueIndex)?;
    }
    let signature = module
        .func_types
        .get(function.ty.as_usize())
        .ok_or_else(|| {
            Fault::Semantic(err(
                InterpretErrorCode::SignatureMismatch,
                function.entry,
                "observed entry signature is absent",
            ))
        })?;
    if signature.is_vararg || signature.params.len() != arguments.len() {
        return Err(Fault::Semantic(err(
            InterpretErrorCode::SignatureMismatch,
            function.entry,
            "observed entry argument count or vararg signature mismatch",
        )));
    }
    for (argument, ty) in arguments.iter().zip(&signature.params) {
        event(session, site, ExecutionPhase::EntryArguments, 1, 0)?;
        if signature.abi.is_some() {
            typed_abi::check_value(interpreter, argument, ty, session, site, function.entry)?;
        } else {
            check_value(module, argument, ty, session, site)?;
        }
    }
    if function.is_declaration() {
        return Err(Fault::Unsupported("bodyless observed entry"));
    }
    if signature.abi.is_some() {
        event(
            session,
            site,
            ExecutionPhase::AbiScan,
            1,
            size_of::<typed_abi::Plan<'_>>(),
        )?;
    }
    Ok((function, typed_abi::plan(signature)))
}

fn check_layout<O: ExecutionObserver>(
    module: &Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<()> {
    event(session, site, ExecutionPhase::Layout, 1, 0)?;
    let Some(target) = &module.target_info else {
        return Ok(());
    };
    // Only the target triple's architecture participates in this decision.
    // Observe each actual examined byte, rather than an uninterruptible split.
    let mut end = 0;
    for byte in target.triple.bytes() {
        event(session, site, ExecutionPhase::Layout, 1, 0)?;
        if byte == b'-' {
            break;
        }
        end += 1;
    }
    let arch = &target.triple[..end];
    let canonical = matches!(arch, "x86_64" | "x64" | "aarch64" | "arm64" | "wasm64")
        || arch.starts_with("riscv64");
    if target.pointer_size != 8 || target.endianness != crate::Endianness::Little || !canonical {
        return Err(Fault::Unsupported("noncanonical observed target layout"));
    }
    Ok(())
}

fn walk_type<O: ExecutionObserver>(
    ty: &Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    phase: ExecutionPhase,
) -> RunResult<()> {
    let mut stack = Vec::new();
    reserve(&mut stack, 1, session, site)?;
    stack.push(ty);
    while let Some(ty) = stack.pop() {
        event(session, site, phase, 1, 0)?;
        match ty {
            Ty::Vector(inner, _)
            | Ty::Tensor(inner, _)
            | Ty::Ref(inner)
            | Ty::RefMut(inner)
            | Ty::PtrConst(inner)
            | Ty::PtrMut(inner)
            | Ty::Rc(inner) => {
                reserve(&mut stack, 1, session, site)?;
                stack.push(inner);
            }
            Ty::Tuple(fields) => {
                for field in fields {
                    event(session, site, phase, 1, 0)?;
                    reserve(&mut stack, 1, session, site)?;
                    stack.push(field);
                }
            }
            Ty::Handle(handle) => {
                for _ in handle.name.bytes().chain(handle.runtime.bytes()) {
                    event(session, site, phase, 1, 0)?;
                }
            }
            Ty::Dialect(dialect) => {
                for _ in dialect.namespace.bytes().chain(dialect.name.bytes()) {
                    event(session, site, phase, 1, 0)?;
                }
            }
            _ => {}
        }
    }
    session.retirement_poll(site);
    Ok(())
}

pub(super) fn check_type<O: ExecutionObserver>(
    module: &Module,
    ty: &Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<()> {
    event(session, site, ExecutionPhase::Layout, 1, 0)?;
    if let Ty::Array(element, _) = ty {
        event(session, site, ExecutionPhase::Layout, 1, 0)?;
        if !matches!(module.types.get(element.as_usize()), Some(Ty::U8)) {
            return Err(Fault::Unsupported(
                "observed array element is not exactly U8",
            ));
        }
    } else if let Ty::Func(signature) = ty {
        // This is a module-local code value, never a heap pointer or closure.
        event(session, site, ExecutionPhase::Layout, 1, 0)?;
        if module.func_types.get(signature.as_usize()).is_none() {
            return Err(Fault::Unsupported(
                "observed function-value signature is absent",
            ));
        }
    } else if !scalar_type(ty) {
        return Err(Fault::Unsupported("observed scalar/flat-U8 type closure"));
    }
    Ok(())
}

pub(super) fn check_value<O: ExecutionObserver>(
    module: &Module,
    value: &InterpretValue,
    ty: &Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<()> {
    check_type(module, ty, session, site)?;
    if !flat_type(&value.ty) || value.ty != *ty {
        return Err(Fault::Unsupported("entry type/value representation"));
    }
    let valid = match (&value.kind, ty) {
        (InterpretValueKind::Int(int), _) if int_shape(ty).is_some() => {
            let (bits, signed) = int_shape(ty).ok_or(Fault::Unsupported("integer type"))?;
            int.bits == bits
                && int.signed == signed
                && int_mask(bits).is_some_and(|mask| int.raw & !mask == 0)
                && (*ty != Ty::Char || valid_char(int.raw))
        }
        (InterpretValueKind::FnDef(_) | InterpretValueKind::NullPtr, Ty::Func(_)) => true,
        (InterpretValueKind::Bool(_), Ty::Bool)
        | (InterpretValueKind::Unit, Ty::Unit)
        | (
            InterpretValueKind::Ptr(_)
            | InterpretValueKind::NullPtr
            | InterpretValueKind::DanglingPtr(_),
            Ty::Ptr,
        ) => true,
        (InterpretValueKind::FloatBits(bits), Ty::F16) => *bits <= u16::MAX as u64,
        (InterpretValueKind::FloatBits(bits), Ty::F32) => *bits <= u32::MAX as u64,
        (InterpretValueKind::FloatBits(_), Ty::F64) => true,
        (InterpretValueKind::Array(array), Ty::Array(_, len)) if array.len() == *len => {
            array.rope().try_for_each_stored_observed(
                &mut session.structural(site),
                |element, progress| {
                    progress.admit(ExecutionPhase::EntryArguments, 1, 0)?;
                    if element.ty != Ty::U8
                        || !matches!(element.kind, InterpretValueKind::Int(int)
                    if int.bits == 8 && !int.signed && int.raw <= 255)
                    {
                        return Err(ObservedValueError::UnsupportedValue);
                    }
                    Ok(())
                },
            )?;
            true
        }
        _ => false,
    };
    if !valid {
        return Err(Fault::Unsupported("entry value kind or scalar shape"));
    }
    Ok(())
}

fn valid_char(raw: u128) -> bool {
    raw <= 0x10ffff && !(0xd800..=0xdfff).contains(&raw)
}

struct EntryArguments<'a> {
    values: &'a mut Vec<InterpretValue>,
    origin: BindOrigin,
}

impl<'a> EntryArguments<'a> {
    fn new(values: &'a mut Vec<InterpretValue>, origin: BindOrigin) -> Self {
        Self { values, origin }
    }
}

pub(super) fn bind_entry<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    function: &Function,
    block: &Block,
    abi: Option<&typed_abi::Plan<'_>>,
    arguments: &mut Vec<InterpretValue>,
    state: &mut ExecState,
    session: &mut ObservedSession<'_, O>,
) -> RunResult<()> {
    bind_entry_core(
        interpreter,
        function,
        block,
        abi,
        EntryArguments::new(arguments, BindOrigin::Existing),
        state,
        session,
    )
}

pub(super) fn bind_call_entry<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    function: &Function,
    block: &Block,
    abi: Option<&typed_abi::Plan<'_>>,
    arguments: &mut Vec<InterpretValue>,
    state: &mut ExecState,
    session: &mut ObservedSession<'_, O>,
) -> RunResult<()> {
    bind_entry_core(
        interpreter,
        function,
        block,
        abi,
        EntryArguments::new(arguments, BindOrigin::OwnedCall),
        state,
        session,
    )
}

fn bind_entry_core<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    function: &Function,
    block: &Block,
    abi: Option<&typed_abi::Plan<'_>>,
    supplied: EntryArguments<'_>,
    state: &mut ExecState,
    session: &mut ObservedSession<'_, O>,
) -> RunResult<()> {
    let EntryArguments { values, origin } = supplied;
    let site = ExecutionSite::Entry(function.id);
    let module = interpreter
        .module
        .ok_or(Fault::Unsupported("entry module"))?;
    if values.len() != block.params.len() {
        return Err(Fault::Semantic(err(
            InterpretErrorCode::SignatureMismatch,
            block.id,
            "entry block argument count mismatch",
        )));
    }
    for ((_, ty), value) in block.params.iter().zip(values.iter()) {
        event(session, site, ExecutionPhase::BlockParameters, 1, 0)?;
        if abi.is_some() {
            typed_abi::check_value(interpreter, value, ty, session, site, function.entry)?;
        } else {
            check_value(module, value, ty, session, site)?;
        }
    }
    // Validation happened before moves. Each insertion has its own debit;
    // a refusal leaves the remaining arguments in the original cleanup path.
    let mut supplied = core::mem::take(values).into_iter();
    for (id, _) in &block.params {
        let Some(value) = supplied.next() else {
            break;
        };
        if let Err(error) = map_insert::<ValueId, InterpretValue, O>(
            state.values.len(),
            session,
            site,
            ExecutionPhase::BlockParameters,
        ) {
            origin.retire_value(value, session, site);
            for remaining in supplied {
                origin.retire_value(remaining, session, site);
            }
            return Err(error);
        }
        if let Some(old) = state.values.insert(*id, value) {
            origin.retire_value(old, session, site);
        }
    }
    Ok(())
}

pub(super) fn check_returns<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    function: &Function,
    abi: Option<&typed_abi::Plan<'_>>,
    values: &[InterpretValue],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<()> {
    let module = interpreter
        .module
        .ok_or(Fault::Unsupported("return module"))?;
    let signature = module
        .func_types
        .get(function.ty.as_usize())
        .ok_or(Fault::Unsupported("return signature"))?;
    if signature.returns.len() != values.len() {
        return Err(Fault::Semantic(err(
            InterpretErrorCode::SignatureMismatch,
            function.entry,
            "return count mismatch",
        )));
    }
    for (value, ty) in values.iter().zip(&signature.returns) {
        event(session, site, ExecutionPhase::BlockParameters, 1, 0)?;
        if abi.is_some() {
            typed_abi::check_value(interpreter, value, ty, session, site, function.entry)?;
        } else {
            check_value(module, value, ty, session, site)?;
        }
    }
    Ok(())
}

/// Real selected callee data, after the root's complete immutable-module
/// preflight. No new session, memory arena, whole-module receipt or budget is
/// created. Preparation failures are sited at the actual caller instruction.
pub(super) fn prepare_call<'m, O: ExecutionObserver>(
    interpreter: &Interpreter<'m>,
    id: FuncId,
    arguments: &[InterpretValue],
    session: &mut ObservedSession<'_, O>,
    caller: InstructionSite,
) -> RunResult<(&'m Function, Option<typed_abi::Plan<'m>>)> {
    let site = ExecutionSite::Instruction(caller);
    event(session, site, ExecutionPhase::ModuleLookup, 1, 0)?;
    let module = interpreter
        .module
        .ok_or(Fault::Unsupported("observed direct call module"))?;
    let mut found = module
        .functions
        .get(id.as_usize())
        .filter(|function| function.id == id);
    if found.is_none() {
        for function in &module.functions {
            event(session, site, ExecutionPhase::ModuleLookup, 1, 0)?;
            if function.id == id {
                found = Some(function);
                break;
            }
        }
    }
    let function = found.ok_or_else(|| {
        Fault::Semantic(err(
            InterpretErrorCode::MissingFunction,
            caller.block,
            "observed direct callee is absent",
        ))
    })?;
    let signature = module
        .func_types
        .get(function.ty.as_usize())
        .ok_or_else(|| {
            Fault::Semantic(signature_mismatch(
                caller.block,
                "observed direct callee signature is absent",
            ))
        })?;
    if signature.is_vararg {
        return Err(Fault::Unsupported("observed direct variadic call"));
    }
    if signature.params.len() != arguments.len() {
        return Err(Fault::Semantic(signature_mismatch(
            caller.block,
            "observed direct argument count differs",
        )));
    }
    for (argument, ty) in arguments.iter().zip(&signature.params) {
        event(session, site, ExecutionPhase::EntryArguments, 1, 0)?;
        if signature.abi.is_some() {
            typed_abi::check_value(interpreter, argument, ty, session, site, caller.block)?;
        } else {
            check_value(module, argument, ty, session, site)?;
        }
    }
    if function.is_declaration() {
        return Err(Fault::Unsupported("observed direct host declaration"));
    }
    if function.blocks.len() != 1 || function.blocks[0].id != function.entry {
        return Err(Fault::Unsupported("multi-block observed direct callee"));
    }
    event(
        session,
        site,
        ExecutionPhase::AbiScan,
        1,
        size_of::<Option<typed_abi::Plan<'_>>>(),
    )?;
    Ok((function, typed_abi::plan(signature)))
}

/// Resolve one actual function-pointer call after its pointer and arguments
/// were evaluated in caller order. This reads the immutable original module,
/// compares all real signature/ABI bytes under the same owner, and then uses
/// the existing selected callee preparation. Closures/hosts remain unavailable.
pub(super) struct IndirectCall {
    signature: FuncTyId,
    convention: crate::CallingConv,
    depth: usize,
    caller: InstructionSite,
}

impl IndirectCall {
    pub(super) fn new(
        signature: FuncTyId,
        convention: crate::CallingConv,
        depth: usize,
        caller: InstructionSite,
    ) -> Self {
        Self {
            signature,
            convention,
            depth,
            caller,
        }
    }
}

pub(super) fn prepare_indirect<'m, O: ExecutionObserver>(
    interpreter: &Interpreter<'m>,
    pointer: &InterpretValue,
    arguments: &[InterpretValue],
    session: &mut ObservedSession<'_, O>,
    call: IndirectCall,
) -> RunResult<(&'m Function, Option<typed_abi::Plan<'m>>)> {
    let IndirectCall {
        signature,
        convention,
        depth,
        caller,
    } = call;
    let site = ExecutionSite::Instruction(caller);
    event(session, site, ExecutionPhase::Validation, 3, 0)?;
    let value_sig = match &pointer.ty {
        Ty::Func(sig) => *sig,
        Ty::Closure(_) => return Err(Fault::Unsupported("observed indirect closure application")),
        _ => {
            return Err(Fault::Semantic(invalid_function_pointer(
                caller.block,
                "observed indirect callee has non-function type",
            )));
        }
    };
    if value_sig != signature {
        return Err(Fault::Semantic(signature_mismatch(
            caller.block,
            "observed function-value signature differs from call",
        )));
    }
    let target = match &pointer.kind {
        InterpretValueKind::FnDef(target) => *target,
        InterpretValueKind::NullPtr => {
            return Err(Fault::Semantic(invalid_function_pointer(
                caller.block,
                "observed null function pointer",
            )));
        }
        _ => {
            return Err(Fault::Semantic(invalid_function_pointer(
                caller.block,
                "observed callee is not a function pointer",
            )));
        }
    };
    event(session, site, ExecutionPhase::EntryArguments, 1, 0)?;
    if u64::try_from(depth).map_err(|_| Fault::Representation)? >= session.options.max_call_depth {
        return Err(Fault::Semantic(err(
            InterpretErrorCode::OutOfFuel,
            caller.block,
            "interpreter call depth exhausted",
        )));
    }
    let module = interpreter
        .module
        .ok_or(Fault::Unsupported("observed indirect call module"))?;
    event(session, site, ExecutionPhase::ModuleLookup, 1, 0)?;
    let expected = module.func_types.get(signature.as_usize()).ok_or_else(|| {
        Fault::Semantic(signature_mismatch(
            caller.block,
            "observed indirect signature is absent",
        ))
    })?;
    event(session, site, ExecutionPhase::ModuleLookup, 1, 0)?;
    let mut found = module
        .functions
        .get(target.as_usize())
        .filter(|function| function.id == target);
    if found.is_none() {
        for function in &module.functions {
            event(session, site, ExecutionPhase::ModuleLookup, 1, 0)?;
            if function.id == target {
                found = Some(function);
                break;
            }
        }
    }
    let function = found.ok_or_else(|| {
        Fault::Semantic(invalid_function_pointer(
            caller.block,
            "observed function pointer target is absent",
        ))
    })?;
    event(session, site, ExecutionPhase::ModuleLookup, 1, 0)?;
    let actual = module
        .func_types
        .get(function.ty.as_usize())
        .ok_or_else(|| {
            Fault::Semantic(signature_mismatch(
                caller.block,
                "observed indirect target signature is absent",
            ))
        })?;
    if !expected.structural_eq_observed(actual, session, site)? {
        return Err(Fault::Semantic(signature_mismatch(
            caller.block,
            "observed indirect target signature or ABI differs",
        )));
    }
    event(session, site, ExecutionPhase::AbiScan, 1, 0)?;
    if convention != function.calling_conv {
        return Err(Fault::Semantic(signature_mismatch(
            caller.block,
            "observed indirect calling convention differs",
        )));
    }
    prepare_call(interpreter, target, arguments, session, caller)
}
