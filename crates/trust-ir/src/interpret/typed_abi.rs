// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Operational source/register/carrier transport. The signature parameters
//! are LOWERED IR values; source storage and physical register padding are
//! separate images. This is reference execution, never target ABI evidence.

use super::*;
use crate::signature_abi::{
    AbiArgument, AbiAttributes, AbiBinding, AbiBindingPlace, AbiCapture, AbiExtension, AbiPassMode,
    AbiRegister, AbiScalar, SignatureAbi,
};
#[cfg(test)]
mod tests;

#[derive(Clone, Debug)]
pub(super) struct Access {
    allocation: u64,
    start: u64,
    end: u64,
    readonly: bool,
    no_free: bool,
    no_alias: bool,
}

pub(super) struct Frame {
    arguments: Packet,
    copies: Vec<InterpretPointer>,
    guards: usize,
    lineage: usize,
    hidden: Option<(InterpretPointer, u64, u64)>,
}

fn unsupported(block: BlockId, detail: impl Into<String>) -> InterpretError {
    err(
        InterpretErrorCode::UnsupportedCall,
        block,
        format!("typed ABI: {}", detail.into()),
    )
}

impl Interpreter<'_> {
    /// Whole-module validation precedes memory, instructions and host effects.
    /// Unused and FnPtr-only descriptors have the same denominator as entries.
    pub(super) fn preflight_typed_abi(&self, supplied: &Function) -> InterpretResult<()> {
        let Some(module) = self.module else {
            return Ok(());
        };
        if module
            .func_types
            .iter()
            .all(|signature| signature.abi.is_none())
        {
            return Ok(());
        }
        for signature in &module.func_types {
            let Some(abi) = &signature.abi else {
                continue;
            };
            abi.validate(signature)
                .and_then(|()| abi.validate_target(module.target_info.as_ref()))
                .map_err(|detail| {
                    signature_mismatch(supplied.entry, format!("typed ABI: {detail}"))
                })?;
            if !abi.can_unwind && self.options.panic_strategy == PanicStrategy::Unwind {
                return Err(unsupported(
                    supplied.entry,
                    "typed no-unwind boundary needs an abort-on-crossing model",
                ));
            }
            self.check_abi_plan(abi, signature, supplied.entry)?;
        }
        for function in module.functions.iter().chain(core::iter::once(supplied)) {
            if function.is_declaration() && module.func_type(function.ty).and_then(|signature|signature.abi.as_ref())
                .is_some_and(|abi|matches!(&abi.result.mode,AbiPassMode::Direct(scalar) if scalar.attributes.no_alias)) {
                return Err(unsupported(supplied.entry,"fresh host pointer result needs a declared memory/allocation-producing host contract"));
            }
            function.fn_abi(module).map_err(|detail| {
                signature_mismatch(supplied.entry, format!("typed ABI: {detail}"))
            })?;
            // A host has no interpreter-memory access. An indirect RESULT
            // cannot be served by the existing scalar/handle host contract.
            // Refuse before ANY callback or earlier body effect, even unused.
            if function.is_declaration()
                && module
                    .func_type(function.ty)
                    .and_then(|sig| sig.abi.as_ref())
                    .is_some_and(|abi| matches!(abi.result.mode, AbiPassMode::Indirect { .. }))
            {
                return Err(unsupported(
                    supplied.entry,
                    "indirect host result needs a memory-capable declared host contract",
                ));
            }
        }
        Ok(())
    }

    fn check_abi_plan(
        &self,
        abi: &SignatureAbi,
        signature: &FuncTy,
        block: BlockId,
    ) -> InterpretResult<()> {
        if matches!(abi.result.mode, AbiPassMode::Indirect { .. })
            && !abi
                .result
                .bindings
                .iter()
                .all(|binding| matches!(binding.place, AbiBindingPlace::HiddenResult(_)))
        {
            return Err(unsupported(
                block,
                "indirect result requires explicit hidden-result storage",
            ));
        }
        if scalars(&abi.result)
            .iter()
            .any(|scalar| scalar.attributes.readonly || scalar.attributes.no_free)
        {
            return Err(unsupported(
                block,
                "direct result access attributes need a returned-pointer lifetime contract",
            ));
        }
        let fresh =
            matches!(&abi.result.mode,AbiPassMode::Direct(scalar) if scalar.attributes.no_alias);
        if attributes(&abi.result).iter().any(|attrs| attrs.no_alias)
            && !fresh
            && !matches!(&abi.result.mode, AbiPassMode::Indirect { .. })
        {
            return Err(unsupported(
                block,
                "fresh result requires one exact scalar pointer result, not pair/cast storage",
            ));
        }
        if fresh && (signature.returns != [Ty::Ptr] || abi.result.bindings.len() != 1) {
            return Err(unsupported(
                block,
                "fresh result requires one actual Ptr result carrier",
            ));
        }
        if attributes(&abi.result)
            .iter()
            .any(|attrs| attrs.capture != AbiCapture::Any)
            && !matches!(&abi.result.mode, AbiPassMode::Indirect { .. })
        {
            return Err(unsupported(
                block,
                "capture attributes on returned values have no argument lifetime",
            ));
        }
        for argument in abi.arguments.iter().chain(core::iter::once(&abi.result)) {
            if let AbiPassMode::Indirect { attributes, .. } = &argument.mode
                && attributes.extension != AbiExtension::None
            {
                return Err(unsupported(
                    block,
                    "indirect pointer/stack extension lacks a scalar defined-bit width",
                ));
            }
            if let AbiPassMode::Cast {
                rest, attributes, ..
            } = &argument.mode
            {
                if rest.total.div_ceil(rest.unit.bytes) > 4096 {
                    return Err(unsupported(
                        block,
                        "physical cast register population exceeds reference capacity",
                    ));
                }
                if pointer_attributes(attributes) {
                    return Err(unsupported(
                        block,
                        "pointer contracts on a cast require source pointer-field types",
                    ));
                }
                if attributes.extension != AbiExtension::None {
                    return Err(unsupported(
                        block,
                        "cast extension has no recorded scalar defined-bit width",
                    ));
                }
            }
            for attrs in attributes(argument) {
                if attrs.readonly && attrs.writable {
                    return Err(unsupported(
                        block,
                        "simultaneous readonly/writable pointer contracts are not executable",
                    ));
                }
                if attrs.no_alias
                    && !core::ptr::eq(argument, &abi.result)
                    && matches!(
                        argument.mode,
                        AbiPassMode::Indirect {
                            on_stack: false,
                            caller_copy: false,
                            ..
                        }
                    )
                {
                    return Err(unsupported(
                        block,
                        "borrowed indirect noalias source storage still needs a complete source-object provenance model",
                    ));
                }
            }
            if attributes(argument)
                .iter()
                .any(|attrs| attrs.capture != AbiCapture::Any)
            {
                let pointer = argument.bindings.len() == 1
                    && argument.bindings.iter().all(|binding| {
                        let types = match binding.place {
                            AbiBindingPlace::Parameter(_) | AbiBindingPlace::HiddenResult(_) => {
                                &signature.params
                            }
                            AbiBindingPlace::Result(_) => &signature.returns,
                        };
                        types.get(binding_index(binding)) == Some(&Ty::Ptr)
                            && binding.carrier_offset == 0
                            && binding.carrier_bytes == self.pointer_bytes()
                    });
                if !pointer
                    || matches!(
                        argument.mode,
                        AbiPassMode::Pair(..) | AbiPassMode::Cast { .. }
                    )
                {
                    return Err(unsupported(
                        block,
                        "capture restrictions need one exact actual pointer carrier",
                    ));
                }
            }
            for binding in &argument.bindings {
                let types = match binding.place {
                    AbiBindingPlace::Parameter(_) | AbiBindingPlace::HiddenResult(_) => {
                        &signature.params
                    }
                    AbiBindingPlace::Result(_) => &signature.returns,
                };
                let index = binding_index(binding);
                let ty = types
                    .get(index)
                    .ok_or_else(|| signature_mismatch(block, "typed ABI carrier is absent"))?;
                let size = self.byte_size(ty, block)?;
                if binding
                    .carrier_offset
                    .checked_add(binding.carrier_bytes)
                    .is_none_or(|end| end > size)
                {
                    return Err(signature_mismatch(
                        block,
                        "typed ABI binding exceeds actual module carrier layout",
                    ));
                }
                if let AbiPassMode::Indirect { on_stack, .. } = &argument.mode {
                    let pointer = *ty == Ty::Ptr
                        && binding.carrier_offset == 0
                        && binding.carrier_bytes == self.pointer_bytes();
                    // The carrier's existing type remains its ONLY type. A
                    // complete explicit value carrier can populate an outgoing
                    // byte area without inventing a source pointee type.
                    let stack_value = *on_stack
                        && binding.carrier_offset == 0
                        && binding.carrier_bytes == size
                        && size <= argument.size;
                    if !pointer && !stack_value {
                        return Err(unsupported(
                            block,
                            "indirect stack value needs one complete actual carrier and an explicit source extent",
                        ));
                    }
                }
            }
            for scalar in scalars(argument) {
                let carrier_type = |binding: &AbiBinding| match binding.place {
                    AbiBindingPlace::Parameter(i) | AbiBindingPlace::HiddenResult(i) => {
                        signature.params.get(i as usize)
                    }
                    AbiBindingPlace::Result(i) => signature.returns.get(i as usize),
                };
                let pointer_carrier = argument.bindings.iter().any(|binding| {
                    binding.source_offset <= scalar.source_offset
                        && scalar.source_offset - binding.source_offset < binding.source_bytes
                        && carrier_type(binding).is_some_and(|ty| {
                            matches!(
                                ty,
                                Ty::Ptr
                                    | Ty::Ref(_)
                                    | Ty::RefMut(_)
                                    | Ty::PtrConst(_)
                                    | Ty::PtrMut(_)
                            )
                        })
                });
                if pointer_attributes(&scalar.attributes) || pointer_carrier {
                    let binding = argument.bindings.iter().find(|binding| {
                        binding.source_offset <= scalar.source_offset
                            && scalar.source_offset - binding.source_offset + scalar.source_bytes
                                <= binding.source_bytes
                    });
                    if scalar.source_bytes != self.pointer_bytes() || binding.is_none() {
                        return Err(unsupported(
                            block,
                            "pointer scalar needs a whole pointer-width binding",
                        ));
                    }
                    if (scalar.attributes.readonly
                        || scalar.attributes.no_free
                        || scalar.attributes.no_alias
                        || scalar.attributes.pointee_size != 0)
                        && !binding.is_some_and(|binding| {
                            binding.source_offset == scalar.source_offset
                                && binding.source_bytes == scalar.source_bytes
                        })
                    {
                        return Err(unsupported(
                            block,
                            "pointer access contract needs one exact scalar binding",
                        ));
                    }
                    if scalar.attributes.no_alias
                        || scalar.attributes.readonly
                        || scalar.attributes.no_free
                        || scalar.attributes.pointee_size != 0
                        || scalar.attributes.capture != AbiCapture::Any
                    {
                        let complete = binding.is_some_and(|binding| {
                            binding.carrier_offset == 0
                                && binding.carrier_bytes == self.pointer_bytes()
                                && carrier_type(binding).is_some_and(|ty| {
                                    matches!(
                                        ty,
                                        Ty::Ptr
                                            | Ty::Ref(_)
                                            | Ty::RefMut(_)
                                            | Ty::PtrConst(_)
                                            | Ty::PtrMut(_)
                                            | Ty::Rc(_)
                                    )
                                })
                        });
                        if !complete {
                            return Err(unsupported(
                                block,
                                "constrained scalar needs one complete actual pointer carrier",
                            ));
                        }
                    }
                    if binding
                        .and_then(carrier_type)
                        .is_some_and(|ty| matches!(ty, Ty::Func(_)))
                        && (scalar.attributes.pointee_size != 0
                            || scalar.attributes.readonly
                            || scalar.attributes.no_free
                            || scalar.attributes.writable)
                    {
                        return Err(unsupported(
                            block,
                            "function-code pointee contracts need executable-memory semantics",
                        ));
                    }
                }
                if scalar.attributes.extension == AbiExtension::None && scalar.value_bits % 8 != 0 {
                    let logical_bool = scalar.value_bits == 1
                        && scalar.source_bytes == 1
                        && argument.bindings.iter().any(|binding| {
                            let ty = match binding.place {
                                AbiBindingPlace::Parameter(i)
                                | AbiBindingPlace::HiddenResult(i) => {
                                    signature.params.get(i as usize)
                                }
                                AbiBindingPlace::Result(i) => signature.returns.get(i as usize),
                            };
                            ty == Some(&Ty::Bool)
                                && binding.source_offset == scalar.source_offset
                                && binding.source_bytes == 1
                                && binding.carrier_offset == 0
                                && binding.carrier_bytes == 1
                        });
                    if !logical_bool {
                        return Err(unsupported(
                            block,
                            "partially defined carrier byte needs per-bit poison; only an exact logical Bool hides those bits",
                        ));
                    }
                }
            }
        }
        for (result, types) in [(false, &signature.params), (true, &signature.returns)] {
            for (index, ty) in types.iter().enumerate() {
                let size = self.byte_size(ty, block)?;
                let mut census = ByteStore::new(size, None);
                for argument in abi.arguments.iter().chain(core::iter::once(&abi.result)) {
                    for binding in &argument.bindings {
                        let here = match binding.place {
                            AbiBindingPlace::Parameter(i) | AbiBindingPlace::HiddenResult(i) => {
                                !result && i as usize == index
                            }
                            AbiBindingPlace::Result(i) => result && i as usize == index,
                        };
                        if here {
                            census.write(
                                binding.carrier_offset,
                                &Image::fill(Some(0), binding.carrier_bytes),
                            );
                        }
                    }
                }
                self.check_abi_coverage(ty, &census.read(0, size), block, 0)?;
            }
        }
        Ok(())
    }

    /// Bind every possible live field of the ACTUAL lowered type, while
    /// permitting true layout padding to have no source owner. Enum coverage
    /// includes every inhabited variant, not just a sampled discriminant.
    fn check_abi_coverage(
        &self,
        ty: &Ty,
        image: &Image,
        block: BlockId,
        depth: usize,
    ) -> InterpretResult<()> {
        if depth >= 128 {
            return Err(unsupported(
                block,
                "carrier-layout census exceeds reference depth",
            ));
        }
        match ty {
            Ty::Struct(_) | Ty::Tuple(_) => {
                for (offset, field) in self.aggregate_value_layout(ty, block)?.field_offsets {
                    self.check_abi_coverage(
                        &field,
                        &image.slice(offset, self.byte_size(&field, block)?),
                        block,
                        depth + 1,
                    )?;
                }
            }
            Ty::Enum(_) => {
                let layout = self.enum_layout(ty, block)?;
                let tag = match layout.byte_view {
                    EnumByteView::Direct { tag_offset } => Some((tag_offset, layout.tag_size)),
                    EnumByteView::Niche {
                        niche_offset,
                        niche_size,
                        ..
                    } => Some((niche_offset, niche_size)),
                    EnumByteView::Untagged { .. } => None,
                };
                if tag.is_some_and(|(offset, size)| {
                    image.slice(offset, size).first_uninit().is_some()
                }) {
                    return Err(signature_mismatch(
                        block,
                        "typed ABI omits an enum encoding lane",
                    ));
                }
                for (index, fields) in layout.variant_field_offsets.iter().enumerate() {
                    if layout.uninhabited_variants.get(index) == Some(&true) {
                        continue;
                    }
                    for (offset, field) in fields {
                        self.check_abi_coverage(
                            field,
                            &image.slice(
                                layout.payload_offset + offset,
                                self.byte_size(field, block)?,
                            ),
                            block,
                            depth + 1,
                        )?;
                    }
                }
            }
            Ty::Array(element, _) => {
                let element = self.resolve_ty(*element, block)?;
                let size = self.byte_size(&element, block)?;
                if size != 0 {
                    image.chunk_map::<Option<u8>, InterpretError>(size, &mut |chunk| {
                        self.check_abi_coverage(&element, chunk, block, depth + 1)?;
                        Ok(Some(0))
                    })?;
                }
            }
            Ty::Vector(element, _) => {
                let size = self.byte_size(element, block)?;
                if size != 0 {
                    image.chunk_map::<Option<u8>, InterpretError>(size, &mut |chunk| {
                        self.check_abi_coverage(element, chunk, block, depth + 1)?;
                        Ok(Some(0))
                    })?;
                }
            }
            Ty::Refine(base, _) => {
                self.check_abi_coverage(&self.resolve_ty(*base, block)?, image, block, depth + 1)?
            }
            _ if image.first_uninit().is_some() => {
                return Err(signature_mismatch(
                    block,
                    "typed ABI omits live bytes of an actual lowered carrier",
                ));
            }
            _ => {}
        }
        Ok(())
    }

    /// Public-data entry to this private evaluator. A copied address imports
    /// no live lineage; only actual internal SSA packets preserve that fact.
    pub(super) fn execute_function_boundary(
        &self,
        block: BlockId,
        function: &Function,
        arguments: Vec<InterpretValue>,
        state: &mut ExecState,
        depth: u64,
    ) -> InterpretResult<Vec<InterpretValue>> {
        state.provenance.imported(&arguments, block)?;
        self.execute_packet_boundary(block, function, Packet::plain(arguments), state, depth)
            .map(|packet| packet.values)
    }

    pub(super) fn execute_packet_boundary(
        &self,
        block: BlockId,
        function: &Function,
        arguments: Packet,
        state: &mut ExecState,
        depth: u64,
    ) -> InterpretResult<Packet> {
        arguments.check(block)?;
        self.check_function_args(function, &arguments, block)?;
        let abi = self
            .function_signature(function, block)?
            .and_then(|sig| sig.abi.as_ref());
        let Some(abi) = abi else {
            return if function.is_declaration() {
                self.execute_host_packet(block, function, arguments, state)
            } else {
                self.execute_function_inner(function, arguments, state, depth)
            };
        };
        // Caller reachability belongs to the ORIGINAL operands. A private
        // ABI byval copy is not an existing caller-visible object.
        let fresh = if matches!(&abi.result.mode,AbiPassMode::Direct(scalar) if scalar.attributes.no_alias)
        {
            Some(state.provenance.begin_fresh(&state.memory, &arguments))
        } else {
            None
        };
        let mut frame = match self.prepare_abi(abi, arguments, state, block) {
            Ok(frame) => frame,
            Err(error) => {
                if fresh.is_some() {
                    state.provenance.end_fresh();
                }
                return Err(error);
            }
        };
        let arguments = core::mem::take(&mut frame.arguments);
        let result = if function.is_declaration() {
            let sig = self
                .function_signature(function, block)?
                .expect("typed module signature");
            check_vararg_declaration_args(block, &arguments, &sig.params)
                .and_then(|()| self.execute_host_packet(block, function, arguments, state))
        } else {
            self.execute_function_inner(function, arguments, state, depth)
        };
        let result = result.and_then(|returns| {
            if let Some((pointer, size, align)) = frame.hidden {
                state
                    .memory
                    .read_image(pointer, size, align, block, "typed ABI hidden result")?;
                Ok(returns)
            } else {
                let mut returns = returns;
                if let Some(fresh) = &fresh {
                    state
                        .provenance
                        .fresh_result(fresh, &returns, &state.memory, block)?;
                }
                self.transport_packet(&abi.result, &mut returns, state, block)?;
                self.abi_scalar_attributes(&abi.result, &returns, state, block, &mut Vec::new())?;
                Ok(returns)
            }
        });
        let capture = state.provenance.capture_exit(
            frame.lineage,
            result.as_ref().ok(),
            &state.memory,
            block,
        );
        let result = match capture {
            Ok(()) => result,
            Err(refusal)
                if result.is_ok() && refusal.code == InterpretErrorCode::UndefinedBehavior =>
            {
                Err(refusal)
            }
            Err(refusal) => {
                let abandoned = state.unwind.in_flight.take();
                Err(unsupported(
                    block,
                    format!(
                        "capture exit unavailable; original: {:?}; refusal: {refusal:?}; abandoned in-flight: {abandoned:?}",
                        result.as_ref().err()
                    ),
                ))
            }
        };
        if fresh.is_some() {
            state.provenance.end_fresh();
        }
        state.provenance.close(frame.lineage);
        state.memory.abi_access.truncate(frame.guards);
        let cleanup = retire_copies(state, frame.copies, block);
        if !cleanup.is_empty() {
            return Err(retirement_refusal(
                state,
                block,
                result.as_ref().err(),
                cleanup,
            ));
        }
        result
    }

    fn execute_host_packet(
        &self,
        block: BlockId,
        function: &Function,
        arguments: Packet,
        state: &mut ExecState,
    ) -> InterpretResult<Packet> {
        // The original host dispatcher classifies RC exactly once; its
        // interpreter-owned RC path records this packet's actual argument
        // fact. A public host result still cannot mint a pointer or lineage.
        self.execute_host_call(block, function, arguments, state)
            .map(Packet::plain)
    }

    fn prepare_abi(
        &self,
        abi: &SignatureAbi,
        mut arguments: Packet,
        state: &mut ExecState,
        block: BlockId,
    ) -> InterpretResult<Frame> {
        let guards = state.memory.abi_access.len();
        let lineage = state.provenance.checkpoint();
        let mut copies = Vec::new();
        let mut stack_areas = BTreeMap::new();
        let mut hidden = None;
        let result = (|| {
            // Validate every source operand and alias promise before copying
            // or modifying any passed carrier. Snapshots are persistent images.
            for argument in &abi.arguments {
                if let AbiPassMode::Indirect {
                    attributes,
                    on_stack,
                    caller_copy,
                    ..
                } = &argument.mode
                {
                    if attributes.no_alias && !*on_stack && !*caller_copy {
                        return Err(unsupported(
                            block,
                            "borrowed indirect noalias source storage still needs a complete source-object provenance model",
                        ));
                    }
                    let binding = &argument.bindings[0];
                    let value = &arguments[binding_index(binding)];
                    if value.ty == Ty::Ptr {
                        let pointer = expect_pointer(value, block, "typed ABI indirect argument")?;
                        state.memory.read_image(
                            pointer,
                            argument.size,
                            argument.align,
                            block,
                            "typed ABI indirect argument",
                        )?;
                        self.abi_pointer_attributes(
                            pointer,
                            attributes,
                            argument.size,
                            state,
                            block,
                            &mut Vec::new(),
                        )?;
                    } else if *on_stack {
                        self.abi_image(value, state, block)?;
                    } else {
                        return Err(unsupported(
                            block,
                            "non-pointer indirect argument has no outgoing stack area",
                        ));
                    }
                } else {
                    self.abi_scalar_attributes(
                        argument,
                        &arguments,
                        state,
                        block,
                        &mut Vec::new(),
                    )?;
                }
            }
            if let AbiPassMode::Indirect { attributes, .. } = &abi.result.mode {
                let binding = &abi.result.bindings[0];
                if !matches!(binding.place, AbiBindingPlace::HiddenResult(_)) {
                    return Err(unsupported(
                        block,
                        "indirect result is not an explicit hidden result parameter",
                    ));
                }
                let pointer = expect_pointer(
                    &arguments[binding_index(binding)],
                    block,
                    "typed ABI hidden result",
                )?;
                state.memory.read_image(
                    pointer,
                    abi.result.size,
                    abi.result.align,
                    block,
                    "typed ABI hidden result",
                )?;
                self.abi_pointer_attributes(
                    pointer,
                    attributes,
                    abi.result.size,
                    state,
                    block,
                    &mut Vec::new(),
                )?;
                hidden = Some((pointer, abi.result.size, abi.result.align));
            }
            for (number, argument) in abi.arguments.iter().enumerate() {
                match &argument.mode {
                    AbiPassMode::Indirect {
                        attributes,
                        on_stack,
                        caller_copy,
                        ..
                    } if *on_stack || *caller_copy => {
                        let binding = &argument.bindings[0];
                        let at = binding_index(binding);
                        let is_pointer = arguments[at].ty == Ty::Ptr;
                        let image = if is_pointer {
                            let original =
                                expect_pointer(&arguments[at], block, "typed ABI byval")?;
                            let image = state.memory.read_image(
                                original,
                                argument.size,
                                argument.align,
                                block,
                                "typed ABI byval",
                            )?;
                            state.provenance.bytes(
                                original,
                                argument.size,
                                &arguments.facts[at],
                                false,
                                false,
                                block,
                            )?;
                            image
                        } else {
                            let carrier = self.abi_image(&arguments[at], state, block)?;
                            Image::concat([
                                carrier.clone(),
                                Image::fill(None, argument.size - carrier.len()),
                            ])
                        };
                        let copy = state.memory.alloc(argument.size, argument.align, block)?;
                        copies.push(copy);
                        state.memory.write_image(
                            copy,
                            &image,
                            argument.align,
                            block,
                            "typed ABI byval copy",
                        )?;
                        if is_pointer {
                            let original =
                                expect_pointer(&arguments[at], block, "typed ABI byval shadow")?;
                            state.provenance.copy(copy, original, argument.size);
                        }
                        arguments.facts[at] = provenance::Fact::Independent;
                        if attributes.no_alias {
                            // Protect the fresh identity BEFORE another source
                            // carrier is decoded: a previously dangling raw
                            // address might otherwise alias this new cell.
                            state.memory.abi_access.push(Access {
                                allocation: copy.allocation,
                                start: 0,
                                end: argument.size,
                                readonly: false,
                                no_free: false,
                                no_alias: true,
                            });
                        }
                        if is_pointer {
                            arguments.values[at] = InterpretValue {
                                ty: Ty::Ptr,
                                kind: InterpretValueKind::Ptr(copy),
                            };
                        } else {
                            stack_areas.insert(number, copy);
                            let ty = arguments[at].ty.clone();
                            let bytes = self.byte_size(&ty, block)?;
                            let actual = state.memory.read_image(
                                copy,
                                argument.size,
                                argument.align,
                                block,
                                "typed ABI outgoing stack area",
                            )?;
                            arguments.values[at] =
                                self.abi_value(&ty, actual.slice(0, bytes), state, block)?;
                        }
                    }
                    AbiPassMode::Indirect { .. } | AbiPassMode::Ignore => {}
                    _ => {
                        self.transport_packet(argument, &mut arguments, state, block)?;
                    }
                }
            }
            // Guard the ACTUAL transported pointers (fresh copies included),
            // never the caller's original cell in place of a byval temporary.
            let mut aliases = Vec::new();
            for (number, argument) in abi.arguments.iter().enumerate() {
                if let AbiPassMode::Indirect { attributes, .. } = &argument.mode {
                    let pointer = match stack_areas.get(&number) {
                        Some(pointer) => *pointer,
                        None => expect_pointer(
                            &arguments[binding_index(&argument.bindings[0])],
                            block,
                            "typed ABI transported argument",
                        )?,
                    };
                    self.abi_pointer_attributes(
                        pointer,
                        attributes,
                        argument.size,
                        state,
                        block,
                        &mut aliases,
                    )?;
                } else {
                    self.abi_scalar_attributes(argument, &arguments, state, block, &mut aliases)?;
                }
                self.install_abi_access(
                    argument,
                    &mut arguments,
                    stack_areas.get(&number).copied(),
                    state,
                    block,
                )?;
            }
            if let (Some((pointer, size, _)), AbiPassMode::Indirect { attributes, .. }) =
                (hidden, &abi.result.mode)
            {
                self.abi_pointer_attributes(pointer, attributes, size, state, block, &mut aliases)?;
                let at = binding_index(&abi.result.bindings[0]);
                self.retag_abi_pointer(&mut arguments, at, attributes, state, block)?;
            }
            for (number, argument) in abi.arguments.iter().enumerate() {
                if let AbiPassMode::Indirect { attributes, .. } = &argument.mode
                    && !stack_areas.contains_key(&number)
                {
                    self.record_abi_entry_access(
                        &arguments,
                        binding_index(&argument.bindings[0]),
                        attributes,
                        state,
                        block,
                    )?;
                }
                for scalar in scalars(argument) {
                    if scalar.attributes.pointee_size == 0 {
                        continue;
                    }
                    let binding = argument
                        .bindings
                        .iter()
                        .find(|binding| {
                            binding.source_offset == scalar.source_offset
                                && binding.source_bytes == scalar.source_bytes
                        })
                        .ok_or_else(|| {
                            provenance::unavailable(
                                block,
                                "implied access lacks one exact pointer carrier",
                            )
                        })?;
                    self.record_abi_entry_access(
                        &arguments,
                        binding_index(binding),
                        &scalar.attributes,
                        state,
                        block,
                    )?;
                }
            }
            if let AbiPassMode::Indirect { attributes, .. } = &abi.result.mode {
                self.record_abi_entry_access(
                    &arguments,
                    binding_index(&abi.result.bindings[0]),
                    attributes,
                    state,
                    block,
                )?;
            }
            Ok(())
        })();
        if let Err(error) = result {
            state.provenance.close(lineage);
            state.memory.abi_access.truncate(guards);
            let cleanup = retire_copies(state, copies, block);
            if !cleanup.is_empty() {
                return Err(retirement_refusal(state, block, Some(&error), cleanup));
            }
            return Err(error);
        }
        Ok(Frame {
            arguments,
            copies,
            guards,
            lineage,
            hidden,
        })
    }

    fn transport_packet(
        &self,
        argument: &AbiArgument,
        packet: &mut Packet,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<()> {
        for binding in &argument.bindings {
            let at = binding_index(binding);
            if !packet.facts[at].independent() {
                let bytes = self.byte_size(&packet.values[at].ty, block)?;
                let whole = argument
                    .bindings
                    .iter()
                    .filter(|other| binding_index(other) == at)
                    .count()
                    == 1
                    && binding.carrier_offset == 0
                    && binding.carrier_bytes == bytes
                    && binding.source_bytes == bytes
                    && bytes == self.pointer_bytes();
                let exact = scalars(argument).iter().any(|scalar| {
                    scalar.source_offset == binding.source_offset
                        && scalar.source_bytes == bytes
                        && u64::from(scalar.value_bits) == bytes * 8
                });
                if !matches!(argument.mode, AbiPassMode::Indirect { .. }) && (!whole || !exact) {
                    return Err(provenance::unavailable(
                        block,
                        "partial carrier transport cannot recreate based-on lineage",
                    ));
                }
            }
        }
        self.transport_values(argument, &mut packet.values, &packet.facts, state, block)
    }

    fn transport_values(
        &self,
        argument: &AbiArgument,
        values: &mut [InterpretValue],
        facts: &[provenance::Fact],
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<()> {
        if matches!(
            argument.mode,
            AbiPassMode::Ignore | AbiPassMode::Indirect { .. }
        ) {
            return Ok(());
        }
        let mut source = ByteStore::new(argument.size, None);
        let mut carriers = BTreeMap::new();
        for binding in &argument.bindings {
            let index = binding_index(binding);
            let value = values
                .get(index)
                .ok_or_else(|| signature_mismatch(block, "typed ABI missing lowered value"))?;
            let image = self.abi_image(value, state, block)?;
            let live = binding.source_bytes.min(binding.carrier_bytes);
            source.write(
                binding.source_offset,
                &image.slice(binding.carrier_offset, live),
            );
            carriers
                .entry(index)
                .or_insert_with(|| ByteStore::new(image.len(), None));
        }
        let registers = transport(argument, &source, block)?;
        let mut transported = ByteStore::new(argument.size, None);
        for register in &registers {
            if let Some(offset) = register.source_offset {
                transported.write(offset, &register.image.slice(0, register.live));
            }
        }
        for binding in &argument.bindings {
            let single = registers.iter().find(|lane| {
                lane.source_offset.is_some_and(|offset| {
                    offset <= binding.source_offset
                        && binding.source_offset - offset + binding.source_bytes <= lane.live
                })
            });
            let image = if let Some(register) = single {
                let offset =
                    binding.source_offset - register.source_offset.expect("source register");
                let bytes = binding.carrier_bytes.min(register.image.len() - offset);
                Image::concat([
                    register.image.slice(offset, bytes),
                    Image::fill(None, binding.carrier_bytes - bytes),
                ])
            } else {
                let bytes = binding.source_bytes.min(binding.carrier_bytes);
                Image::concat([
                    transported.read(binding.source_offset, bytes),
                    Image::fill(None, binding.carrier_bytes - bytes),
                ])
            };
            carriers
                .get_mut(&binding_index(binding))
                .expect("collected carrier")
                .write(binding.carrier_offset, &image);
        }
        for (index, carrier) in carriers {
            // A carrier can also belong to ANOTHER source argument. Replace
            // exactly this argument's bindings, retaining all other bytes.
            let mut whole = ByteStore::new(self.byte_size(&values[index].ty, block)?, None);
            whole.write(0, &self.abi_image(&values[index], state, block)?);
            for binding in argument
                .bindings
                .iter()
                .filter(|binding| binding_index(binding) == index)
            {
                whole.write(
                    binding.carrier_offset,
                    &carrier.read(binding.carrier_offset, binding.carrier_bytes),
                );
            }
            let image = whole.read(0, self.byte_size(&values[index].ty, block)?);
            values[index] = if values[index].ty == Ty::Bool {
                // The existing Bool IR type observes one logical bit. This is
                // projection from its actual physical extension, not permission
                // to initialize partial-byte padding in an integer carrier.
                let byte = image
                    .get(0)
                    .copied()
                    .flatten()
                    .ok_or_else(|| ub(block, "typed ABI Bool value bit is uninitialized"))?;
                InterpretValue::bool(byte & 1 != 0)
            } else {
                let pointer = match &values[index].kind {
                    InterpretValueKind::Ptr(pointer) => Some(*pointer),
                    _ => None,
                };
                self.with_pointer_decode(state, &facts[index], pointer, || {
                    self.abi_value(&values[index].ty, image, state, block)
                })?
            };
        }
        Ok(())
    }

    fn abi_image(
        &self,
        value: &InterpretValue,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<Image> {
        let image = match &value.kind {
            InterpretValueKind::PartialBytes(bytes)
                if bytes.len() as u64 == self.byte_size(&value.ty, block)? =>
            {
                Ok(Image::literal(bytes.clone()))
            }
            InterpretValueKind::PartialBytes(_) => Err(type_error(
                block,
                "typed ABI partial carrier has the wrong byte count",
            )),
            InterpretValueKind::Int(int)
                if int_shape(&value.ty) != Some((int.bits, int.signed))
                    || int.raw & !int_mask(int.bits).unwrap_or(0) != 0 =>
            {
                Err(type_error(
                    block,
                    "typed ABI integer carrier shape mismatch",
                ))
            }
            InterpretValueKind::Bool(_) if value.ty != Ty::Bool => Err(type_error(
                block,
                "typed ABI boolean carrier shape mismatch",
            )),
            InterpretValueKind::FloatBits(bits)
                if !matches!(value.ty, Ty::F16 | Ty::F32 | Ty::F64)
                    || (value.ty == Ty::F16 && *bits > u64::from(u16::MAX))
                    || (value.ty == Ty::F32 && *bits > u64::from(u32::MAX)) =>
            {
                Err(type_error(block, "typed ABI float carrier shape mismatch"))
            }
            InterpretValueKind::Ptr(_)
            | InterpretValueKind::NullPtr
            | InterpretValueKind::DanglingPtr(_)
                if !matches!(
                    value.ty,
                    Ty::Ptr
                        | Ty::Func(_)
                        | Ty::Ref(_)
                        | Ty::RefMut(_)
                        | Ty::PtrConst(_)
                        | Ty::PtrMut(_)
                        | Ty::Rc(_)
                ) =>
            {
                Err(type_error(
                    block,
                    "typed ABI pointer carrier shape mismatch",
                ))
            }
            InterpretValueKind::Unit if value.ty != Ty::Unit => {
                Err(type_error(block, "typed ABI unit carrier shape mismatch"))
            }
            _ => self.encode_image(value, state, block),
        }?;
        if image.len() != self.byte_size(&value.ty, block)? {
            return Err(type_error(
                block,
                "typed ABI carrier byte count differs from declared layout",
            ));
        }
        check_char_validity(value, block)?;
        Ok(image)
    }

    fn abi_value(
        &self,
        ty: &Ty,
        image: Image,
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        if image.first_uninit().is_some() && partial_load_ty(ty) {
            return Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::PartialBytes(image.to_vec()),
            });
        }
        if self
            .first_uninit_covered(ty, &image, state, block)?
            .is_some()
        {
            return Err(ub(
                block,
                "typed ABI has uninitialized live aggregate carrier bytes",
            ));
        }
        self.decode_image(ty, &image, state, block)
    }

    fn abi_scalar_attributes(
        &self,
        argument: &AbiArgument,
        values: &Packet,
        state: &ExecState,
        block: BlockId,
        aliases: &mut Vec<(InterpretPointer, u64, bool)>,
    ) -> InterpretResult<()> {
        for scalar in scalars(argument) {
            let attrs = &scalar.attributes;
            let pointer_carrier = argument.bindings.iter().any(|binding| {
                binding.source_offset <= scalar.source_offset
                    && scalar.source_offset - binding.source_offset < binding.source_bytes
                    && matches!(
                        values[binding_index(binding)].ty,
                        Ty::Ptr | Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_)
                    )
            });
            if !pointer_attributes(attrs) && !pointer_carrier {
                continue;
            }
            let binding = argument
                .bindings
                .iter()
                .find(|binding| {
                    binding.source_offset <= scalar.source_offset
                        && scalar.source_offset - binding.source_offset + scalar.source_bytes
                            <= binding.source_bytes
                })
                .ok_or_else(|| {
                    unsupported(block, "pointer scalar straddles multiple carrier bindings")
                })?;
            if scalar.source_bytes != self.pointer_bytes() {
                return Err(unsupported(
                    block,
                    "pointer attributes on a non-pointer-width scalar",
                ));
            }
            let image = self.abi_image(&values[binding_index(binding)], state, block)?;
            let image = image.slice(
                binding.carrier_offset + scalar.source_offset - binding.source_offset,
                scalar.source_bytes,
            );
            if image.first_uninit().is_some() {
                return Err(ub(block, "typed ABI pointer is not initialized"));
            }
            let at = binding_index(binding);
            let pointer = match &values[at].kind {
                InterpretValueKind::Ptr(pointer) => Some(*pointer),
                _ => None,
            };
            let value = self.with_pointer_decode(state, &values.facts[at], pointer, || {
                self.decode_image(&Ty::Ptr, &image, state, block)
            })?;
            if matches!(value.kind, InterpretValueKind::NullPtr) {
                if attrs.nonnull || attrs.pointee_size != 0 {
                    return Err(ub(
                        block,
                        "typed ABI null pointer contradicts its nonnull/dereferenceable record",
                    ));
                }
                continue;
            }
            if let InterpretValueKind::DanglingPtr(address) = &value.kind {
                if attrs.pointee_size != 0 {
                    return Err(ub(
                        block,
                        "typed ABI dereferenceable pointer has no live allocation",
                    ));
                }
                if attrs
                    .pointee_align
                    .is_some_and(|align| *address % align != 0)
                {
                    return Err(ub(block, "typed ABI pointer alignment is not satisfied"));
                }
                if !attrs.no_alias && !attrs.readonly && !attrs.no_free && !attrs.writable {
                    continue;
                }
                return Err(unsupported(
                    block,
                    "address-only pointer access contracts need based-on provenance",
                ));
            }
            let pointer = expect_pointer(&value, block, "typed ABI pointer attributes")?;
            self.abi_pointer_attributes(pointer, attrs, attrs.pointee_size, state, block, aliases)?;
        }
        Ok(())
    }

    fn abi_pointer_attributes(
        &self,
        pointer: InterpretPointer,
        attrs: &AbiAttributes,
        extent: u64,
        state: &ExecState,
        block: BlockId,
        aliases: &mut Vec<(InterpretPointer, u64, bool)>,
    ) -> InterpretResult<()> {
        let extent = extent.max(attrs.pointee_size);
        if extent == 0 && !attrs.no_alias && !attrs.readonly && !attrs.no_free && !attrs.writable {
            let address = state
                .memory
                .address(pointer, block, "typed ABI inert pointer")?;
            if attrs
                .pointee_align
                .is_some_and(|align| address % align != 0)
            {
                return Err(ub(block, "typed ABI pointer alignment is not satisfied"));
            }
            return Ok(());
        }
        state.memory.checked_access(
            pointer,
            extent,
            attrs.pointee_align.unwrap_or(1),
            block,
            "typed ABI pointee",
        )?;
        aliases.push((pointer, extent, attrs.no_alias));
        Ok(())
    }

    pub(super) fn resolve_abi_pointer(
        &self,
        state: &ExecState,
        address: u64,
        block: BlockId,
    ) -> InterpretResult<InterpretValueKind> {
        let value = state.memory.resolve_pointer_kind(address);
        if let InterpretValueKind::Ptr(pointer) = &value {
            state.provenance.check_decode(*pointer, block)?;
            if state
                .memory
                .allocations
                .get(&pointer.allocation)
                .is_some_and(|cell| cell.alive)
                && state
                    .memory
                    .abi_access
                    .iter()
                    .any(|guard| guard.no_alias && guard.allocation == pointer.allocation)
            {
                return Err(unsupported(
                    block,
                    "raw-address alias of an active noalias copy needs based-on provenance",
                ));
            }
        }
        Ok(value)
    }

    fn retag_abi_pointer(
        &self,
        arguments: &mut Packet,
        at: usize,
        attrs: &AbiAttributes,
        state: &mut ExecState,
        block: BlockId,
    ) -> InterpretResult<()> {
        let pointer = match &arguments[at].kind {
            InterpretValueKind::Ptr(pointer) => Some(*pointer),
            _ => None,
        };
        state.provenance.parameter(
            &mut arguments.facts[at],
            pointer,
            state.memory.next_alloc_id,
            attrs,
            block,
        )
    }

    fn record_abi_entry_access(
        &self,
        arguments: &Packet,
        at: usize,
        attrs: &AbiAttributes,
        state: &mut ExecState,
        block: BlockId,
    ) -> InterpretResult<()> {
        // Every argument scope is installed BEFORE any entry event. Otherwise
        // an early writable argument could evade a later noalias parameter.
        // Dereferenceable promises accessibility, not initialized bytes.
        if attrs.pointee_size != 0 {
            let pointer = expect_pointer(&arguments[at], block, "typed ABI implied read")?;
            state.provenance.bytes(
                pointer,
                attrs.pointee_size,
                &arguments.facts[at],
                false,
                false,
                block,
            )?;
            if attrs.writable {
                state.provenance.bytes(
                    pointer,
                    attrs.pointee_size,
                    &arguments.facts[at],
                    true,
                    false,
                    block,
                )?;
            }
        }
        Ok(())
    }

    fn install_abi_access(
        &self,
        argument: &AbiArgument,
        arguments: &mut Packet,
        stack_area: Option<InterpretPointer>,
        state: &mut ExecState,
        block: BlockId,
    ) -> InterpretResult<()> {
        if let AbiPassMode::Indirect { attributes, .. } = &argument.mode {
            if let Some(pointer) = stack_area {
                // A logical on-stack value has no IR pointer SSA lane to retag.
                // Its inaccessible temporary retains conservative safeguards.
                let access = allocation_access(state, pointer, attributes, block)?;
                state.memory.abi_access.push(access);
            } else {
                let at = binding_index(&argument.bindings[0]);
                self.retag_abi_pointer(arguments, at, attributes, state, block)?;
            }
        }
        for scalar in scalars(argument) {
            let attrs = &scalar.attributes;
            if !attrs.readonly
                && !attrs.no_free
                && !attrs.no_alias
                && attrs.pointee_size == 0
                && attrs.capture == AbiCapture::Any
            {
                continue;
            }
            let binding = argument
                .bindings
                .iter()
                .find(|binding| {
                    binding.source_offset == scalar.source_offset
                        && binding.source_bytes == scalar.source_bytes
                        && binding.carrier_offset == 0
                        && binding.carrier_bytes == self.pointer_bytes()
                })
                .ok_or_else(|| {
                    provenance::unavailable(
                        block,
                        "constrained scalar requires one whole pointer carrier",
                    )
                })?;
            let at = binding_index(binding);
            if !matches!(
                arguments[at].ty,
                Ty::Ptr | Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Rc(_)
            ) {
                return Err(provenance::unavailable(
                    block,
                    "constrained scalar lacks an actual pointer carrier",
                ));
            }
            self.retag_abi_pointer(arguments, at, attrs, state, block)?;
        }
        Ok(())
    }
}

fn allocation_access(
    state: &ExecState,
    pointer: InterpretPointer,
    attributes: &AbiAttributes,
    block: BlockId,
) -> InterpretResult<Access> {
    let allocation = state
        .memory
        .allocations
        .get(&pointer.allocation)
        .ok_or_else(|| unsupported(block, "ABI access pointer allocation disappeared"))?;
    // Conservatively cover the WHOLE allocation, including bytes before a
    // nonzero input offset. A denied access is Unavailable, never invented UB.
    Ok(Access {
        allocation: pointer.allocation,
        start: 0,
        end: allocation.size,
        readonly: attributes.readonly,
        no_free: attributes.no_free,
        no_alias: attributes.no_alias,
    })
}

fn retire_copies(
    state: &mut ExecState,
    copies: Vec<InterpretPointer>,
    block: BlockId,
) -> Vec<InterpretError> {
    let mut failures = Vec::new();
    for pointer in copies.into_iter().rev() {
        match state.memory.allocations.get(&pointer.allocation) {
            None => failures.push(unsupported(
                block,
                "tracked ABI copy allocation disappeared",
            )),
            Some(allocation) if !allocation.alive => {}
            Some(_) => {
                if let Err(error) = state.memory.dealloc(pointer, block) {
                    failures.push(error);
                }
            }
        }
    }
    failures
}
fn retirement_refusal(
    state: &mut ExecState,
    block: BlockId,
    original: Option<&InterpretError>,
    cleanup: Vec<InterpretError>,
) -> InterpretError {
    // catch_unwinding consults the actual in-flight exception, not the error
    // code. A model-incapable retirement MUST NOT become a catchable body panic.
    // Keep the original complete error/Panic and retirement refusals in the
    // returned diagnostic; keep ordinary live-borrow/dealloc checks intact.
    let abandoned = state.unwind.in_flight.take();
    unsupported(
        block,
        format!(
            "copy retirement unavailable; original body exit: {original:?}; retirement refusals: {cleanup:?}; abandoned in-flight exception: {abandoned:?}"
        ),
    )
}

fn binding_index(binding: &AbiBinding) -> usize {
    match binding.place {
        AbiBindingPlace::Parameter(i)
        | AbiBindingPlace::Result(i)
        | AbiBindingPlace::HiddenResult(i) => i as usize,
    }
}
fn pointer_attributes(attrs: &AbiAttributes) -> bool {
    attrs.nonnull
        || attrs.no_alias
        || attrs.readonly
        || attrs.writable
        || attrs.no_free
        || attrs.pointee_size != 0
        || attrs.pointee_align.is_some()
}
fn scalars(argument: &AbiArgument) -> Vec<&AbiScalar> {
    match &argument.mode {
        AbiPassMode::Direct(a) => vec![a],
        AbiPassMode::Pair(a, b) => vec![a, b],
        _ => vec![],
    }
}
fn attributes(argument: &AbiArgument) -> Vec<&AbiAttributes> {
    match &argument.mode {
        AbiPassMode::Direct(a) => vec![&a.attributes],
        AbiPassMode::Pair(a, b) => vec![&a.attributes, &b.attributes],
        AbiPassMode::Cast { attributes, .. } => vec![attributes],
        AbiPassMode::Indirect {
            attributes,
            metadata_attributes,
            ..
        } => core::iter::once(attributes)
            .chain(metadata_attributes.iter())
            .collect(),
        AbiPassMode::Ignore => vec![],
    }
}
struct RegisterImage {
    source_offset: Option<u64>,
    live: u64,
    image: Image,
}

fn transport(
    argument: &AbiArgument,
    source: &ByteStore,
    block: BlockId,
) -> InterpretResult<Vec<RegisterImage>> {
    let mut registers = Vec::new();
    match &argument.mode {
        AbiPassMode::Direct(a) => registers.push(scalar_register(a, source, block)?),
        AbiPassMode::Pair(a, b) => {
            registers.push(scalar_register(a, source, block)?);
            registers.push(scalar_register(b, source, block)?);
        }
        AbiPassMode::Cast {
            pad_i32,
            prefix,
            rest_offset,
            rest,
            attributes,
        } => {
            // pad_i32 is an extra physical alignment register, with NO source
            // binding. Retaining its undefined image prevents source ownership.
            if *pad_i32 {
                registers.push(RegisterImage {
                    source_offset: None,
                    live: 0,
                    image: Image::fill(None, 4),
                });
            }
            let mut offset = 0;
            for register in prefix {
                registers.push(cast_register(
                    register,
                    offset,
                    register.bytes,
                    source,
                    attributes,
                    block,
                )?);
                offset += register.bytes;
            }
            offset = rest_offset.unwrap_or(offset);
            let mut left = rest.total;
            while left != 0 {
                let live = left.min(rest.unit.bytes);
                registers.push(cast_register(
                    &rest.unit, offset, live, source, attributes, block,
                )?);
                offset += live;
                left -= live;
            }
        }
        AbiPassMode::Ignore | AbiPassMode::Indirect { .. } => {}
    }
    Ok(registers)
}

fn scalar_register(
    scalar: &AbiScalar,
    source: &ByteStore,
    block: BlockId,
) -> InterpretResult<RegisterImage> {
    let live = source.read(scalar.source_offset, scalar.source_bytes);
    if live.first_uninit().is_some() {
        return Err(ub(block, "typed ABI scalar has uninitialized value bits"));
    }
    let mut bytes = live.to_vec();
    let bit_count = usize::from(scalar.value_bits);
    let final_index = (bit_count - 1) / 8;
    let final_mask = u8::MAX >> (7 - (bit_count - 1) % 8);
    let final_byte = bytes[final_index].expect("initialized scalar");
    let sign = final_byte & (1 << ((bit_count - 1) % 8)) != 0;
    let extension = match scalar.attributes.extension {
        AbiExtension::Sign => Some(if sign { 255 } else { 0 }),
        AbiExtension::Zero => Some(0),
        AbiExtension::None => None,
    };
    bytes[final_index] = Some((final_byte & final_mask) | (extension.unwrap_or(0) & !final_mask));
    for byte in bytes.iter_mut().skip(final_index + 1) {
        *byte = extension;
    }
    bytes.resize(scalar.register.bytes as usize, extension);
    Ok(RegisterImage {
        source_offset: Some(scalar.source_offset),
        live: scalar.source_bytes,
        image: Image::literal(bytes),
    })
}
fn cast_register(
    register: &AbiRegister,
    offset: u64,
    live: u64,
    source: &ByteStore,
    attributes: &AbiAttributes,
    block: BlockId,
) -> InterpretResult<RegisterImage> {
    let image = source.read(offset, live);
    if attributes.no_undef && image.first_uninit().is_some() {
        return Err(ub(
            block,
            "typed ABI noundef cast has uninitialized live bytes",
        ));
    }
    Ok(RegisterImage {
        source_offset: Some(offset),
        live,
        image: Image::concat([image, Image::fill(None, register.bytes - live)]),
    })
}

pub(super) fn check_write(
    access: &[Access],
    pointer: InterpretPointer,
    bytes: u64,
    block: BlockId,
) -> InterpretResult<()> {
    if bytes == 0 {
        return Ok(());
    }
    if access.iter().any(|guard| {
        guard.readonly
            && guard.allocation == pointer.allocation
            && pointer.offset < guard.end
            && guard.start < pointer.offset.saturating_add(bytes)
    }) {
        Err(unsupported(
            block,
            "a write overlaps readonly ABI storage; based-on access provenance is not modeled",
        ))
    } else {
        Ok(())
    }
}
pub(super) fn check_free(
    access: &[Access],
    pointer: InterpretPointer,
    block: BlockId,
) -> InterpretResult<()> {
    if access
        .iter()
        .any(|guard| (guard.no_free || guard.readonly) && guard.allocation == pointer.allocation)
    {
        Err(unsupported(
            block,
            "free overlaps nofree/readonly ABI storage; based-on access provenance is not modeled",
        ))
    } else {
        Ok(())
    }
}
pub(super) fn check_rc_write(
    access: &[Access],
    pointer: InterpretPointer,
    block: BlockId,
) -> InterpretResult<()> {
    if access
        .iter()
        .any(|guard| guard.readonly && guard.allocation == pointer.allocation)
    {
        Err(unsupported(
            block,
            "reference-count mutation overlaps readonly ABI storage; based-on provenance is not modeled",
        ))
    } else {
        Ok(())
    }
}

pub(super) fn check_carrier_types(
    block: BlockId,
    label: &str,
    values: &[InterpretValue],
    types: &[Ty],
) -> InterpretResult<()> {
    if values.len() != types.len() {
        return Err(signature_mismatch(block, format!("{label} arity mismatch")));
    }
    for (value, ty) in values.iter().zip(types) {
        expect_ty(value, ty, block)?;
    }
    Ok(())
}
