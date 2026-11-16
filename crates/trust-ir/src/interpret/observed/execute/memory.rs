// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The observed scalar / flat-U8 memory closure. All byte-store and rope
//! operations use the original session, including copies of initializedness.

use super::*;

#[derive(Clone, Copy)]
enum ImageOrigin {
    Memory,
    OwnedBoundary,
}
impl ImageOrigin {
    fn progress<'s, 'o, O: ExecutionObserver>(
        self,
        session: &'s mut ObservedSession<'o, O>,
        site: ExecutionSite,
    ) -> SessionProgress<'s, 'o, O> {
        match self {
            Self::Memory => session.structural(site),
            Self::OwnedBoundary => session.structural_owned(site),
        }
    }
    fn retire_bytes<O: ExecutionObserver>(
        self,
        bytes: Vec<Option<u8>>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        if matches!(self, Self::OwnedBoundary) {
            for _ in &bytes {
                session.retirement_step(site, 1);
            }
            session.retirement_step(site, 1);
        }
        drop(bytes);
    }
}

impl From<BindOrigin> for ImageOrigin {
    fn from(origin: BindOrigin) -> Self {
        match origin {
            BindOrigin::Existing => Self::Memory,
            BindOrigin::OwnedCall => Self::OwnedBoundary,
        }
    }
}

#[derive(Clone, Copy)]
struct Access {
    ptr: InterpretPointer,
    size: u64,
    align: u64,
    site: InstructionSite,
    op: &'static str,
}

impl Access {
    fn new(
        ptr: InterpretPointer,
        size: u64,
        align: u64,
        site: InstructionSite,
        op: &'static str,
    ) -> Self {
        Self {
            ptr,
            size,
            align,
            site,
            op,
        }
    }
}

#[derive(Clone, Copy)]
struct DecodeMode {
    origin: ImageOrigin,
    strict: bool,
}

impl DecodeMode {
    fn new(origin: ImageOrigin, strict: bool) -> Self {
        Self { origin, strict }
    }
}

#[derive(Clone, Copy)]
pub(super) struct DecodeLocation {
    at: ExecutionSite,
    block: BlockId,
}

impl DecodeLocation {
    pub(super) fn new(at: ExecutionSite, block: BlockId) -> Self {
        Self { at, block }
    }
}

pub(super) fn shape<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    ty: &Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<(u64, u64)> {
    let module = interpreter
        .module
        .ok_or(Fault::Unsupported("memory module"))?;
    startup::check_type(module, ty, session, site)?;
    Ok(match ty {
        Ty::Bool | Ty::I8 | Ty::U8 => (1, 1),
        Ty::I16 | Ty::U16 | Ty::F16 => (2, 2),
        Ty::I32 | Ty::U32 | Ty::F32 | Ty::Char => (4, 4),
        Ty::I64 | Ty::U64 | Ty::F64 | Ty::Ptr | Ty::Func(_) | Ty::Isize | Ty::Usize => (8, 8),
        Ty::I128 | Ty::U128 => (16, 16),
        Ty::Unit => (0, 1),
        Ty::Array(_, len) => (*len, 1),
        _ => return Err(Fault::Unsupported("observed memory shape")),
    })
}

pub(super) fn allocate<O: ExecutionObserver>(
    execution_origin: BindOrigin,
    memory: &mut MemoryState,
    size: u64,
    align: u64,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<InterpretValue> {
    let origin = ImageOrigin::from(execution_origin);
    let at = ExecutionSite::Instruction(site);
    let exhausted = || {
        Fault::Semantic(err(
            InterpretErrorCode::OutOfMemory,
            site.block,
            "observed allocation exhausts target address space",
        ))
    };
    let base = align_addr(memory.next_addr, align).ok_or_else(exhausted)?;
    let next = base.checked_add(size.max(1)).ok_or_else(exhausted)?;
    let id = memory.next_alloc_id;
    let next_id = id.checked_add(1).ok_or_else(exhausted)?;
    map_insert::<u64, Allocation, O>(
        memory.allocations.len(),
        session,
        at,
        ExecutionPhase::HostAllocation,
    )?;
    let bytes = ByteStore::new_observed(size, None, &mut origin.progress(session, at))?;
    memory.allocations.insert(
        id,
        Allocation {
            base,
            size,
            alive: true,
            bytes,
            ref_count: 1,
            origin: None,
            requested: size,
            live_borrows: 0,
        },
    );
    memory.next_alloc_id = next_id;
    memory.next_addr = next;
    Ok(InterpretValue {
        ty: Ty::Ptr,
        kind: InterpretValueKind::Ptr(InterpretPointer {
            allocation: id,
            offset: 0,
        }),
    })
}

fn access<'a, O: ExecutionObserver>(
    memory: &'a MemoryState,
    access: Access,
    session: &mut ObservedSession<'_, O>,
) -> RunResult<&'a Allocation> {
    let Access {
        ptr,
        size,
        align,
        site,
        op,
    } = access;
    event(
        session,
        ExecutionSite::Instruction(site),
        ExecutionPhase::SparseRun,
        map_work(memory.allocations.len())?,
        0,
    )?;
    Ok(memory.checked_access(ptr, size, align, site.block, op)?)
}

fn read<O: ExecutionObserver>(
    origin: ImageOrigin,
    memory: &MemoryState,
    access: Access,
    session: &mut ObservedSession<'_, O>,
) -> RunResult<Image> {
    let allocation = self::access(memory, access, session)?;
    Ok(allocation.bytes.read_observed(
        access.ptr.offset,
        access.size,
        &mut origin.progress(session, ExecutionSite::Instruction(access.site)),
    )?)
}

fn write<O: ExecutionObserver>(
    origin: ImageOrigin,
    memory: &mut MemoryState,
    access: Access,
    image: &Image,
    session: &mut ObservedSession<'_, O>,
) -> RunResult<()> {
    debug_assert_eq!(access.size, image.len());
    self::access(memory, access, session)?;
    // No accepted observed instruction can create aggregate unwritten-lane
    // metadata. Never silently invoke the ordinary unobserved range walk.
    if !memory.unwritten_lane_bytes.is_empty() {
        return Err(Fault::Unsupported("aggregate unwritten-lane metadata"));
    }
    event(
        session,
        ExecutionSite::Instruction(access.site),
        ExecutionPhase::SparseRun,
        map_work(memory.allocations.len())?,
        0,
    )?;
    let allocation = memory
        .allocations
        .get_mut(&access.ptr.allocation)
        .ok_or_else(|| Fault::Semantic(ub(access.site.block, "observed write lost allocation")))?;
    allocation.bytes.write_observed(
        access.ptr.offset,
        image,
        &mut origin.progress(session, ExecutionSite::Instruction(access.site)),
    )?;
    Ok(())
}

pub(super) struct CopyRequest<'a> {
    dst: &'a InterpretValue,
    src: &'a InterpretValue,
    count: u64,
    overlap: bool,
}

impl<'a> CopyRequest<'a> {
    pub(super) fn new(
        dst: &'a InterpretValue,
        src: &'a InterpretValue,
        count: u64,
        overlap: bool,
    ) -> Self {
        Self {
            dst,
            src,
            count,
            overlap,
        }
    }
}

pub(super) fn copy<O: ExecutionObserver>(
    execution_origin: BindOrigin,
    memory: &mut MemoryState,
    request: CopyRequest<'_>,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<()> {
    let CopyRequest {
        dst,
        src,
        count,
        overlap,
    } = request;
    let origin = ImageOrigin::from(execution_origin);
    // Exact zero-byte semantics: no pointer dereference or range validation.
    if count == 0 {
        return Ok(());
    }
    let dst = expect_pointer(dst, site.block, "MemCopy destination")?;
    let src = expect_pointer(src, site.block, "MemCopy source")?;
    access(
        memory,
        Access::new(src, count, 1, site, "MemCopy source"),
        session,
    )?;
    access(
        memory,
        Access::new(dst, count, 1, site, "MemCopy destination"),
        session,
    )?;
    if !overlap
        && src.allocation == dst.allocation
        && src.offset < dst.offset.saturating_add(count)
        && dst.offset < src.offset.saturating_add(count)
    {
        return Err(Fault::Semantic(ub(
            site.block,
            "MemCopy: overlapping ranges require memmove",
        )));
    }
    // Snapshot the ENTIRE source before any write. Compressed images retain
    // both byte values and initializedness; length is not a host loop bound.
    let image = read(
        origin,
        memory,
        Access::new(src, count, 1, site, "MemCopy source"),
        session,
    )?;
    let result = write(
        origin,
        memory,
        Access::new(dst, count, 1, site, "MemCopy destination"),
        &image,
        session,
    );
    image.retire_observed(&mut origin.progress(session, ExecutionSite::Instruction(site)));
    result
}

pub(super) fn fill<O: ExecutionObserver>(
    execution_origin: BindOrigin,
    memory: &mut MemoryState,
    dst: &InterpretValue,
    byte: u8,
    count: u64,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<()> {
    let origin = ImageOrigin::from(execution_origin);
    if count == 0 {
        return Ok(());
    }
    let ptr = expect_pointer(dst, site.block, "MemSet")?;
    let access = Access::new(ptr, count, 1, site, "MemSet");
    self::access(memory, access, session)?;
    let at = ExecutionSite::Instruction(site);
    let image = Image::uniform_observed(Some(byte), count, &mut origin.progress(session, at))?;
    let result = write(origin, memory, access, &image, session);
    image.retire_observed(&mut origin.progress(session, at));
    result
}

#[allow(
    clippy::too_many_arguments,
    reason = "the observed twin keeps the unobserved signature and adds the session"
)]
pub(super) fn store<O: ExecutionObserver>(
    execution_origin: BindOrigin,
    interpreter: &Interpreter<'_>,
    state: &mut ExecState,
    ty: &Ty,
    ptr: &InterpretValue,
    value: &InterpretValue,
    align: Option<u64>,
    strict: bool,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<()> {
    let origin = ImageOrigin::from(execution_origin);
    let (_, natural) = shape(interpreter, ty, session, ExecutionSite::Instruction(site))?;
    if strict {
        reject_partial(value, site.block, "Store (atomic/volatile)")?;
    }
    if value.ty != *ty {
        return Err(Fault::Semantic(type_error(
            site.block,
            "observed Store type mismatch",
        )));
    }
    let align = checked_align(align.unwrap_or(natural), site.block)?;
    let ptr = expect_pointer(ptr, site.block, "Store")?;
    let image = encode(origin, interpreter, state, value, session, site)?;
    let result = write(
        origin,
        &mut state.memory,
        Access::new(ptr, image.len(), align, site, "Store"),
        &image,
        session,
    );
    image.retire_observed(&mut origin.progress(session, ExecutionSite::Instruction(site)));
    result
}

#[allow(
    clippy::too_many_arguments,
    reason = "the observed twin keeps the unobserved signature and adds the session"
)]
pub(super) fn load<O: ExecutionObserver>(
    execution_origin: BindOrigin,
    interpreter: &Interpreter<'_>,
    state: &ExecState,
    ty: &Ty,
    ptr: &InterpretValue,
    align: Option<u64>,
    strict: bool,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<InterpretValue> {
    let origin = ImageOrigin::from(execution_origin);
    let at = ExecutionSite::Instruction(site);
    let (size, natural) = shape(interpreter, ty, session, at)?;
    let ptr = expect_pointer(ptr, site.block, "Load")?;
    let align = checked_align(align.unwrap_or(natural), site.block)?;
    let image = read(
        origin,
        &state.memory,
        Access::new(ptr, size, align, site, "Load"),
        session,
    )?;
    let result = decode(
        DecodeMode::new(origin, strict),
        interpreter,
        state,
        ty,
        &image,
        session,
        site,
    );
    image.retire_observed(&mut origin.progress(session, at));
    result
}

fn encode<O: ExecutionObserver>(
    origin: ImageOrigin,
    interpreter: &Interpreter<'_>,
    state: &ExecState,
    value: &InterpretValue,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<Image> {
    encode_core(
        interpreter,
        state,
        value,
        session,
        ExecutionSite::Instruction(site),
        site.block,
        origin,
    )
}

/// The same paid image construction at an entry or call boundary. The caller
/// retains its actual source execution site, never a fabricated instruction.
pub(super) fn encode_at<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    state: &ExecState,
    value: &InterpretValue,
    session: &mut ObservedSession<'_, O>,
    at: ExecutionSite,
    block: BlockId,
) -> RunResult<Image> {
    encode_core(
        interpreter,
        state,
        value,
        session,
        at,
        block,
        ImageOrigin::OwnedBoundary,
    )
}

fn encode_core<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    state: &ExecState,
    value: &InterpretValue,
    session: &mut ObservedSession<'_, O>,
    at: ExecutionSite,
    block: BlockId,
    origin: ImageOrigin,
) -> RunResult<Image> {
    let (size, _) = shape(interpreter, &value.ty, session, at)?;
    if let InterpretValueKind::Array(array) = &value.kind {
        if !matches!(value.ty, Ty::Array(_, len) if len == array.len()) {
            return Err(Fault::Unsupported("array Store shape"));
        }
        return Ok(array.rope().try_map_observed(
            &mut origin.progress(session, at),
            |element, progress| {
                progress.admit(ExecutionPhase::LiteralElement, 1, 1)?;
                match (&element.ty, &element.kind) {
                    (Ty::U8, InterpretValueKind::Int(int))
                        if int.bits == 8 && !int.signed && int.raw <= 255 =>
                    {
                        Ok(Some(int.raw as u8))
                    }
                    _ => Err(ObservedValueError::UnsupportedValue),
                }
            },
        )?);
    }
    if size > 16 {
        return Err(Fault::Unsupported("scalar image width"));
    }
    let mut bytes = Vec::new();
    reserve(&mut bytes, size as usize, session, at)?;
    let encoded: RunResult<()> = (|| {
        if let InterpretValueKind::PartialBytes(partial) = &value.kind {
            if partial.len() as u64 != size {
                return Err(Fault::Unsupported("partial scalar image shape"));
            }
            for byte in partial {
                event(session, at, ExecutionPhase::LiteralElement, 1, 1)?;
                bytes.push(*byte);
            }
        } else {
            let raw = match value.kind {
                InterpretValueKind::Int(int) => int.raw,
                InterpretValueKind::FloatBits(bits) => u128::from(bits),
                InterpretValueKind::Bool(bit) => u128::from(bit),
                InterpretValueKind::Ptr(ptr) => {
                    event(
                        session,
                        at,
                        ExecutionPhase::SparseRun,
                        map_work(state.memory.allocations.len())?,
                        0,
                    )?;
                    u128::from(state.memory.address(ptr, block, "Store")?)
                }
                InterpretValueKind::FnDef(target) if matches!(value.ty, Ty::Func(_)) => {
                    u128::from(function_address(interpreter, target, session, at, block)?)
                }
                InterpretValueKind::NullPtr | InterpretValueKind::Unit => 0,
                InterpretValueKind::DanglingPtr(address) => u128::from(address),
                _ => return Err(Fault::Unsupported("scalar Store payload")),
            };
            for index in 0..size as usize {
                event(session, at, ExecutionPhase::LiteralElement, 1, 1)?;
                bytes.push(Some((raw >> (8 * index)) as u8));
            }
        }
        Ok(())
    })();
    if let Err(error) = encoded {
        origin.retire_bytes(bytes, session, at);
        return Err(error);
    }
    Ok(Image::dense_observed(
        bytes,
        &mut origin.progress(session, at),
    )?)
}

fn decode<O: ExecutionObserver>(
    mode: DecodeMode,
    _interpreter: &Interpreter<'_>,
    state: &ExecState,
    ty: &Ty,
    image: &Image,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<InterpretValue> {
    decode_core(
        _interpreter,
        state,
        ty,
        image,
        session,
        mode,
        DecodeLocation::new(ExecutionSite::Instruction(site), site.block),
    )
}

/// The paid image decoder shared by actual memory and ABI boundaries. This
/// grants no permission to use an unobserved layout, clone or memory helper.
pub(super) fn decode_at<O: ExecutionObserver>(
    _interpreter: &Interpreter<'_>,
    state: &ExecState,
    ty: &Ty,
    image: &Image,
    strict: bool,
    session: &mut ObservedSession<'_, O>,
    location: DecodeLocation,
) -> RunResult<InterpretValue> {
    decode_core(
        _interpreter,
        state,
        ty,
        image,
        session,
        DecodeMode::new(ImageOrigin::OwnedBoundary, strict),
        location,
    )
}

fn decode_core<O: ExecutionObserver>(
    _interpreter: &Interpreter<'_>,
    state: &ExecState,
    ty: &Ty,
    image: &Image,
    session: &mut ObservedSession<'_, O>,
    mode: DecodeMode,
    location: DecodeLocation,
) -> RunResult<InterpretValue> {
    let DecodeMode { origin, strict } = mode;
    let DecodeLocation { at, block } = location;
    if matches!(ty, Ty::Array(_, _)) {
        let mut uninit = false;
        image.try_for_each_stored_observed(&mut origin.progress(session, at), |byte, _| {
            uninit |= byte.is_none();
            Ok(())
        })?;
        if uninit {
            return Err(Fault::Semantic(ub(block, "Load: uninitialized array byte")));
        }
        let values =
            image.try_map_observed(&mut origin.progress(session, at), |byte, progress| {
                progress.admit(
                    ExecutionPhase::LiteralElement,
                    1,
                    size_of::<InterpretValue>(),
                )?;
                let byte = byte.ok_or(ObservedValueError::UnsupportedValue)?;
                Ok(InterpretValue {
                    ty: Ty::U8,
                    kind: InterpretValueKind::Int(InterpretInt {
                        bits: 8,
                        signed: false,
                        raw: u128::from(byte),
                    }),
                })
            })?;
        return Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Array(ArrayValue::from_rope(values)),
        });
    }
    let size = image.len();
    if size > 16 {
        return Err(Fault::Unsupported("scalar Load width"));
    }
    let mut bytes = Vec::new();
    reserve(&mut bytes, size as usize, session, at)?;
    let mut raw = 0u128;
    let mut uninit = false;
    let decoded: RunResult<()> = (|| {
        for index in 0..size {
            let byte = image
                .get_observed(index, &mut origin.progress(session, at))?
                .copied()
                .ok_or(Fault::Representation)?;
            event(session, at, ExecutionPhase::LiteralElement, 1, 1)?;
            bytes.push(byte);
            uninit |= byte.is_none();
            raw |= u128::from(byte.unwrap_or(0)) << (8 * index);
        }
        Ok(())
    })();
    if let Err(error) = decoded {
        origin.retire_bytes(bytes, session, at);
        return Err(error);
    }
    if uninit {
        if strict || matches!(ty, Ty::Func(_)) {
            origin.retire_bytes(bytes, session, at);
            return Err(Fault::Semantic(ub(
                block,
                "Load: uninitialized strict scalar byte",
            )));
        }
        return Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::PartialBytes(bytes),
        });
    }
    origin.retire_bytes(bytes, session, at);
    let kind = if let Some((bits, signed)) = int_shape(ty) {
        InterpretValueKind::Int(
            InterpretInt::from_raw(bits, signed, raw).ok_or(Fault::Representation)?,
        )
    } else {
        match ty {
            Ty::Bool => InterpretValueKind::Bool(raw != 0),
            Ty::Unit => InterpretValueKind::Unit,
            Ty::F16 | Ty::F32 | Ty::F64 => InterpretValueKind::FloatBits(raw as u64),
            Ty::Ptr => resolve_pointer(&state.memory, raw as u64, session, at)?,
            Ty::Func(_) => function_from_address(_interpreter, raw as u64, session, at, block)?,
            _ => return Err(Fault::Unsupported("scalar Load type")),
        }
    };
    Ok(InterpretValue {
        ty: ty.clone(),
        kind,
    })
}

fn resolve_pointer<O: ExecutionObserver>(
    memory: &MemoryState,
    address: u64,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<InterpretValueKind> {
    if address == 0 {
        return Ok(InterpretValueKind::NullPtr);
    }
    // Preserve ordinary provenance's in-bounds-before-one-past preference.
    for one_past in [false, true] {
        for (id, allocation) in &memory.allocations {
            event(session, site, ExecutionPhase::SparseRun, 1, 0)?;
            let Some(end) = allocation.base.checked_add(allocation.size) else {
                continue;
            };
            if (!one_past && address >= allocation.base && address < end)
                || (one_past && address == end)
            {
                return Ok(InterpretValueKind::Ptr(InterpretPointer {
                    allocation: *id,
                    offset: address - allocation.base,
                }));
            }
        }
    }
    Ok(InterpretValueKind::DanglingPtr(address))
}

pub(super) fn retire<O: ExecutionObserver>(
    memory: &mut MemoryState,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    retire_core(memory, session, site, ImageOrigin::Memory)
}

pub(super) fn retire_call_memory<O: ExecutionObserver>(
    memory: &mut MemoryState,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    retire_core(memory, session, site, ImageOrigin::OwnedBoundary)
}

fn retire_core<O: ExecutionObserver>(
    memory: &mut MemoryState,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    origin: ImageOrigin,
) {
    while !memory.allocations.is_empty() {
        if matches!(origin, ImageOrigin::OwnedBoundary) {
            session.retirement_step(site, memory.allocations.len().saturating_add(1));
        }
        if let Some((_, allocation)) = memory.allocations.pop_first() {
            if matches!(origin, ImageOrigin::Memory) {
                session.retirement_poll(site);
            }
            allocation
                .bytes
                .retire_observed(&mut origin.progress(session, site));
        }
    }
    while !memory.unwritten_lane_bytes.is_empty() {
        if matches!(origin, ImageOrigin::OwnedBoundary) {
            session.retirement_step(site, memory.unwritten_lane_bytes.len().saturating_add(1));
        }
        if let Some((_, mut holes)) = memory.unwritten_lane_bytes.pop_first() {
            while !holes.is_empty() {
                if matches!(origin, ImageOrigin::OwnedBoundary) {
                    session.retirement_step(site, holes.len().saturating_add(1));
                }
                if holes.pop_first().is_some() && matches!(origin, ImageOrigin::Memory) {
                    session.retirement_poll(site);
                }
            }
        }
    }
}

// The ordinary interpreter's exact module-local code-word model: zero is null,
// and index+1 identifies the actual function roster entry, not its raw FuncId.
// This is reference-execution data, never an executable native address.
fn function_address<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    target: FuncId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    block: BlockId,
) -> RunResult<u64> {
    let module = interpreter
        .module
        .ok_or(Fault::Unsupported("observed function pointer Store module"))?;
    for (index, function) in module.functions.iter().enumerate() {
        event(session, site, ExecutionPhase::ModuleLookup, 1, 0)?;
        if function.id == target {
            return u64::try_from(index)
                .ok()
                .and_then(|index| index.checked_add(1))
                .ok_or_else(|| {
                    Fault::Semantic(invalid_function_pointer(
                        block,
                        "observed function code address exceeds target word",
                    ))
                });
        }
    }
    Err(Fault::Semantic(invalid_function_pointer(
        block,
        "observed function pointer Store target is absent",
    )))
}
fn function_from_address<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    address: u64,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    block: BlockId,
) -> RunResult<InterpretValueKind> {
    event(session, site, ExecutionPhase::ModuleLookup, 1, 0)?;
    if address == 0 {
        return Ok(InterpretValueKind::NullPtr);
    }
    let module = interpreter
        .module
        .ok_or(Fault::Unsupported("observed function pointer Load module"))?;
    let index = usize::try_from(address - 1).map_err(|_| {
        Fault::Semantic(invalid_function_pointer(
            block,
            "observed invalid function code address",
        ))
    })?;
    let function = module.functions.get(index).ok_or_else(|| {
        Fault::Semantic(invalid_function_pointer(
            block,
            "observed unregistered function code address",
        ))
    })?;
    Ok(InterpretValueKind::FnDef(function.id))
}
