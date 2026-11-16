// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private operational lineage. Public values contain addresses, not this
//! execution's based-on facts. Neither serializing a value nor resolving its
//! numeric address can construct a parameter tag. The state is not Clone.
//!
//! This first slice models scalar lineage and complete scalar memory images.
//! An unmapped memory operation in a constrained call refuses before effects;
//! it cannot silently execute without appearing in the noalias history.

use super::*;
use crate::signature_abi::{AbiAttributes, AbiCapture};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) enum Fact {
    #[default]
    Independent,
    Based(BTreeSet<u64>),
    /// Witness of an actual private pointer-valued SSA/carrier operation.
    /// The allocation's birth/kind is stored separately and never inferred
    /// from this coordinate or from a numeric-address lookup.
    Pointer {
        allocation: u64,
        tags: BTreeSet<u64>,
    },
    /// A known constrained contribution underwent an unmapped transformation.
    /// This is unavailable evidence, never independent or proved undefined.
    Unknown,
}

impl Fact {
    fn contains(&self, tag: u64) -> bool {
        matches!(self, Self::Based(tags)|Self::Pointer {tags,..} if tags.contains(&tag))
    }
    pub(super) fn independent(&self) -> bool {
        matches!(self, Self::Independent)
    }
    pub(super) fn pointer(&self) -> Option<u64> {
        match self {
            Self::Pointer { allocation, .. } => Some(*allocation),
            _ => None,
        }
    }
    pub(super) fn actual_pointer(&mut self, pointer: InterpretPointer) {
        match self {
            Self::Independent => {
                *self = Self::Pointer {
                    allocation: pointer.allocation,
                    tags: BTreeSet::new(),
                }
            }
            Self::Based(tags) => {
                *self = Self::Pointer {
                    allocation: pointer.allocation,
                    tags: tags.clone(),
                }
            }
            Self::Pointer { allocation, .. } if *allocation == pointer.allocation => {}
            _ => *self = Self::Unknown,
        }
    }
    fn retag(&mut self, tag: u64, block: BlockId) -> InterpretResult<()> {
        match self {
            Self::Independent => *self = Self::Based(BTreeSet::from([tag])),
            Self::Based(tags) | Self::Pointer { tags, .. } => {
                tags.insert(tag);
            }
            Self::Unknown => {
                return Err(unavailable(
                    block,
                    "parameter has unresolved incoming lineage",
                ));
            }
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
pub(super) struct Packet {
    pub(super) values: Vec<InterpretValue>,
    pub(super) facts: Vec<Fact>,
}
impl Packet {
    pub(super) fn plain(values: Vec<InterpretValue>) -> Self {
        Self {
            facts: vec![Fact::Independent; values.len()],
            values,
        }
    }
    pub(super) fn check(&self, block: BlockId) -> InterpretResult<()> {
        if self.values.len() == self.facts.len() {
            Ok(())
        } else {
            Err(unavailable(
                block,
                "internal value/lineage packet population differs",
            ))
        }
    }
}
impl core::ops::Deref for Packet {
    type Target = [InterpretValue];
    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

#[derive(Clone, Copy, Debug)]
enum Location {
    Bytes {
        allocation: u64,
        start: u64,
        end: u64,
    },
    Rc(u64),
}
impl Location {
    fn overlaps(self, other: Self) -> bool {
        match (self, other) {
            (
                Self::Bytes {
                    allocation: a,
                    start: x,
                    end: y,
                },
                Self::Bytes {
                    allocation: b,
                    start: u,
                    end: v,
                },
            ) => a == b && x < v && u < y,
            (Self::Rc(a), Self::Rc(b)) => a == b,
            _ => false,
        }
    }
}
struct Event {
    location: Location,
    based: bool,
    write: bool,
}
struct Scope {
    tag: u64,
    readonly: bool,
    no_free: bool,
    no_alias: bool,
    capture: AbiCapture,
    allocation: Option<u64>,
    entry_floor: u64,
    events: Vec<Event>,
}
#[derive(Clone, Copy)]
enum OriginKind {
    Stack,
    Heap,
    Global,
}
struct Origin {
    born: u64,
    kind: OriginKind,
}
pub(super) struct Fresh {
    floor: u64,
    before: BTreeSet<u64>,
    definite: BTreeSet<u64>,
}
#[derive(Default)]
pub(super) struct Decode {
    fact: Fact,
    pointer: Option<InterpretPointer>,
}

/// Sparse shadow bytes, not an address-to-authority lookup. A write supplies
/// the actual source SSA fact; a read consumes the full actual stored extent.
/// Independent holes carry no tag. Partial/mixed representations are Unknown.
#[derive(Default)]
struct Shadows(BTreeMap<u64, BTreeMap<u64, (u64, Fact)>>);
impl Shadows {
    fn image(&self, ptr: InterpretPointer, bytes: u64) -> Vec<(u64, u64, Fact)> {
        let end = ptr.offset + bytes;
        let mut image = Vec::new();
        let mut cursor = ptr.offset;
        if let Some(runs) = self.0.get(&ptr.allocation) {
            for (&start, (stop, fact)) in runs.range(..end) {
                if *stop <= ptr.offset {
                    continue;
                }
                let start = start.max(ptr.offset);
                let stop = (*stop).min(end);
                if cursor < start {
                    image.push((cursor - ptr.offset, start - ptr.offset, Fact::Independent));
                }
                image.push((start - ptr.offset, stop - ptr.offset, fact.clone()));
                cursor = stop;
            }
        }
        if cursor < end {
            image.push((cursor - ptr.offset, bytes, Fact::Independent));
        }
        image
    }
    fn uniform(&self, ptr: InterpretPointer, bytes: u64) -> Fact {
        let image = self.image(ptr, bytes);
        let Some((_, _, first)) = image.first() else {
            return Fact::Independent;
        };
        if image.iter().all(|(_, _, fact)| fact == first) {
            first.clone()
        } else {
            Fact::Unknown
        }
    }
    fn write(&mut self, ptr: InterpretPointer, bytes: u64, fact: Fact) {
        if bytes == 0 {
            return;
        }
        let end = ptr.offset + bytes;
        let runs = self.0.entry(ptr.allocation).or_default();
        let touched: Vec<_> = runs
            .range(..end)
            .filter(|(_, (stop, _))| *stop > ptr.offset)
            .map(|(&start, (stop, fact))| (start, *stop, fact.clone()))
            .collect();
        for (start, stop, old) in touched {
            runs.remove(&start);
            if start < ptr.offset {
                runs.insert(start, (ptr.offset, old.clone()));
            }
            if stop > end {
                runs.insert(end, (stop, old));
            }
        }
        if !fact.independent() {
            runs.insert(ptr.offset, (end, fact));
        }
        // Canonical population: a cleared allocation has no shadow entry.
        // This also covers Independent writes performed by Shadows::copy.
        if runs.is_empty() {
            self.0.remove(&ptr.allocation);
        }
    }
    fn copy(&mut self, dst: InterpretPointer, src: InterpretPointer, bytes: u64) {
        let image = self.image(src, bytes); // snapshot BEFORE any overlapping write
        self.write(dst, bytes, Fact::Independent);
        for (start, end, fact) in image {
            self.write(
                InterpretPointer {
                    allocation: dst.allocation,
                    offset: dst.offset + start,
                },
                end - start,
                fact,
            );
        }
    }
}

#[derive(Default)]
pub(super) struct State {
    pub(super) values: BTreeMap<ValueId, Fact>,
    next_tag: u64,
    scopes: Vec<Scope>,
    shadows: Shadows,
    retired: BTreeMap<u64, (AbiCapture, Option<u64>)>,
    origins: BTreeMap<u64, Origin>,
    next_birth: u64,
    fresh_floors: Vec<u64>,
    decode: std::cell::RefCell<Decode>,
    fresh_protected: BTreeSet<u64>,
}
impl State {
    /// A refusal-only guard for the observed plain-memory closure. Copying
    /// nonempty lineage needs its own metered semantics; never erase shadows
    /// or call the ordinary unmetered provenance copier under an observer.
    pub(super) fn observed_inert(&self) -> bool {
        let decode = self.decode.borrow();
        self.values.is_empty()
            && self.scopes.is_empty()
            && self.shadows.0.is_empty()
            && self.retired.is_empty()
            && self.origins.is_empty()
            && self.fresh_floors.is_empty()
            && self.fresh_protected.is_empty()
            && matches!(decode.fact, Fact::Independent)
            && decode.pointer.is_none()
    }
    pub(super) fn fact(&self, id: ValueId) -> Fact {
        self.values.get(&id).cloned().unwrap_or_default()
    }
    pub(super) fn checkpoint(&self) -> usize {
        self.scopes.len()
    }
    pub(super) fn close(&mut self, checkpoint: usize) {
        for scope in self.scopes.drain(checkpoint..) {
            if scope.capture != AbiCapture::Any {
                self.retired
                    .insert(scope.tag, (scope.capture, scope.allocation));
            }
        }
    }
    fn constrained(&self) -> bool {
        !self.scopes.is_empty()
            || !self.retired.is_empty()
            || !self.fresh_floors.is_empty()
            || !self.fresh_protected.is_empty()
    }
    fn tracking(&self) -> bool {
        self.constrained() || !self.shadows.0.is_empty()
    }
    fn any_none(&self) -> bool {
        self.scopes
            .iter()
            .any(|scope| scope.capture == AbiCapture::None)
            || self
                .retired
                .values()
                .any(|(capture, _)| *capture == AbiCapture::None)
    }
    fn retired_none(&self, fact: &Fact) -> bool {
        self.retired
            .iter()
            .any(|(tag, (capture, _))| *capture == AbiCapture::None && fact.contains(*tag))
    }
    fn none_address(&self, fact: &Fact) -> bool {
        self.scopes
            .iter()
            .any(|scope| scope.capture == AbiCapture::None && fact.contains(scope.tag))
            || self
                .retired
                .iter()
                .any(|(tag, (capture, _))| *capture == AbiCapture::None && fact.contains(*tag))
    }
    pub(super) fn capture_exit(
        &self,
        checkpoint: usize,
        returns: Option<&Packet>,
        memory: &MemoryState,
        block: BlockId,
    ) -> InterpretResult<()> {
        for scope in &self.scopes[checkpoint..] {
            if scope.capture != AbiCapture::None {
                continue;
            }
            if returns
                .is_some_and(|packet| packet.facts.iter().any(|fact| fact.contains(scope.tag)))
            {
                return Err(ub(
                    block,
                    "typed ABI captures(none) returns the pointer's address",
                ));
            }
            if returns.is_some_and(|packet| {
                packet
                    .facts
                    .iter()
                    .any(|fact| matches!(fact, Fact::Unknown))
            }) {
                return Err(unavailable(
                    block,
                    "unresolved return cannot establish captures(none) address independence",
                ));
            }
            let mut exposed: BTreeSet<_> = memory
                .allocations
                .keys()
                .filter(|allocation| **allocation < scope.entry_floor)
                .copied()
                .collect();
            exposed.extend(self.origins.iter().filter_map(|(id, origin)| {
                matches!(origin.kind, OriginKind::Global).then_some(*id)
            }));
            // A complete pointer actually returned by this boundary makes its
            // storage caller-visible too, even when the new root itself has
            // no None tag. Follow its retained scalar images transitively.
            if let Some(packet) = returns {
                for (value, fact) in packet.values.iter().zip(&packet.facts) {
                    if let InterpretValueKind::Ptr(pointer) = &value.kind {
                        exposed.insert(pointer.allocation);
                    } else if fact.pointer().is_some_and(|root| !exposed.contains(&root)) {
                        return Err(unavailable(
                            block,
                            "captures(none) returned pointer-image root needs a complete scalar pointer representation",
                        ));
                    }
                }
            }
            loop {
                let previous = exposed.len();
                for (allocation, runs) in &self.shadows.0 {
                    if exposed.contains(allocation) {
                        for (_, fact) in runs.values() {
                            if let Some(pointer) = fact.pointer() {
                                exposed.insert(pointer);
                            }
                        }
                    }
                }
                if previous == exposed.len() {
                    break;
                }
            }
            for allocation in exposed {
                if !memory
                    .allocations
                    .get(&allocation)
                    .is_some_and(|cell| cell.alive)
                {
                    continue;
                }
                if self.shadows.0.get(&allocation).is_some_and(|runs| {
                    runs.values()
                        .any(|(_, fact)| fact.contains(scope.tag) || matches!(fact, Fact::Unknown))
                }) {
                    return Err(unavailable(
                        block,
                        "captures(none) address escapes into potentially caller-visible memory",
                    ));
                }
            }
        }
        Ok(())
    }
    pub(super) fn begin_fresh(&mut self, memory: &MemoryState, arguments: &Packet) -> Fresh {
        let floor = self.next_birth;
        self.fresh_floors.push(floor);
        let before = memory.allocations.keys().copied().collect();
        let definite = arguments
            .values
            .iter()
            .filter_map(|value| match &value.kind {
                InterpretValueKind::Ptr(ptr) => Some(ptr.allocation),
                _ => None,
            })
            .collect();
        Fresh {
            floor,
            before,
            definite,
        }
    }
    pub(super) fn end_fresh(&mut self) {
        self.fresh_floors.pop();
    }
    pub(super) fn fresh_result(
        &mut self,
        fresh: &Fresh,
        returns: &Packet,
        memory: &MemoryState,
        block: BlockId,
    ) -> InterpretResult<()> {
        let [value] = returns.values.as_slice() else {
            return Err(unavailable(
                block,
                "fresh result requires one actual pointer result",
            ));
        };
        if matches!(&value.kind, InterpretValueKind::NullPtr) {
            return Ok(());
        }
        let pointer = expect_pointer(value, block, "typed ABI fresh result")?;
        memory.checked_access(pointer, 0, 1, block, "typed ABI fresh result")?;
        let mut reachable = fresh.definite.clone();
        reachable.extend(
            self.origins.iter().filter_map(|(id, origin)| {
                matches!(origin.kind, OriginKind::Global).then_some(*id)
            }),
        );
        if reachable.contains(&pointer.allocation) {
            return Err(ub(
                block,
                "typed ABI noalias result is already accessible through a caller argument or actual global",
            ));
        }
        loop {
            let previous = reachable.len();
            for (id, runs) in &self.shadows.0 {
                if reachable.contains(id) {
                    for (_, fact) in runs.values() {
                        if let Some(root) = fact.pointer() {
                            reachable.insert(root);
                        }
                    }
                }
            }
            if reachable.len() == previous {
                break;
            }
        }
        if reachable.contains(&pointer.allocation) {
            return Err(unavailable(
                block,
                "retained caller-visible pointer representation prevents fresh-result isolation",
            ));
        }
        if returns.facts[0].pointer() != Some(pointer.allocation) {
            return Err(unavailable(
                block,
                "fresh result lacks the actual pointer-producing lineage",
            ));
        }
        let Some(origin) = self.origins.get(&pointer.allocation) else {
            return Err(unavailable(
                block,
                "fresh result has no retained allocation producer",
            ));
        };
        if !matches!(origin.kind, OriginKind::Heap) || origin.born < fresh.floor {
            return Err(unavailable(
                block,
                "fresh result is not a new live heap allocation produced during this call",
            ));
        }
        let mut possible = fresh.before.clone();
        loop {
            let previous = possible.len();
            for (id, runs) in &self.shadows.0 {
                if possible.contains(id) {
                    for (_, fact) in runs.values() {
                        if let Some(root) = fact.pointer() {
                            possible.insert(root);
                        }
                    }
                }
            }
            if possible.len() == previous {
                break;
            }
        }
        if possible.iter().any(|id| {
            self.shadows
                .0
                .get(id)
                .is_some_and(|runs| runs.values().any(|(_, fact)| matches!(fact, Fact::Unknown)))
        }) {
            return Err(unavailable(
                block,
                "unknown caller-visible representation prevents fresh-result isolation",
            ));
        }
        if possible.contains(&pointer.allocation) {
            return Err(unavailable(
                block,
                "fresh result may be exposed through a pre-existing caller object",
            ));
        }
        self.fresh_protected.insert(pointer.allocation);
        Ok(())
    }
    pub(super) fn imported(
        &self,
        arguments: &[InterpretValue],
        block: BlockId,
    ) -> InterpretResult<()> {
        for value in arguments {
            if (!self.retired.is_empty() || !self.fresh_protected.is_empty())
                && !matches!(
                    &value.kind,
                    InterpretValueKind::Ptr(_)
                        | InterpretValueKind::Int(_)
                        | InterpretValueKind::Bool(_)
                        | InterpretValueKind::FloatBits(_)
                        | InterpretValueKind::Unit
                        | InterpretValueKind::NullPtr
                        | InterpretValueKind::DanglingPtr(_)
                        | InterpretValueKind::FnDef(_)
                        | InterpretValueKind::PartialBytes(_)
                )
            {
                return Err(unavailable(
                    block,
                    "public structured values have no retained protected-pointer lane provenance",
                ));
            }
            if let InterpretValueKind::Ptr(pointer) = &value.kind
                && (self
                    .retired
                    .values()
                    .any(|(_, allocation)| *allocation == Some(pointer.allocation))
                    || self.fresh_protected.contains(&pointer.allocation))
            {
                return Err(unavailable(
                    block,
                    "public copied pointer coordinates cannot import protected execution provenance",
                ));
            }
        }
        Ok(())
    }
    pub(super) fn swap_decode(&self, fact: Fact) -> Decode {
        self.decode.replace(Decode {
            fact,
            pointer: None,
        })
    }
    pub(super) fn restore_decode(&self, previous: Decode) {
        self.decode.replace(previous);
    }
    pub(super) fn check_decode(
        &self,
        pointer: InterpretPointer,
        block: BlockId,
    ) -> InterpretResult<()> {
        let protected =
            self.scopes
                .iter()
                .any(|scope| scope.allocation == Some(pointer.allocation))
                || self
                    .retired
                    .values()
                    .any(|(_, allocation)| *allocation == Some(pointer.allocation))
                || self.origins.get(&pointer.allocation).is_some_and(|origin| {
                    self.fresh_floors.iter().any(|floor| origin.born >= *floor)
                });
        if !protected && !self.fresh_protected.contains(&pointer.allocation) {
            return Ok(());
        }
        let decode = self.decode.borrow();
        if decode.fact.pointer() == Some(pointer.allocation)
            || decode
                .pointer
                .is_some_and(|source| source.allocation == pointer.allocation)
        {
            return Ok(());
        }
        if self.scopes.iter().any(|scope| {
            scope.allocation == Some(pointer.allocation) && decode.fact.contains(scope.tag)
        }) || self.retired.iter().any(|(tag, (_, allocation))| {
            *allocation == Some(pointer.allocation) && decode.fact.contains(*tag)
        }) {
            return Ok(());
        }
        Err(unavailable(
            block,
            "numeric address cannot reconstruct protected pointer provenance",
        ))
    }

    pub(super) fn require_unconstrained(
        &self,
        block: BlockId,
        detail: &str,
    ) -> InterpretResult<()> {
        if !self.tracking() {
            Ok(())
        } else {
            Err(unavailable(block, detail))
        }
    }
    pub(super) fn parameter(
        &mut self,
        fact: &mut Fact,
        pointer: Option<InterpretPointer>,
        entry_floor: u64,
        attrs: &AbiAttributes,
        block: BlockId,
    ) -> InterpretResult<()> {
        let constrained =
            attrs.no_alias || attrs.readonly || attrs.no_free || attrs.capture != AbiCapture::Any;
        if !constrained && !self.tracking() {
            return Ok(());
        }
        if let Some(pointer) = pointer {
            fact.actual_pointer(pointer);
        }
        if !constrained {
            return Ok(());
        }
        let tag = self.next_tag;
        self.next_tag = self
            .next_tag
            .checked_add(1)
            .ok_or_else(|| unavailable(block, "lineage population exhausted"))?;
        fact.retag(tag, block)?;
        self.scopes.push(Scope {
            tag,
            readonly: attrs.readonly,
            no_free: attrs.no_free,
            no_alias: attrs.no_alias,
            capture: attrs.capture,
            allocation: pointer.map(|pointer| pointer.allocation),
            entry_floor,
            events: Vec::new(),
        });
        Ok(())
    }
    fn access(
        &mut self,
        location: Location,
        fact: &Fact,
        write: bool,
        free: bool,
        block: BlockId,
    ) -> InterpretResult<()> {
        // Retained scalar shadows still follow ordinary writes after every
        // access scope expires; no expired access policy is imposed here.
        if !self.constrained() {
            return Ok(());
        }
        if matches!(fact, Fact::Unknown) {
            return Err(unavailable(block, "access has unresolved based-on lineage"));
        }
        for (tag, (capture, _)) in &self.retired {
            if fact.contains(*tag)
                && (matches!(capture, AbiCapture::None | AbiCapture::Address)
                    || (write || free) && *capture == AbiCapture::ReadOnly)
            {
                return Err(ub(
                    block,
                    "typed ABI access uses provenance whose capture permissions expired at return/unwind",
                ));
            }
        }
        for scope in &self.scopes {
            let based = fact.contains(scope.tag);
            if based && free && scope.readonly && !scope.no_free {
                return Err(unavailable(
                    block,
                    "readonly allocation invalidation needs a distinct lifetime model",
                ));
            }
            if based && ((write && scope.readonly) || (free && scope.no_free)) {
                return Err(ub(
                    block,
                    "typed ABI based-on access violates readonly/nofree",
                ));
            }
            if scope.no_alias
                && scope.events.iter().any(|old| {
                    old.location.overlaps(location) && old.based != based && (old.write || write)
                })
            {
                return Err(ub(
                    block,
                    "typed ABI noalias has conflicting based-on and independent accesses to modified storage",
                ));
            }
        }
        for scope in &mut self.scopes {
            if scope.no_alias {
                scope.events.push(Event {
                    location,
                    based: fact.contains(scope.tag),
                    write,
                });
            }
        }
        Ok(())
    }
    pub(super) fn bytes(
        &mut self,
        ptr: InterpretPointer,
        bytes: u64,
        fact: &Fact,
        write: bool,
        free: bool,
        block: BlockId,
    ) -> InterpretResult<()> {
        let end = ptr
            .offset
            .checked_add(bytes)
            .ok_or_else(|| unavailable(block, "access extent overflow"))?;
        if bytes == 0 {
            return Ok(());
        }
        self.access(
            Location::Bytes {
                allocation: ptr.allocation,
                start: ptr.offset,
                end,
            },
            fact,
            write,
            free,
            block,
        )
    }
    pub(super) fn rc(
        &mut self,
        ptr: InterpretPointer,
        fact: &Fact,
        write: bool,
        free: bool,
        block: BlockId,
    ) -> InterpretResult<()> {
        self.access(Location::Rc(ptr.allocation), fact, write, free, block)
    }
    pub(super) fn copy(&mut self, dst: InterpretPointer, src: InterpretPointer, bytes: u64) {
        self.shadows.copy(dst, src, bytes);
    }
}

pub(super) fn unavailable(block: BlockId, detail: &str) -> InterpretError {
    err(
        InterpretErrorCode::UnsupportedCall,
        block,
        format!("typed ABI provenance: {detail}"),
    )
}

pub(super) struct Plan {
    facts: Option<Vec<Fact>>,
    writes: Vec<Write>,
    origin: Option<OriginKind>,
    pub(super) decode: Fact,
}
enum Write {
    Scalar(InterpretPointer, u64, Fact),
    Copy(InterpretPointer, InterpretPointer, u64),
}
impl Plan {
    pub(super) fn commit(
        mut self,
        state: &mut ExecState,
        node: &InstrNode,
        block: BlockId,
    ) -> InterpretResult<()> {
        if let Some(kind) = self.origin {
            for id in &node.results {
                if let Some(InterpretValue {
                    kind: InterpretValueKind::Ptr(pointer),
                    ..
                }) = state.values.get(id)
                {
                    if !state.provenance.origins.contains_key(&pointer.allocation) {
                        let born = state.provenance.next_birth;
                        state.provenance.next_birth = born.checked_add(1).ok_or_else(|| {
                            unavailable(block, "allocation event population exhausted")
                        })?;
                        state
                            .provenance
                            .origins
                            .insert(pointer.allocation, Origin { born, kind });
                    }
                    self.facts = Some(vec![Fact::Pointer {
                        allocation: pointer.allocation,
                        tags: BTreeSet::new(),
                    }]);
                }
            }
        }
        if let Some(facts) = self.facts {
            for (id, fact) in node.results.iter().zip(facts) {
                state.provenance.values.insert(*id, fact);
            }
        }
        for write in self.writes {
            match write {
                Write::Scalar(ptr, bytes, fact) => state.provenance.shadows.write(ptr, bytes, fact),
                Write::Copy(dst, src, bytes) => state.provenance.shadows.copy(dst, src, bytes),
            }
        }
        Ok(())
    }
}

fn scalar(ty: &Ty) -> bool {
    int_shape(ty).is_some()
        || matches!(
            ty,
            Ty::Bool
                | Ty::Char
                | Ty::F16
                | Ty::F32
                | Ty::F64
                | Ty::Ptr
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Rc(_)
                | Ty::Func(_)
        )
}

impl Interpreter<'_> {
    pub(super) fn with_pointer_decode<T>(
        &self,
        state: &ExecState,
        fact: &Fact,
        pointer: Option<InterpretPointer>,
        operation: impl FnOnce() -> InterpretResult<T>,
    ) -> InterpretResult<T> {
        let previous = state.provenance.decode.replace(Decode {
            fact: fact.clone(),
            pointer,
        });
        let result = operation();
        state.provenance.decode.replace(previous);
        result
    }

    /// The normal evaluator is still the sole executor. This hook validates
    /// actual operands and records the memory events before it may mutate;
    /// the Plan changes shadows only after the original operation succeeds.
    pub(super) fn provenance_before_node(
        &self,
        block: BlockId,
        node: &InstrNode,
        state: &mut ExecState,
    ) -> InterpretResult<Plan> {
        let mut plan = Plan {
            facts: Some(vec![Fact::Independent; node.results.len()]),
            writes: Vec::new(),
            origin: None,
            decode: Fact::Independent,
        };
        if matches!(
            &node.inst,
            Inst::Call { .. }
                | Inst::CallIndirect { .. }
                | Inst::Invoke { .. }
                | Inst::InvokeIndirect { .. }
                | Inst::Drop { .. }
                | Inst::DropInvoke { .. }
        ) {
            plan.facts = None;
        }
        // Maintain retained shadow bytes through actual ordinary writes too.
        // Skip only a completely empty lineage state; expired parameter tags
        // impose no ordinary access policy, while capture permissions persist.
        if !state.provenance.tracking() {
            return Ok(plan);
        }
        let fact = |id| state.provenance.fact(id);
        if state.provenance.any_none() {
            let condition = match &node.inst {
                Inst::Select { cond, .. }
                | Inst::CondBr { cond, .. }
                | Inst::Assert { cond, .. }
                | Inst::Assume { cond }
                | Inst::AssertInvoke { cond, .. } => Some(*cond),
                Inst::Switch { value, .. } => Some(*value),
                _ => None,
            };
            if condition.is_some_and(|id| {
                state.provenance.none_address(&fact(id)) || matches!(fact(id), Fact::Unknown)
            }) {
                return Err(unavailable(
                    block,
                    "captures(none) address-dependent control needs a noninterference proof",
                ));
            }
            if let Inst::Return { values } = &node.inst {
                if values
                    .iter()
                    .any(|id| state.provenance.retired_none(&fact(*id)))
                {
                    return Err(ub(
                        block,
                        "typed ABI return exposes a retired captures(none) address",
                    ));
                }
                if values.iter().any(|id| matches!(fact(*id), Fact::Unknown)) {
                    return Err(unavailable(
                        block,
                        "unknown return may expose a captures(none) address",
                    ));
                }
            }
            if matches!(
                &node.inst,
                Inst::Load { volatile: true, .. } | Inst::Store { volatile: true, .. }
            ) {
                return Err(unavailable(
                    block,
                    "volatile capture observation needs target-specific semantics",
                ));
            }
        }
        match &node.inst {
            Inst::Alloca { .. } => plan.origin = Some(OriginKind::Stack),
            Inst::HeapAlloc { .. } => plan.origin = Some(OriginKind::Heap),
            Inst::GlobalAddr { .. } => plan.origin = Some(OriginKind::Global),
            Inst::Copy { operand, .. }
            | Inst::GEP { base: operand, .. }
            | Inst::Borrow { ptr: operand }
            | Inst::BorrowMut { ptr: operand } => plan.facts = Some(vec![fact(*operand)]),
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let mut incoming = fact(*operand);
                if state.provenance.none_address(&incoming)
                    && matches!(
                        op,
                        CastOp::PtrToInt | CastOp::IntToPtr | CastOp::Bitcast | CastOp::Transmute
                    )
                {
                    return Err(unavailable(
                        block,
                        "captures(none) address inspection needs an independence proof",
                    ));
                }
                if let InterpretValueKind::Ptr(pointer) = &state.value(block, *operand)?.kind {
                    incoming.actual_pointer(*pointer);
                }
                plan.decode = incoming.clone();
                let exact = matches!(
                    op,
                    CastOp::PtrToInt | CastOp::IntToPtr | CastOp::PtrToPtr | CastOp::Bitcast
                ) && scalar(src_ty)
                    && scalar(dst_ty)
                    && self.byte_size(src_ty, block)? == self.pointer_bytes()
                    && self.byte_size(dst_ty, block)? == self.pointer_bytes();
                plan.facts = Some(vec![if exact || incoming.independent() {
                    incoming
                } else {
                    Fact::Unknown
                }]);
            }
            Inst::Select {
                cond,
                then_val,
                else_val,
                ..
            } => {
                let selected = match state.value(block, *cond)?.as_bool() {
                    Some(true) => *then_val,
                    Some(false) => *else_val,
                    None => return Err(type_error(block, "select requires bool")),
                };
                plan.facts = Some(vec![fact(selected)]);
            }
            Inst::BinOp { lhs, rhs, .. }
            | Inst::ICmp { lhs, rhs, .. }
            | Inst::FCmp { lhs, rhs, .. }
            | Inst::Overflow { lhs, rhs, .. } => {
                if state.provenance.none_address(&fact(*lhs))
                    || state.provenance.none_address(&fact(*rhs))
                {
                    return Err(unavailable(
                        block,
                        "captures(none) address-dependent computation needs a noninterference proof",
                    ));
                }
                if !fact(*lhs).independent() || !fact(*rhs).independent() {
                    plan.facts = Some(vec![Fact::Unknown; node.results.len()]);
                }
            }
            Inst::UnOp { operand, .. } => {
                if !fact(*operand).independent() {
                    plan.facts = Some(vec![Fact::Unknown; node.results.len()]);
                }
            }
            Inst::Load { ty, ptr, .. } | Inst::AtomicLoad { ty, ptr, .. } => {
                if !scalar(ty) {
                    state.provenance.require_unconstrained(
                        block,
                        "aggregate load needs structural shadow projection",
                    )?;
                }
                let ptr_value = state.value(block, *ptr)?;
                let pointer = expect_pointer(ptr_value, block, "Load")?;
                let bytes = self.byte_size(ty, block)?;
                let align = match &node.inst {
                    Inst::Load { align, .. } | Inst::Store { align, .. } => *align,
                    _ => None,
                };
                let align = checked_align(align.unwrap_or(self.byte_align(ty, block)?), block)?;
                state
                    .memory
                    .checked_access(pointer, bytes, align, block, "Load")?;
                let incoming = fact(*ptr);
                state
                    .provenance
                    .bytes(pointer, bytes, &incoming, false, false, block)?;
                let loaded = state.provenance.shadows.uniform(pointer, bytes);
                plan.decode = loaded.clone();
                plan.facts = Some(vec![loaded]);
            }
            Inst::Store { ty, ptr, value, .. } | Inst::AtomicStore { ty, ptr, value, .. } => {
                if !scalar(ty) {
                    state.provenance.require_unconstrained(
                        block,
                        "aggregate store needs structural shadow projection",
                    )?;
                }
                let pointer = expect_pointer(state.value(block, *ptr)?, block, "Store")?;
                let bytes = self.byte_size(ty, block)?;
                let align = match &node.inst {
                    Inst::Load { align, .. } | Inst::Store { align, .. } => *align,
                    _ => None,
                };
                let align = checked_align(align.unwrap_or(self.byte_align(ty, block)?), block)?;
                state
                    .memory
                    .checked_access(pointer, bytes, align, block, "Store")?;
                let incoming = fact(*ptr);
                let mut stored = fact(*value);
                if let InterpretValueKind::Ptr(pointer) = &state.value(block, *value)?.kind {
                    if state.provenance.constrained() {
                        stored.actual_pointer(*pointer);
                    } else if !matches!(stored, Fact::Unknown) {
                        // No live/retired capture or fresh scope depends on
                        // these expired known tags. This ACTUAL overwrite
                        // replaces them; unresolved representations survive.
                        stored = Fact::Independent;
                    }
                }
                if matches!(stored, Fact::Unknown)
                    && (!state.provenance.fresh_floors.is_empty() || state.provenance.any_none())
                {
                    return Err(unavailable(
                        block,
                        "unknown stored representation cannot establish capture/fresh-result isolation",
                    ));
                }
                state
                    .provenance
                    .bytes(pointer, bytes, &incoming, true, false, block)?;
                plan.writes.push(Write::Scalar(pointer, bytes, stored));
            }
            Inst::MemCopy {
                dst, src, bytes, ..
            } => {
                let count = self.bulk_byte_count(state.value(block, *bytes)?, block, "MemCopy")?;
                if count != 0 {
                    let dst_pointer = expect_pointer(state.value(block, *dst)?, block, "MemCopy")?;
                    let src_pointer = expect_pointer(state.value(block, *src)?, block, "MemCopy")?;
                    state
                        .memory
                        .checked_access(src_pointer, count, 1, block, "MemCopy")?;
                    state
                        .memory
                        .checked_access(dst_pointer, count, 1, block, "MemCopy")?;
                    let src_fact = fact(*src);
                    let dst_fact = fact(*dst);
                    state
                        .provenance
                        .bytes(src_pointer, count, &src_fact, false, false, block)?;
                    state
                        .provenance
                        .bytes(dst_pointer, count, &dst_fact, true, false, block)?;
                    plan.writes
                        .push(Write::Copy(dst_pointer, src_pointer, count));
                }
            }
            Inst::MemSet { dst, byte, bytes } => {
                let count = self.bulk_byte_count(state.value(block, *bytes)?, block, "MemSet")?;
                if count != 0 {
                    let pointer = expect_pointer(state.value(block, *dst)?, block, "MemSet")?;
                    state
                        .memory
                        .checked_access(pointer, count, 1, block, "MemSet")?;
                    let incoming = fact(*dst);
                    let stored = fact(*byte);
                    state
                        .provenance
                        .bytes(pointer, count, &incoming, true, false, block)?;
                    // Repetition of a partial scalar representation cannot
                    // reconstruct a pointer basis, even if byte values match.
                    plan.writes.push(Write::Scalar(
                        pointer,
                        count,
                        if stored.independent() {
                            stored
                        } else {
                            Fact::Unknown
                        },
                    ));
                }
            }
            Inst::Dealloc { ptr } => {
                let pointer = expect_pointer(state.value(block, *ptr)?, block, "Dealloc")?;
                let incoming = fact(*ptr);
                let allocation = state
                    .memory
                    .checked_access(pointer, 0, 1, block, "Dealloc")?;
                let bytes = allocation.size;
                state.provenance.bytes(
                    InterpretPointer {
                        offset: 0,
                        ..pointer
                    },
                    bytes,
                    &incoming,
                    true,
                    true,
                    block,
                )?;
                state.provenance.rc(pointer, &incoming, true, true, block)?;
            }
            Inst::Retain { ptr } | Inst::Release { ptr } | Inst::IsUnique { ptr } => {
                let pointer = expect_pointer(state.value(block, *ptr)?, block, "RC")?;
                // Preserve the ordinary allocation/origin/base/liveness floor.
                state.memory.is_unique(pointer, block)?;
                let incoming = fact(*ptr);
                let write = !matches!(&node.inst, Inst::IsUnique { .. });
                let free = matches!(&node.inst, Inst::Release { .. })
                    && state
                        .memory
                        .allocations
                        .get(&pointer.allocation)
                        .is_some_and(|cell| cell.ref_count == 1);
                state
                    .provenance
                    .rc(pointer, &incoming, write, free, block)?;
                if free {
                    let size = state.memory.allocations[&pointer.allocation].size;
                    state
                        .provenance
                        .bytes(pointer, size, &incoming, true, true, block)?;
                }
            }
            // These actual paths supply their returned facts explicitly.
            Inst::Call { .. }
            | Inst::CallIndirect { .. }
            | Inst::Invoke { .. }
            | Inst::InvokeIndirect { .. }
            | Inst::Drop { .. }
            | Inst::DropInvoke { .. } => plan.facts = None,
            Inst::Const { .. }
            | Inst::NullPtr
            | Inst::Undef { .. }
            | Inst::Return { .. }
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Assume { .. }
            | Inst::Assert { .. }
            | Inst::EndBorrow { .. }
            | Inst::AssertInvoke { .. }
            | Inst::Unreachable
            | Inst::LandingPad { .. }
            | Inst::Resume { .. }
            | Inst::Fence { .. } => {}
            _ => {
                state.provenance.require_unconstrained(
                    block,
                    "instruction has no complete constrained-access/structural-lineage model",
                )?;
                let mut constrained = false;
                node.inst
                    .visit_value_operands(|id| constrained |= !fact(id).independent());
                if constrained {
                    return Err(unavailable(
                        block,
                        "instruction cannot discard retained constrained lineage",
                    ));
                }
            }
        }
        Ok(plan)
    }
}
