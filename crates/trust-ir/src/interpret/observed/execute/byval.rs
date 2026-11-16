// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private ownership of actual plain byval storage. Images preserve every
//! initialized and poison byte; source and destination allocation identities
//! are distinct even for empty storage. No ordinary ABI/image/layout fallback
//! or provenance reconstruction is used here.
use super::*;

#[derive(Default)]
pub(super) struct Scope {
    copies: Vec<InterpretPointer>,
}

#[derive(Clone, Copy)]
pub(super) struct Layout {
    size: u64,
    align: u64,
}

impl Layout {
    pub(super) fn new(size: u64, align: u64) -> Self {
        Self { size, align }
    }
}

pub(super) fn validate<O: ExecutionObserver>(
    memory: &MemoryState,
    source: InterpretPointer,
    layout: Layout,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    block: BlockId,
) -> RunResult<()> {
    event(
        session,
        site,
        ExecutionPhase::AbiScan,
        map_work(memory.allocations.len())?,
        0,
    )?;
    // The whole-module descriptor check has already checked align. Check the
    // complete actual source extent, including a real identity at size zero.
    memory.checked_access(
        source,
        layout.size,
        layout.align,
        block,
        "typed ABI indirect argument",
    )?;
    if !memory.abi_access.is_empty() || !memory.unwritten_lane_bytes.is_empty() {
        return Err(Fault::Unsupported(
            "observed byval access/unwritten-lane metadata",
        ));
    }
    Ok(())
}

impl Scope {
    pub(super) fn copy<O: ExecutionObserver>(
        &mut self,
        memory: &mut MemoryState,
        source: InterpretPointer,
        layout: Layout,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
        block: BlockId,
    ) -> RunResult<InterpretValue> {
        validate(memory, source, layout, session, site, block)?;
        // Reserve the owner BEFORE constructing or installing a new object.
        // A failure during entry/bind therefore never abandons an allocation.
        reserve(&mut self.copies, 1, session, site)?;
        event(
            session,
            site,
            ExecutionPhase::SparseRun,
            map_work(memory.allocations.len())?,
            0,
        )?;
        let allocation = memory
            .allocations
            .get(&source.allocation)
            .ok_or(Fault::Representation)?;
        let image = allocation.bytes.read_observed(
            source.offset,
            layout.size,
            &mut session.structural_owned(site),
        )?;
        let result: RunResult<InterpretValue> = (|| {
            let base = align_addr(memory.next_addr, layout.align).ok_or_else(|| {
                Fault::Semantic(err(
                    InterpretErrorCode::OutOfMemory,
                    block,
                    "observed byval address alignment overflow",
                ))
            })?;
            let next = base
                .checked_add(layout.size.max(1))
                .filter(|next| *next - 1 <= memory.max_address)
                .ok_or_else(|| {
                    Fault::Semantic(err(
                        InterpretErrorCode::OutOfMemory,
                        block,
                        "observed byval address extent overflow",
                    ))
                })?;
            let id = memory.next_alloc_id;
            let next_id = id.checked_add(1).ok_or(Fault::Representation)?;
            event(
                session,
                site,
                ExecutionPhase::EntryArguments,
                1,
                size_of::<InterpretPointer>(),
            )?;
            map_insert::<u64, Allocation, O>(
                memory.allocations.len(),
                session,
                site,
                ExecutionPhase::HostAllocation,
            )?;
            let bytes =
                ByteStore::new_observed(layout.size, None, &mut session.structural_owned(site))?;
            // Everything after constructing bytes through owner installation
            // is infallible, constant work admitted by the map/vector reserves.
            memory.allocations.insert(
                id,
                Allocation {
                    base,
                    size: layout.size,
                    alive: true,
                    bytes,
                    ref_count: 1,
                    origin: None,
                    requested: layout.size,
                    live_borrows: 0,
                },
            );
            memory.next_alloc_id = next_id;
            memory.next_addr = next;
            let copy = InterpretPointer {
                allocation: id,
                offset: 0,
            };
            self.copies.push(copy);
            event(
                session,
                site,
                ExecutionPhase::SparseRun,
                map_work(memory.allocations.len())?,
                0,
            )?;
            memory
                .allocations
                .get_mut(&id)
                .ok_or(Fault::Representation)?
                .bytes
                .write_observed(0, &image, &mut session.structural_owned(site))?;
            Ok(InterpretValue {
                ty: Ty::Ptr,
                kind: InterpretValueKind::Ptr(copy),
            })
        })();
        image.retire_observed(&mut session.structural_owned(site));
        match result {
            Ok(_) if session.first_refusal().is_some() => Err(Fault::Admission),
            other => other,
        }
    }

    /// Retire only this frame's copies, retaining dead address/size tombstones
    /// so an escaped pointer never becomes another object or loses its numeric
    /// identity. Every actual image is drained under the original observer,
    /// even after sticky refusal. Caller objects and parent copies stay live.
    pub(super) fn retire<O: ExecutionObserver>(
        &mut self,
        memory: &mut MemoryState,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> RunResult<()> {
        let mut unavailable = false;
        while !self.copies.is_empty() {
            session.retirement_record(
                site,
                memory.allocations.len().saturating_add(1),
                size_of::<InterpretPointer>(),
            );
            let pointer = self
                .copies
                .pop()
                .expect("nonempty private owned-copy stack");
            match memory.allocations.get_mut(&pointer.allocation) {
                None => unavailable = true,
                Some(allocation) => {
                    // These families have no admitted observed creator. Refuse
                    // rather than silently retire a live borrow or RC owner.
                    if allocation.origin.is_some() || allocation.live_borrows != 0 {
                        unavailable = true;
                    }
                    allocation.alive = false;
                    // The zero-length constructor has no allocation or walk;
                    // its fixed metadata work is charged above. It is never a
                    // source image, layout, copy or ordinary execution fallback.
                    let bytes = core::mem::replace(&mut allocation.bytes, ByteStore::new(0, None));
                    bytes.retire_observed(&mut session.structural_owned(site));
                }
            }
        }
        if self.copies.capacity() != 0 {
            session.retirement_step(site, 1);
            self.copies = Vec::new();
        }
        if session.first_refusal().is_some() {
            Err(Fault::Admission)
        } else if unavailable {
            Err(Fault::Unsupported(
                "observed byval copy retirement unavailable",
            ))
        } else {
            Ok(())
        }
    }
}
