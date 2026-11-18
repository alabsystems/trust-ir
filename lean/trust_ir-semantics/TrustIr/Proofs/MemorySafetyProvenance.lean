-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.MemorySafetyLifetime

namespace TrustIr

-- =================================================================
-- Provenance: every pointer operand names the allocation it was derived from
-- =================================================================

/-!
The general theorems of SPEC "A pointer operand names the allocation it was
derived from", stated for EVERY state: each instruction that consumes a
pointer moves, reads or frees only the allocation its operand rule names,
never a neighbour (`semAccess_names_provenance` above is the access rule).
The concrete theorems after them are the decided cells of the differential's
provenance tables (`crates/trust-ir-conformance/tests/lean_exec_differential.rs`),
computed in the reference placement (`Memory.alloc`); placement itself is a
property of the two reference models, not a format rule.
-/

theorem PermissionMap.get_set_ne (pm : PermissionMap) (id id' : AllocId) (p : Permission)
    (h : id' ≠ id) : (pm.set id p).get id' = pm.get id' := by
  simp [PermissionMap.set, PermissionMap.get, h]

/-- The borrow operand rule, characterized: it reads the state, changes
    nothing, and answers `endBorrowTarget` of the operand. -/
theorem borrowOperand_ok_inv (op : String) (v : Value) (s s' : MachineState)
    (t : Option AllocId) (h : StateT.run (borrowOperand op v) s = .ok (t, s')) :
    s' = s ∧ t = endBorrowTarget s.memory v := by
  unfold borrowOperand at h
  rw [sr_bind, sr_get] at h
  simp only [Except.bind] at h
  match v, h with
  | .ptr addr (some id), h =>
    rw [sr_pure] at h; cases h; exact ⟨rfl, rfl⟩
  | .ptr addr none, h =>
    rw [sr_ite] at h; split at h <;> cases h
  | .nullPtr, h => cases h
  | .int .., h | .float .., h | .bool .., h | .aggregate .., h | .vector .., h | .frame .., h
  | .set .., h | .sequence .., h | .record .., h | .closure .., h | .typedClosure .., h | .fatPtr .., h
  | .partial .., h | .undef .., h | .uninit, h => cases h

theorem getPermission_ok_inv (id : AllocId) (s s' : MachineState) (p : Permission)
    (h : StateT.run (getPermission id) s = .ok (p, s')) :
    s' = s ∧ s.permissions.get id = some p := by
  unfold getPermission at h
  rw [sr_bind, sr_get] at h
  simp only [Except.bind] at h
  split at h
  · rename_i perm hperm
    rw [sr_pure] at h; cases h; exact ⟨rfl, hperm⟩
  · cases h

theorem sr_setPermission (id : AllocId) (p : Permission) (s : MachineState) :
    StateT.run (setPermission id p) s = .ok ((), { s with permissions := s.permissions.set id p }) :=
  rfl

/-- **`Borrow` moves only its operand's target.** A successful `Borrow`
    changes no memory, no reference count and no global, and no permission
    but that of the allocation its operand names by the borrow operand rule
    (`endBorrowTarget`: a thin provenance pointer inside the live
    allocation's requested bytes) — never a neighbour's. -/
theorem semBorrow_frame (ptrId : ValueId) (s s' : MachineState) (r : ValueId)
    (h : Sem.run (semBorrow ptrId) s = .ok (r, s')) :
    s'.memory = s.memory ∧ s'.refCounts = s.refCounts ∧ s'.globals = s.globals ∧
    ∃ v, s.lookupValue ptrId = some v ∧
      ∀ id, endBorrowTarget s.memory v ≠ some id → s'.permissions.get id = s.permissions.get id := by
  unfold semBorrow at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  rcases hv : s.lookupValue ptrId with _ | v
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Except.bind] at h
  split at h
  · rw [sr_bindFresh] at h
    cases h
    exact ⟨rfl, rfl, rfl, _, rfl, fun _ _ => rfl⟩
  · rw [sr_bind] at h
    rcases hb : StateT.run (borrowOperand "Borrow" v) s with e | ⟨t, s1⟩
    · rw [hb] at h; cases h
    obtain ⟨hs1, ht⟩ := borrowOperand_ok_inv _ _ _ _ _ hb
    subst s1
    rw [hb] at h
    simp only [Except.bind] at h
    split at h
    · rw [sr_bindFresh] at h
      cases h
      exact ⟨rfl, rfl, rfl, _, rfl, fun _ _ => rfl⟩
    · rename_i allocId
      rw [sr_bind] at h
      rcases hg : StateT.run (getPermission allocId) s with e | ⟨perm, s2⟩
      · rw [hg] at h; cases h
      obtain ⟨hs2, -⟩ := getPermission_ok_inv _ _ _ _ hg
      subst s2
      rw [hg] at h
      simp only [Except.bind] at h
      have hframe : ∀ (p : Permission) id, endBorrowTarget s.memory v ≠ some id →
          (s.permissions.set allocId p).get id = s.permissions.get id := by
        intro p id hid
        apply PermissionMap.get_set_ne
        intro heq; subst heq; exact hid ht.symm
      split at h
      · rw [sr_bind, sr_setPermission] at h
        simp only [Except.bind] at h
        rw [sr_bindFresh] at h
        cases h
        exact ⟨rfl, rfl, rfl, _, rfl, hframe _⟩
      · rw [sr_bind, sr_setPermission] at h
        simp only [Except.bind] at h
        rw [sr_bindFresh] at h
        cases h
        exact ⟨rfl, rfl, rfl, _, rfl, hframe _⟩
      · cases h


/-- **`BorrowMut` moves only its operand's target** (as `semBorrow_frame`). -/
theorem semBorrowMut_frame (ptrId : ValueId) (s s' : MachineState) (r : ValueId)
    (h : Sem.run (semBorrowMut ptrId) s = .ok (r, s')) :
    s'.memory = s.memory ∧ s'.refCounts = s.refCounts ∧ s'.globals = s.globals ∧
    ∃ v, s.lookupValue ptrId = some v ∧
      ∀ id, endBorrowTarget s.memory v ≠ some id → s'.permissions.get id = s.permissions.get id := by
  unfold semBorrowMut at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  rcases hv : s.lookupValue ptrId with _ | v
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Except.bind] at h
  split at h
  · rw [sr_bindFresh] at h
    cases h
    exact ⟨rfl, rfl, rfl, _, rfl, fun _ _ => rfl⟩
  · rw [sr_bind] at h
    rcases hb : StateT.run (borrowOperand "Borrow" v) s with e | ⟨t, s1⟩
    · rw [hb] at h; cases h
    obtain ⟨hs1, ht⟩ := borrowOperand_ok_inv _ _ _ _ _ hb
    subst s1
    rw [hb] at h
    simp only [Except.bind] at h
    split at h
    · rw [sr_bindFresh] at h
      cases h
      exact ⟨rfl, rfl, rfl, _, rfl, fun _ _ => rfl⟩
    · rename_i allocId
      rw [sr_bind] at h
      rcases hg : StateT.run (getPermission allocId) s with e | ⟨perm, s2⟩
      · rw [hg] at h; cases h
      obtain ⟨hs2, -⟩ := getPermission_ok_inv _ _ _ _ hg
      subst s2
      rw [hg] at h
      simp only [Except.bind] at h
      split at h
      · rw [sr_bind, sr_setPermission] at h
        simp only [Except.bind] at h
        rw [sr_bindFresh] at h
        cases h
        refine ⟨rfl, rfl, rfl, _, rfl, fun id hid => ?_⟩
        apply PermissionMap.get_set_ne
        intro heq; subst heq; exact hid ht.symm
      · cases h

/-- **`EndBorrow` moves only its operand's target**: no memory, reference
    count, global or SSA value changes, and no permission but that of the
    allocation `endBorrowTarget` names. -/
theorem semEndBorrow_frame (ptrId : ValueId) (s s' : MachineState)
    (h : Sem.run (semEndBorrow ptrId) s = .ok ((), s')) :
    s'.memory = s.memory ∧ s'.refCounts = s.refCounts ∧ s'.globals = s.globals ∧
    s'.locals = s.locals ∧
    ∃ v, s.lookupValue ptrId = some v ∧
      ∀ id, endBorrowTarget s.memory v ≠ some id → s'.permissions.get id = s.permissions.get id := by
  unfold semEndBorrow at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  rcases hv : s.lookupValue ptrId with _ | v
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Except.bind, sr_bind, sr_get] at h
  split at h
  · rw [sr_pure] at h; cases h
    exact ⟨rfl, rfl, rfl, rfl, _, rfl, fun _ _ => rfl⟩
  · rename_i allocId ht
    rw [sr_bind] at h
    rcases hg : StateT.run (getPermission allocId) s with e | ⟨perm, s2⟩
    · rw [hg] at h; cases h
    obtain ⟨hs2, -⟩ := getPermission_ok_inv _ _ _ _ hg
    subst s2
    rw [hg] at h
    simp only [Except.bind] at h
    have hframe : ∀ (p : Permission) id, endBorrowTarget s.memory v ≠ some id →
        (s.permissions.set allocId p).get id = s.permissions.get id := by
      intro p id hid
      apply PermissionMap.get_set_ne
      intro heq; subst heq; exact hid ht
    split at h
    · split at h
      · cases h
      · rw [sr_setPermission] at h; cases h
        exact ⟨rfl, rfl, rfl, rfl, _, rfl, hframe _⟩
      · rw [sr_setPermission] at h; cases h
        exact ⟨rfl, rfl, rfl, rfl, _, rfl, hframe _⟩
    · rw [sr_setPermission] at h; cases h
      exact ⟨rfl, rfl, rfl, rfl, _, rfl, hframe _⟩
    · cases h

/-- A thin provenance pointer outside its allocation's requested bytes — one
    past the end, in the heap slack tail, in a zero-size or freed allocation —
    is passed through by `Borrow`, which moves nothing at all. -/
theorem semBorrow_outside_requested_is_identity (ptrId : ValueId) (s : MachineState)
    (a : Addr) (id : AllocId)
    (hp : s.lookupValue ptrId = some (.ptr a (some id)))
    (hOut : s.memory.borrowTarget a id = none) :
    Sem.run (semBorrow ptrId) s = .ok (s.bindValue (.ptr a (some id))) := by
  unfold semBorrow
  simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind]
  unfold borrowOperand
  simp only [sr_bind, sr_get, Except.bind, sr_pure, hOut]
  rfl

/-- The `EndBorrow` twin: an operand outside its allocation's requested
    bytes ends nothing and leaves the state exactly as it was. -/
theorem semEndBorrow_outside_requested_is_noop (ptrId : ValueId) (s : MachineState)
    (v : Value) (hp : s.lookupValue ptrId = some v)
    (hOut : endBorrowTarget s.memory v = none) :
    Sem.run (semEndBorrow ptrId) s = .ok ((), s) := by
  unfold semEndBorrow
  simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind, sr_get, hOut, sr_pure]

/-- The ARC operand rule, characterized: it reads the state, changes
    nothing, and answers the provenance of a pointer whose allocation is
    known and live. -/
theorem getAllocIdFromPtrARC_ok_inv (v : Value) (s s' : MachineState) (id : AllocId)
    (h : StateT.run (getAllocIdFromPtrARC v) s = .ok (id, s')) :
    s' = s ∧ ∃ a alloc, v = .ptr a (some id) ∧ s.memory.lookup id = some alloc ∧
      alloc.alive = true := by
  unfold getAllocIdFromPtrARC at h
  rw [sr_bind, sr_get] at h
  simp only [Except.bind] at h
  match v, h with
  | .ptr addr (some pid), h =>
    simp only [] at h
    rcases hl : s.memory.lookup pid with _ | alloc
    · rw [hl, sr_throwUB] at h; cases h
    · rw [hl] at h
      simp only [] at h
      rw [sr_ite] at h
      split at h
      · rename_i hAlive
        rw [sr_pure] at h; cases h
        exact ⟨rfl, addr, alloc, rfl, hl, hAlive⟩
      · cases h
  | .ptr addr none, h =>
    simp only [] at h
    rw [sr_ite] at h; split at h <;> cases h
  | .nullPtr, h => cases h
  | .int .., h | .float .., h | .bool .., h | .aggregate .., h | .vector .., h | .frame .., h
  | .set .., h | .sequence .., h | .record .., h | .closure .., h | .typedClosure .., h | .fatPtr .., h
  | .partial .., h | .undef .., h | .uninit, h => cases h

theorem requireArcRef_ok_inv (id : AllocId) (s s' : MachineState) (u : Unit)
    (h : StateT.run (requireArcRef id) s = .ok (u, s')) :
    s' = s ∧ s.permissions.get id = some .arcRef := by
  unfold requireArcRef at h
  rw [sr_bind, sr_get] at h
  simp only [Except.bind] at h
  split at h
  · rename_i hp; rw [sr_pure] at h; cases h; exact ⟨rfl, hp⟩
  · cases h
  · cases h

/-- A successful object-base check changed nothing, and its operand is a
    pointer at the base of the allocation it names. -/
theorem requireObjectBase_ok_inv (op : String) (v : Value) (id : AllocId)
    (s s' : MachineState) (u : Unit)
    (h : StateT.run (requireObjectBase op v id) s = .ok (u, s')) :
    s' = s ∧ ∃ addr p alloc, v = .ptr addr p ∧ s.memory.lookup id = some alloc ∧
      addr = alloc.base := by
  unfold requireObjectBase at h
  rw [sr_bind, sr_get] at h
  simp only [Except.bind] at h
  rcases hl : s.memory.lookup id with _ | alloc
  · rw [hl] at h
    cases v <;> cases h
  · rw [hl] at h
    cases v <;> try cases h
    rename_i addr p
    simp only [] at h
    rw [sr_ite] at h
    split at h
    · rename_i hb
      rw [sr_pure] at h; cases h
      exact ⟨rfl, addr, p, alloc, rfl, rfl, by simpa using hb⟩
    · cases h

/-- **`Retain` counts only its provenance.** A successful `Retain` went
    through a pointer derived from a live `arcRef` allocation `id`, and
    changes no memory, permission, SSA value or global, and no reference count
    but `id`'s. -/
theorem semRetain_frame (ptrId : ValueId) (s s' : MachineState)
    (h : Sem.run (semRetain ptrId) s = .ok ((), s')) :
    ∃ a id, s.lookupValue ptrId = some (.ptr a (some id)) ∧
      s'.memory = s.memory ∧ s'.permissions = s.permissions ∧ s'.locals = s.locals ∧
      s'.globals = s.globals ∧ ∀ id', id' ≠ id → s'.refCounts id' = s.refCounts id' := by
  unfold semRetain at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  rcases hv : s.lookupValue ptrId with _ | v
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Except.bind] at h
  rcases hg : StateT.run (getAllocIdFromPtrARC v) s with e | ⟨id, s1⟩
  · rw [hg] at h; cases h
  obtain ⟨hs1, a, alloc, rfl, -, -⟩ := getAllocIdFromPtrARC_ok_inv _ _ _ _ hg
  subst s1
  rw [hg] at h
  simp only [Except.bind] at h
  rcases hr : StateT.run (requireArcRef id) s with e | ⟨u, s2⟩
  · rw [hr] at h; cases h
  obtain ⟨hs2, -⟩ := requireArcRef_ok_inv _ _ _ _ hr
  subst s2
  rw [hr] at h
  simp only [Except.bind] at h
  rcases hb : StateT.run (requireObjectBase _ _ id) s with e | ⟨u', s3⟩
  · rw [hb] at h; cases h
  obtain ⟨hs3, -⟩ := requireObjectBase_ok_inv _ _ _ _ _ _ hb
  subst s3
  rw [hb] at h
  simp only [Except.bind, sr_get, sr_set] at h
  cases h
  refine ⟨a, id, rfl, rfl, rfl, rfl, rfl, fun id' hne => ?_⟩
  simp [setRefCount, hne]

/-- **`IsUnique` reads only its provenance**: it changes no memory,
    permission, reference count or global. -/
theorem semIsUnique_frame (ptrId : ValueId) (s s' : MachineState) (r : ValueId)
    (h : Sem.run (semIsUnique ptrId) s = .ok (r, s')) :
    ∃ a id, s.lookupValue ptrId = some (.ptr a (some id)) ∧
      s'.memory = s.memory ∧ s'.permissions = s.permissions ∧ s'.refCounts = s.refCounts ∧
      s'.globals = s.globals := by
  unfold semIsUnique at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  rcases hv : s.lookupValue ptrId with _ | v
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Except.bind] at h
  rcases hg : StateT.run (getAllocIdFromPtrARC v) s with e | ⟨id, s1⟩
  · rw [hg] at h; cases h
  obtain ⟨hs1, a, alloc, rfl, -, -⟩ := getAllocIdFromPtrARC_ok_inv _ _ _ _ hg
  subst s1
  rw [hg] at h
  simp only [Except.bind] at h
  rcases hr : StateT.run (requireArcRef id) s with e | ⟨u, s2⟩
  · rw [hr] at h; cases h
  obtain ⟨hs2, -⟩ := requireArcRef_ok_inv _ _ _ _ hr
  subst s2
  rw [hr] at h
  simp only [Except.bind] at h
  rcases hb : StateT.run (requireObjectBase _ _ id) s with e | ⟨u', s3⟩
  · rw [hb] at h; cases h
  obtain ⟨hs3, -⟩ := requireObjectBase_ok_inv _ _ _ _ _ _ hb
  subst s3
  rw [hb] at h
  simp only [Except.bind, sr_get, sr_bindFresh] at h
  cases h
  exact ⟨a, id, rfl, rfl, rfl, rfl, rfl⟩

/-- **`Release` touches only its provenance.** A successful `Release` went
    through a pointer derived from a live `arcRef` allocation `id`; every
    other allocation keeps its record, permission and reference count, the
    bytes and SSA values are unchanged. -/
theorem semRelease_frame (ptrId : ValueId) (s s' : MachineState)
    (h : Sem.run (semRelease ptrId) s = .ok ((), s')) :
    ∃ a id, s.lookupValue ptrId = some (.ptr a (some id)) ∧
      s'.memory.bytes = s.memory.bytes ∧ s'.locals = s.locals ∧ s'.globals = s.globals ∧
      ∀ id', id' ≠ id →
        s'.memory.lookup id' = s.memory.lookup id' ∧
        s'.permissions.get id' = s.permissions.get id' ∧
        s'.refCounts id' = s.refCounts id' := by
  unfold semRelease at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  rcases hv : s.lookupValue ptrId with _ | v
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Except.bind] at h
  rcases hg : StateT.run (getAllocIdFromPtrARC v) s with e | ⟨id, s1⟩
  · rw [hg] at h; cases h
  obtain ⟨hs1, a, alloc, rfl, -, -⟩ := getAllocIdFromPtrARC_ok_inv _ _ _ _ hg
  subst s1
  rw [hg] at h
  simp only [Except.bind] at h
  rcases hr : StateT.run (requireArcRef id) s with e | ⟨u, s2⟩
  · rw [hr] at h; cases h
  obtain ⟨hs2, -⟩ := requireArcRef_ok_inv _ _ _ _ hr
  subst s2
  rw [hr] at h
  simp only [Except.bind] at h
  rcases hb : StateT.run (requireObjectBase _ _ id) s with e | ⟨u', s3⟩
  · rw [hb] at h; cases h
  obtain ⟨hs3, -⟩ := requireObjectBase_ok_inv _ _ _ _ _ _ hb
  subst s3
  rw [hb] at h
  simp only [Except.bind, sr_get] at h
  refine ⟨a, id, rfl, ?_⟩
  revert h
  generalize getRefCount s.refCounts id = count
  intro h
  match count, h with
  | 0, h => cases h
  | 1, h =>
    unfold deallocARC at h
    rw [sr_bind, sr_get] at h
    simp only [Except.bind] at h
    rw [sr_ite] at h
    split at h
    · cases h
    · rw [sr_set] at h; cases h
      refine ⟨rfl, rfl, rfl, fun id' hne => ⟨?_, ?_, ?_⟩⟩
      · simp only [Memory.lookup]
        rw [find?_map_alloc]
        have hcongr : (fun x : Allocation =>
            (if x.id == id then { x with alive := false } else x).id == id')
            = (fun x => x.id == id') := by
          funext x; by_cases hx : (x.id == id) = true <;> simp [hx]
        rw [hcongr]
        cases hf : s.memory.allocations.find? (fun x => x.id == id') with
        | none => rfl
        | some b =>
          have hb := find?_some_pred hf
          simp only [beq_iff_eq] at hb
          have hbid : b.id ≠ id := by rw [hb]; exact hne
          simp [hbid]
      · simp [clearPermission, PermissionMap.get, hne]
      · simp [setRefCount, hne]
  | n + 2, h =>
    rw [sr_set] at h; cases h
    exact ⟨rfl, rfl, rfl, fun id' hne => ⟨rfl, rfl, by simp [setRefCount, hne]⟩⟩

/-- **`Dealloc` frees its provenance, and only it.** A successful `Dealloc`
    names the allocation its pointer was derived from, at that allocation's
    base, marks exactly it dead, and leaves every other allocation's record
    as it was — even one that starts at the same address. -/
theorem semDealloc_frees_its_provenance (ptrId : ValueId) (s s' : MachineState)
    (h : Sem.run (semDealloc ptrId) s = .ok ((), s')) :
    ∃ alloc : Allocation, s.lookupValue ptrId = some (.ptr alloc.base (some alloc.id)) ∧
      s'.memory.lookup alloc.id = some { alloc with alive := false } ∧
      ∀ id', id' ≠ alloc.id → s'.memory.lookup id' = s.memory.lookup id' := by
  obtain ⟨addr, alloc, _, hp, hl, -, hBase, -, -, hs', -, -, -⟩ :=
    semDealloc_marks_dead ptrId s s' h
  subst hBase
  refine ⟨alloc, hp, ?_, fun id' hne => ?_⟩
  · rw [hs']
    simp only [Memory.lookup]
    rw [find?_map_alloc]
    have hcongr : (fun x : Allocation =>
        (if x.id == alloc.id then { x with alive := false } else x).id == alloc.id)
        = (fun x => x.id == alloc.id) := by
      funext x; by_cases hx : (x.id == alloc.id) = true <;> simp [hx]
    rw [hcongr]
    have hl' : s.memory.allocations.find? (fun x => x.id == alloc.id) = some alloc := hl
    rw [hl']
    simp
  · rw [hs']
    simp only [Memory.lookup]
    rw [find?_map_alloc]
    have hcongr : (fun x : Allocation =>
        (if x.id == alloc.id then { x with alive := false } else x).id == id')
        = (fun x => x.id == id') := by
      funext x; by_cases hx : (x.id == alloc.id) = true <;> simp [hx]
    rw [hcongr]
    cases hf : s.memory.allocations.find? (fun x => x.id == id') with
    | none => rfl
    | some b =>
      have hb := find?_some_pred hf
      simp only [beq_iff_eq] at hb
      have hbid : b.id ≠ alloc.id := by rw [hb]; exact hne
      simp [hbid]

/-- **The integer-to-address conversion** (`Sem.addrOfInt`, the
    interpreter's `int.as_unsigned()` + `u64::try_from`): a successful
    conversion is the unsigned value of the integer at its source width, it is
    below 2^64, and the state is untouched. -/
theorem addrOfInt_lt_two_pow_64 (op : String) (w : Nat) (v : Int) (s s' : MachineState)
    (a : Nat) (h : StateT.run (Sem.addrOfInt op w v) s = .ok (a, s')) :
    a = (v % 2 ^ w).toNat ∧ a < 2 ^ 64 ∧ s' = s := by
  unfold Sem.addrOfInt at h
  simp only [] at h
  rw [sr_ite] at h
  split at h
  · rename_i hlt; rw [sr_pure] at h; cases h; exact ⟨rfl, hlt, rfl⟩
  · cases h


-- -----------------------------------------------------------------
-- Concrete instances: the decided cells
-- -----------------------------------------------------------------

-- Name the concrete allocation transitions before reducing the remaining
-- memory operations. This shares their checked execution and keeps the
-- closed witnesses within the ordinary kernel reduction budget.
private def stackAllocationResult (before : MachineState) (size alignment : Nat) :
    ValueId × MachineState :=
  let id := AllocId.mk before.memory.nextAllocId
  let (address, memory) := before.memory.alloc size alignment 0 .rustStack
  let allocated : MachineState :=
    { before with
      memory := memory
      permissions := before.permissions.set id .owned }
  allocated.bindValue (.ptr address (some id))

-- Independently named ground transitions for these fixtures. They describe
-- actual operation results; each equation below is checked by reflexivity.
private def provenanceStack32Result : ValueId × MachineState :=
  let before := MachineState.empty
  let id := AllocId.mk before.memory.nextAllocId
  let (address, memory) := before.memory.alloc 4 4 0 .rustStack
  let allocated : MachineState :=
    { before with memory := memory, permissions := before.permissions.set id .owned }
  allocated.bindValue (.ptr address (some id))

private def provenanceStack64Result : ValueId × MachineState :=
  let before := MachineState.empty
  let id := AllocId.mk before.memory.nextAllocId
  let (address, memory) := before.memory.alloc 8 8 0 .rustStack
  let allocated : MachineState :=
    { before with memory := memory, permissions := before.permissions.set id .owned }
  allocated.bindValue (.ptr address (some id))

private def provenanceStack32SecondResult : ValueId × MachineState :=
  let before := provenanceStack32Result.2
  let id := AllocId.mk before.memory.nextAllocId
  let (address, memory) := before.memory.alloc 4 4 0 .rustStack
  let allocated : MachineState :=
    { before with memory := memory, permissions := before.permissions.set id .owned }
  allocated.bindValue (.ptr address (some id))

private theorem provenanceStack32_run :
    StateT.run (semAlloca .I32 none) MachineState.empty =
      .ok provenanceStack32Result := rfl

private theorem provenanceStack64_run :
    StateT.run (semAlloca .I64 none) MachineState.empty =
      .ok provenanceStack64Result := rfl

private theorem provenanceStack32Second_run :
    StateT.run (semAlloca .I32 none) provenanceStack32Result.2 =
      .ok provenanceStack32SecondResult := rfl

private def provenanceNegativeIntResult : ValueId × MachineState :=
  MachineState.empty.bindValue (.int 64 (-8))

private def provenanceNegativePointerResult : ValueId × MachineState :=
  provenanceNegativeIntResult.2.bindValue (.ptr (2 ^ 64 - 8) none)

private theorem provenanceNegativeInt_run :
    StateT.run (Sem.bindFresh (.int 64 (-8))) MachineState.empty =
      .ok provenanceNegativeIntResult := rfl

private theorem provenanceNegativePointer_run :
    StateT.run (semCast .IntToPtr .I64 .Ptr provenanceNegativeIntResult.1)
      provenanceNegativeIntResult.2 = .ok provenanceNegativePointerResult := rfl

private theorem provenanceNegativeLookup_run :
    StateT.run (Sem.lookupValue provenanceNegativePointerResult.1)
      provenanceNegativePointerResult.2 =
      .ok (.ptr (2 ^ 64 - 8) none, provenanceNegativePointerResult.2) := rfl

#trustIrAxiomsExact provenanceStack32_run == []
#trustIrAxiomsExact provenanceStack64_run == []
#trustIrAxiomsExact provenanceStack32Second_run == []
#trustIrAxiomsExact provenanceNegativeInt_run == []
#print axioms provenanceNegativePointer_run
#trustIrAxioms provenanceNegativePointer_run <= [propext, Classical.choice, Quot.sound]
#trustIrAxiomsExact provenanceNegativeLookup_run == []

-- Ground transitions for the remaining five concrete controls.
private def provenanceUnitResult : ValueId × MachineState :=
  stackAllocationResult MachineState.empty 0 1

private theorem provenanceUnit_run :
    StateT.run (semAlloca .Unit none) MachineState.empty =
      .ok provenanceUnitResult := rfl

private def provenanceUnit32Result : ValueId × MachineState :=
  stackAllocationResult provenanceUnitResult.2 4 4

private theorem provenanceUnit32_run :
    StateT.run (semAlloca .I32 none) provenanceUnitResult.2 =
      .ok provenanceUnit32Result := rfl

private def provenanceBorrowedUnit32Result : ValueId × MachineState :=
  let before := provenanceUnit32Result.2
  let borrowed : MachineState := { before with permissions := before.permissions.set ⟨1⟩ (.sharedBorrow 1) }
  borrowed.bindValue (.ptr 1028 (some ⟨1⟩))

private theorem provenanceBorrowedUnit32_run :
    StateT.run (semBorrow provenanceUnit32Result.1) provenanceUnit32Result.2 =
      .ok provenanceBorrowedUnit32Result := rfl

private def provenanceFreedUnit32State : MachineState :=
  let before := provenanceBorrowedUnit32Result.2
  let id := AllocId.mk 0
  let allocations := before.memory.allocations.map
    (fun allocation => if allocation.id == id then { allocation with alive := false } else allocation)
  let memory := { before.memory with allocations := allocations }
  { before with memory := memory, permissions := clearPermissionAt before.permissions id, refCounts := clearRefCountAt before.refCounts id }

private theorem provenanceFreedUnit32_run :
    StateT.run (semDealloc provenanceUnitResult.1) provenanceBorrowedUnit32Result.2 =
      .ok ((), provenanceFreedUnit32State) := rfl

private theorem provenanceUnit32Permission_run :
    StateT.run (getPermission ⟨1⟩) provenanceFreedUnit32State =
      .ok (.sharedBorrow 1, provenanceFreedUnit32State) := rfl

private theorem provenanceUnit32GetState_run :
    StateT.run Sem.getState provenanceFreedUnit32State =
      .ok (provenanceFreedUnit32State, provenanceFreedUnit32State) := rfl

private theorem provenanceUnit32Observation :
    (Permission.sharedBorrow 1, (provenanceFreedUnit32State.memory.lookup ⟨0⟩).map (·.alive), (provenanceFreedUnit32State.memory.lookup ⟨1⟩).map (·.alive)) =
      (.sharedBorrow 1, some false, some true) := rfl

private def provenanceOneAfterTwo32Result : ValueId × MachineState :=
  provenanceStack32SecondResult.2.bindValue (.int 64 1)

private theorem provenanceOneAfterTwo32_run :
    StateT.run (Sem.bindFresh (.int 64 1)) provenanceStack32SecondResult.2 =
      .ok provenanceOneAfterTwo32Result := rfl

private def provenancePast32Result : ValueId × MachineState :=
  provenanceOneAfterTwo32Result.2.bindValue (.ptr 1028 (some ⟨0⟩))

private theorem provenancePast32GEP_run :
    StateT.run (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 provenanceStack32Result.1 [provenanceOneAfterTwo32Result.1]) provenanceOneAfterTwo32Result.2 =
      .ok provenancePast32Result := rfl

private theorem provenancePast32Dealloc_run :
    StateT.run (semDealloc provenancePast32Result.1) provenancePast32Result.2 =
      .error (.ub "Dealloc: pointer must reference allocation base") := rfl

private def provenanceByteResult : ValueId × MachineState :=
  stackAllocationResult MachineState.empty 1 1

private theorem provenanceByte_run :
    StateT.run (semAlloca .I8 none) MachineState.empty =
      .ok provenanceByteResult := rfl

private def provenanceByte32Result : ValueId × MachineState :=
  stackAllocationResult provenanceByteResult.2 4 4

private theorem provenanceByte32_run :
    StateT.run (semAlloca .I32 none) provenanceByteResult.2 =
      .ok provenanceByte32Result := rfl

private def provenanceByteSevenResult : ValueId × MachineState :=
  provenanceByte32Result.2.bindValue (.int 32 7)

private theorem provenanceByteSeven_run :
    StateT.run (Sem.bindFresh (.int 32 7)) provenanceByte32Result.2 =
      .ok provenanceByteSevenResult := rfl

private def provenanceByteStoredState : MachineState :=
  let before := provenanceByteSevenResult.2
  { before with memory := before.memory.writeBytes 1028 (encodeIntBytes 7 4) }

private theorem provenanceByteStore_run :
    StateT.run (semStore .I32 provenanceByte32Result.1 provenanceByteSevenResult.1 false (some 4)) provenanceByteSevenResult.2 =
      .ok ((), provenanceByteStoredState) := rfl

private def provenanceByteLoadedResult : ValueId × MachineState :=
  provenanceByteStoredState.bindValue (.int 32 7)

private theorem provenanceByteLoad_run :
    StateT.run (semLoad .I32 provenanceByte32Result.1 false (some 4)) provenanceByteStoredState =
      .ok provenanceByteLoadedResult := rfl

private theorem provenanceByteLookup_run :
    StateT.run (Sem.lookupValue provenanceByteLoadedResult.1) provenanceByteLoadedResult.2 =
      .ok (.int 32 7, provenanceByteLoadedResult.2) := rfl

private def provenanceTwoSevenResult : ValueId × MachineState :=
  provenanceStack32SecondResult.2.bindValue (.int 32 7)

private theorem provenanceTwoSeven_run :
    StateT.run (Sem.bindFresh (.int 32 7)) provenanceStack32SecondResult.2 =
      .ok provenanceTwoSevenResult := rfl

private def provenanceTwoStoredState : MachineState :=
  let before := provenanceTwoSevenResult.2
  { before with memory := before.memory.writeBytes 1028 (encodeIntBytes 7 4) }

private theorem provenanceTwoStore_run :
    StateT.run (semStore .I32 provenanceStack32SecondResult.1 provenanceTwoSevenResult.1) provenanceTwoSevenResult.2 =
      .ok ((), provenanceTwoStoredState) := rfl

private def provenanceStoredOneResult : ValueId × MachineState :=
  provenanceTwoStoredState.bindValue (.int 64 1)

private theorem provenanceStoredOne_run :
    StateT.run (Sem.bindFresh (.int 64 1)) provenanceTwoStoredState =
      .ok provenanceStoredOneResult := rfl

private def provenanceStoredPastResult : ValueId × MachineState :=
  provenanceStoredOneResult.2.bindValue (.ptr 1028 (some ⟨0⟩))

private theorem provenanceStoredPastGEP_run :
    StateT.run (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 provenanceStack32Result.1 [provenanceStoredOneResult.1]) provenanceStoredOneResult.2 =
      .ok provenanceStoredPastResult := rfl

private theorem provenanceStoredPastLoad_run :
    StateT.run (semLoad .I32 provenanceStoredPastResult.1) provenanceStoredPastResult.2 =
      .error (.ub "Load: access is out of bounds") := rfl

private def provenance64ZeroResult : ValueId × MachineState :=
  provenanceStack64Result.2.bindValue (.int 64 0)

private theorem provenance64Zero_run :
    StateT.run (Sem.bindFresh (.int 64 0)) provenanceStack64Result.2 =
      .ok provenance64ZeroResult := rfl

private def provenance64StoredState : MachineState :=
  let before := provenance64ZeroResult.2
  { before with memory := before.memory.writeBytes 1024 (encodeIntBytes 0 8) }

set_option maxRecDepth 4096 in
private theorem provenance64Store_run :
    StateT.run (semStore .I64 provenanceStack64Result.1 provenance64ZeroResult.1) provenance64ZeroResult.2 =
      .ok ((), provenance64StoredState) := rfl

private def provenance64OneResult : ValueId × MachineState :=
  provenance64StoredState.bindValue (.int 64 1)

private theorem provenance64One_run :
    StateT.run (Sem.bindFresh (.int 64 1)) provenance64StoredState =
      .ok provenance64OneResult := rfl

private def provenanceMisalignedResult : ValueId × MachineState :=
  provenance64OneResult.2.bindValue (.ptr 1025 (some ⟨0⟩))

private theorem provenanceMisalignedGEP_run :
    StateT.run (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 provenanceStack64Result.1 [provenance64OneResult.1]) provenance64OneResult.2 =
      .ok provenanceMisalignedResult := rfl

private theorem provenanceMisalignedLoad_run :
    StateT.run (semLoad .I32 provenanceMisalignedResult.1) provenanceMisalignedResult.2 =
      .error (.ub "Load: pointer address 1025 is not aligned to 4") := rfl

#trustIrAxiomsExact provenanceUnit_run == []
#trustIrAxiomsExact provenanceUnit32_run == []
#trustIrAxiomsExact provenanceBorrowedUnit32_run == []
#trustIrAxiomsExact provenanceFreedUnit32_run == []
#trustIrAxiomsExact provenanceUnit32Permission_run == []
#trustIrAxiomsExact provenanceUnit32GetState_run == []
#trustIrAxiomsExact provenanceUnit32Observation == []
#trustIrAxiomsExact provenanceOneAfterTwo32_run == []
#print axioms provenancePast32GEP_run
#trustIrAxioms provenancePast32GEP_run <= [propext, Classical.choice, Quot.sound]
#trustIrAxiomsExact provenancePast32Dealloc_run == []
#trustIrAxiomsExact provenanceByte_run == []
#trustIrAxiomsExact provenanceByte32_run == []
#trustIrAxiomsExact provenanceByteSeven_run == []
#print axioms provenanceByteStore_run
#trustIrAxioms provenanceByteStore_run <= [propext, Classical.choice, Quot.sound]
#print axioms provenanceByteLoad_run
#trustIrAxioms provenanceByteLoad_run <= [propext, Classical.choice, Quot.sound]
#trustIrAxiomsExact provenanceByteLookup_run == []
#trustIrAxiomsExact provenanceTwoSeven_run == []
#print axioms provenanceTwoStore_run
#trustIrAxioms provenanceTwoStore_run <= [propext, Classical.choice, Quot.sound]
#trustIrAxiomsExact provenanceStoredOne_run == []
#print axioms provenanceStoredPastGEP_run
#trustIrAxioms provenanceStoredPastGEP_run <= [propext, Classical.choice, Quot.sound]
#print axioms provenanceStoredPastLoad_run
#trustIrAxioms provenanceStoredPastLoad_run <= [propext, Classical.choice, Quot.sound]
#trustIrAxiomsExact provenance64Zero_run == []
#print axioms provenance64Store_run
#trustIrAxioms provenance64Store_run <= [propext, Classical.choice, Quot.sound]
#trustIrAxiomsExact provenance64One_run == []
#print axioms provenanceMisalignedGEP_run
#trustIrAxioms provenanceMisalignedGEP_run <= [propext, Classical.choice, Quot.sound]
#print axioms provenanceMisalignedLoad_run
#trustIrAxioms provenanceMisalignedLoad_run <= [propext, Classical.choice, Quot.sound]

private theorem alloca32_empty : StateT.run (semAlloca .I32 none) MachineState.empty =
    .ok (stackAllocationResult MachineState.empty 4 4) := by
      trustIrCompilerProof {
        rfl
      } {
        change StateT.run (semAlloca .I32 none) MachineState.empty =
          .ok provenanceStack32Result
        exact provenanceStack32_run
      }
private theorem alloca64_empty : StateT.run (semAlloca .I64 none) MachineState.empty =
    .ok (stackAllocationResult MachineState.empty 8 8) := by
      trustIrCompilerProof {
        rfl
      } {
        change StateT.run (semAlloca .I64 none) MachineState.empty =
          .ok provenanceStack64Result
        exact provenanceStack64_run
      }
private theorem alloca32_second :
    StateT.run (semAlloca .I32 none) (stackAllocationResult MachineState.empty 4 4).2 =
    .ok (stackAllocationResult (stackAllocationResult MachineState.empty 4 4).2 4 4) := by
      trustIrCompilerProof {
        rfl
      } {
        change StateT.run (semAlloca .I32 none) provenanceStack32Result.2 =
          .ok provenanceStack32SecondResult
        exact provenanceStack32Second_run
      }

/-- Family (c) of the SPEC borrow section's clause 2, decided: an address
    computed through an integer recovers the allocation of the ONE layout.
    `a = alloca i8`, `b = alloca i32`, `c = alloca i32`; the reference
    placement aligns `b` to 4, so `inttoptr(ptrtoint a + 5)` is address 1029,
    inside `b` = [1028, 1032), and recovers `b`'s provenance — as in the
    interpreter (`IntToPtrAcrossLayouts`). -/
theorem inttoptr_resolves_in_the_one_layout :
    (match Sem.run (do
        let a ← semAlloca .I8 none
        let _b ← semAlloca .I32 none
        let _c ← semAlloca .I32 none
        let ai ← semCast .PtrToInt .Ptr .U64 a
        let five ← Sem.bindFresh (.int 64 5)
        let sum ← semBinOp .Add .U64 ai five
        let q ← semCast .IntToPtr .U64 .Ptr sum
        Sem.lookupValue q) MachineState.empty with
      | .ok (v, _) => some v
      | .error _ => none) = some (.ptr 1029 (some ⟨1⟩)) := by
  trustIrReduce

/-- Family (d) of the SPEC borrow section's clause 2, decided: `Dealloc` of a
    zero-size slot frees THAT slot, not the borrowed allocation placed after
    it. The slot's bump makes the next base differ, and the free is named by
    provenance anyway; `b`'s borrow stays live. -/
theorem dealloc_zero_size_frees_itself :
    (match Sem.run (do
        let z ← semAlloca .Unit none
        let b ← semAlloca .I32 none
        let _ ← semBorrow b
        semDealloc z
        let pb ← getPermission ⟨1⟩
        let s ← Sem.getState
        pure (pb, (s.memory.lookup ⟨0⟩).map (·.alive), (s.memory.lookup ⟨1⟩).map (·.alive)))
        MachineState.empty with
      | .ok (r, _) => some r
      | .error _ => none) = some (.sharedBorrow 1, some false, some true) :=
  by
    trustIrCompilerProof {
      rfl
    } {
      all_goals
        change (match StateT.run (semAlloca .Unit none >>= fun z =>
          (semAlloca .I32 none >>= fun b =>
            (semBorrow b >>= fun _borrowed =>
              (semDealloc z >>= fun _freed =>
                (getPermission ⟨1⟩ >>= fun pb =>
                  (Sem.getState >>= fun st =>
                    pure (pb, (st.memory.lookup ⟨0⟩).map (·.alive), (st.memory.lookup ⟨1⟩).map (·.alive)))))))) MachineState.empty with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals rw [sr_bind, provenanceUnit_run]
      all_goals
        change (match StateT.run (semAlloca .I32 none >>= fun b =>
          (semBorrow b >>= fun _borrowed =>
            (semDealloc provenanceUnitResult.1 >>= fun _freed =>
              (getPermission ⟨1⟩ >>= fun pb =>
                (Sem.getState >>= fun st =>
                  pure (pb, (st.memory.lookup ⟨0⟩).map (·.alive), (st.memory.lookup ⟨1⟩).map (·.alive))))))) provenanceUnitResult.2 with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals rw [sr_bind, provenanceUnit32_run]
      all_goals
        change (match StateT.run (semBorrow provenanceUnit32Result.1 >>= fun _borrowed =>
          (semDealloc provenanceUnitResult.1 >>= fun _freed =>
            (getPermission ⟨1⟩ >>= fun pb =>
              (Sem.getState >>= fun st =>
                pure (pb, (st.memory.lookup ⟨0⟩).map (·.alive), (st.memory.lookup ⟨1⟩).map (·.alive)))))) provenanceUnit32Result.2 with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals rw [sr_bind, provenanceBorrowedUnit32_run]
      all_goals
        change (match StateT.run (semDealloc provenanceUnitResult.1 >>= fun _freed =>
          (getPermission ⟨1⟩ >>= fun pb =>
            (Sem.getState >>= fun st =>
              pure (pb, (st.memory.lookup ⟨0⟩).map (·.alive), (st.memory.lookup ⟨1⟩).map (·.alive))))) provenanceBorrowedUnit32Result.2 with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals rw [sr_bind, provenanceFreedUnit32_run]
      all_goals
        change (match StateT.run (getPermission ⟨1⟩ >>= fun pb =>
          (Sem.getState >>= fun st =>
            pure (pb, (st.memory.lookup ⟨0⟩).map (·.alive), (st.memory.lookup ⟨1⟩).map (·.alive)))) provenanceFreedUnit32State with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals rw [sr_bind, provenanceUnit32Permission_run]
      all_goals
        change (match StateT.run (Sem.getState >>= fun st =>
          pure ((Permission.sharedBorrow 1), (st.memory.lookup ⟨0⟩).map (·.alive), (st.memory.lookup ⟨1⟩).map (·.alive))) provenanceFreedUnit32State with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals rw [sr_bind, provenanceUnit32GetState_run]
      all_goals
        change (match StateT.run (pure ((Permission.sharedBorrow 1), (provenanceFreedUnit32State.memory.lookup ⟨0⟩).map (·.alive), (provenanceFreedUnit32State.memory.lookup ⟨1⟩).map (·.alive)) : Sem (Permission × Option Bool × Option Bool)) provenanceFreedUnit32State with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals
        change some (Permission.sharedBorrow 1, (provenanceFreedUnit32State.memory.lookup ⟨0⟩).map (·.alive), (provenanceFreedUnit32State.memory.lookup ⟨1⟩).map (·.alive)) = _
      all_goals exact congrArg some provenanceUnit32Observation
    }

-- Closed kernel reduction includes the full machine record. Use the
-- same scoped budget as adjacent ground memory witnesses.
set_option maxHeartbeats 4000000 in
/-- `Dealloc` of a pointer one past the end of an `i32` slot is UB — it names
    that slot, at an offset other than its base — and never frees the slot
    placed at that address (probe p14). -/
theorem dealloc_one_past_end_is_ub :
    ∃ msg, Sem.run (do
        let a ← semAlloca .I32 none
        let _b ← semAlloca .I32 none
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [one]
        semDealloc q) MachineState.empty = .error (.ub msg) :=
  ⟨_, by
    trustIrCompilerProof {
      simp only [semGEPUsing, semGEPValuesUsing, pure_bind, bind_assoc]
    } { skip }
    trustIrCompilerProof {
      rfl
    } {
      all_goals
        change StateT.run (semAlloca .I32 none >>= fun a =>
          (semAlloca .I32 none >>= fun b =>
            (Sem.bindFresh (.int 64 1) >>= fun one =>
              (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [one] >>= fun q =>
                semDealloc q)))) MachineState.empty = _
      all_goals rw [sr_bind, provenanceStack32_run]
      all_goals
        change StateT.run (semAlloca .I32 none >>= fun b =>
          (Sem.bindFresh (.int 64 1) >>= fun one =>
            (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 provenanceStack32Result.1 [one] >>= fun q =>
              semDealloc q))) provenanceStack32Result.2 = _
      all_goals rw [sr_bind, provenanceStack32Second_run]
      all_goals
        change StateT.run (Sem.bindFresh (.int 64 1) >>= fun one =>
          (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 provenanceStack32Result.1 [one] >>= fun q =>
            semDealloc q)) provenanceStack32SecondResult.2 = _
      all_goals rw [sr_bind, provenanceOneAfterTwo32_run]
      all_goals
        change StateT.run (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 provenanceStack32Result.1 [provenanceOneAfterTwo32Result.1] >>= fun q =>
          semDealloc q) provenanceOneAfterTwo32Result.2 = _
      all_goals rw [sr_bind, provenancePast32GEP_run]
      all_goals
        change StateT.run (semDealloc provenancePast32Result.1) provenancePast32Result.2 = _
      all_goals exact provenancePast32Dealloc_run
    }⟩

set_option maxHeartbeats 4000000 in
/-- An `i32` slot placed after a byte slot is 4-aligned by the reference
    placement, so a store and load with a declared `align 4` succeed (probe
    p04; a packed allocator put it at 1025 and refused the access). -/
theorem aligned_store_after_byte_local_ok :
    (match Sem.run (do
        let _ ← semAlloca .I8 none
        let p ← semAlloca .I32 none
        let seven ← Sem.bindFresh (.int 32 7)
        semStore .I32 p seven false (some 4)
        let r ← semLoad .I32 p false (some 4)
        Sem.lookupValue r) MachineState.empty with
      | .ok (v, _) => some v
      | .error _ => none) = some (.int 32 7) :=
  by
    trustIrCompilerProof {
      rfl
    } {
      all_goals
        change (match StateT.run (semAlloca .I8 none >>= fun _byte =>
          (semAlloca .I32 none >>= fun p =>
            (Sem.bindFresh (.int 32 7) >>= fun seven =>
              (semStore .I32 p seven false (some 4) >>= fun _stored =>
                (semLoad .I32 p false (some 4) >>= fun r =>
                  Sem.lookupValue r))))) MachineState.empty with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals rw [sr_bind, provenanceByte_run]
      all_goals
        change (match StateT.run (semAlloca .I32 none >>= fun p =>
          (Sem.bindFresh (.int 32 7) >>= fun seven =>
            (semStore .I32 p seven false (some 4) >>= fun _stored =>
              (semLoad .I32 p false (some 4) >>= fun r =>
                Sem.lookupValue r)))) provenanceByteResult.2 with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals rw [sr_bind, provenanceByte32_run]
      all_goals
        change (match StateT.run (Sem.bindFresh (.int 32 7) >>= fun seven =>
          (semStore .I32 provenanceByte32Result.1 seven false (some 4) >>= fun _stored =>
            (semLoad .I32 provenanceByte32Result.1 false (some 4) >>= fun r =>
              Sem.lookupValue r))) provenanceByte32Result.2 with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals rw [sr_bind, provenanceByteSeven_run]
      all_goals
        change (match StateT.run (semStore .I32 provenanceByte32Result.1 provenanceByteSevenResult.1 false (some 4) >>= fun _stored =>
          (semLoad .I32 provenanceByte32Result.1 false (some 4) >>= fun r =>
            Sem.lookupValue r)) provenanceByteSevenResult.2 with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals rw [sr_bind, provenanceByteStore_run]
      all_goals
        change (match StateT.run (semLoad .I32 provenanceByte32Result.1 false (some 4) >>= fun r =>
          Sem.lookupValue r) provenanceByteStoredState with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals rw [sr_bind, provenanceByteLoad_run]
      all_goals
        change (match StateT.run (Sem.lookupValue provenanceByteLoadedResult.1) provenanceByteLoadedResult.2 with
          | .ok (v, _) => some v
          | .error _ => none) = _
      all_goals rw [provenanceByteLookup_run]
      all_goals rfl
    }

set_option maxHeartbeats 4000000 in
/-- A load one past the end of an `i32` slot is UB, even with another slot
    placed right there: the access is checked against the allocation the
    pointer was derived from (probe p02). -/
theorem load_one_past_end_is_ub :
    ∃ msg, Sem.run (do
        let a ← semAlloca .I32 none
        let b ← semAlloca .I32 none
        let seven ← Sem.bindFresh (.int 32 7)
        semStore .I32 b seven
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [one]
        let _ ← semLoad .I32 q
        pure ()) MachineState.empty = .error (.ub msg) :=
  ⟨_, by
    trustIrCompilerProof {
      simp only [Sem.run, sr_bind, alloca32_empty, alloca64_empty, alloca32_second, Except.bind]
      simp only [semGEPUsing, semGEPValuesUsing, pure_bind, bind_assoc]
    } { skip }
    trustIrCompilerProof {
      rfl
    } {
      all_goals
        change StateT.run (semAlloca .I32 none >>= fun a =>
          (semAlloca .I32 none >>= fun b =>
            (Sem.bindFresh (.int 32 7) >>= fun seven =>
              (semStore .I32 b seven >>= fun _stored =>
                (Sem.bindFresh (.int 64 1) >>= fun one =>
                  (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [one] >>= fun q =>
                    (semLoad .I32 q >>= fun _loaded => pure ()))))))) MachineState.empty = _
      all_goals rw [sr_bind, provenanceStack32_run]
      all_goals
        change StateT.run (semAlloca .I32 none >>= fun b =>
          (Sem.bindFresh (.int 32 7) >>= fun seven =>
            (semStore .I32 b seven >>= fun _stored =>
              (Sem.bindFresh (.int 64 1) >>= fun one =>
                (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 provenanceStack32Result.1 [one] >>= fun q =>
                  (semLoad .I32 q >>= fun _loaded => pure ())))))) provenanceStack32Result.2 = _
      all_goals rw [sr_bind, provenanceStack32Second_run]
      all_goals
        change StateT.run (Sem.bindFresh (.int 32 7) >>= fun seven =>
          (semStore .I32 provenanceStack32SecondResult.1 seven >>= fun _stored =>
            (Sem.bindFresh (.int 64 1) >>= fun one =>
              (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 provenanceStack32Result.1 [one] >>= fun q =>
                (semLoad .I32 q >>= fun _loaded => pure ()))))) provenanceStack32SecondResult.2 = _
      all_goals rw [sr_bind, provenanceTwoSeven_run]
      all_goals
        change StateT.run (semStore .I32 provenanceStack32SecondResult.1 provenanceTwoSevenResult.1 >>= fun _stored =>
          (Sem.bindFresh (.int 64 1) >>= fun one =>
            (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 provenanceStack32Result.1 [one] >>= fun q =>
              (semLoad .I32 q >>= fun _loaded => pure ())))) provenanceTwoSevenResult.2 = _
      all_goals rw [sr_bind, provenanceTwoStore_run]
      all_goals
        change StateT.run (Sem.bindFresh (.int 64 1) >>= fun one =>
          (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 provenanceStack32Result.1 [one] >>= fun q =>
            (semLoad .I32 q >>= fun _loaded => pure ()))) provenanceTwoStoredState = _
      all_goals rw [sr_bind, provenanceStoredOne_run]
      all_goals
        change StateT.run (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 provenanceStack32Result.1 [provenanceStoredOneResult.1] >>= fun q =>
          (semLoad .I32 q >>= fun _loaded => pure ())) provenanceStoredOneResult.2 = _
      all_goals rw [sr_bind, provenanceStoredPastGEP_run]
      all_goals
        change StateT.run (semLoad .I32 provenanceStoredPastResult.1 >>= fun _loaded => pure ()) provenanceStoredPastResult.2 = _
      all_goals rw [sr_bind, provenanceStoredPastLoad_run]
      all_goals rfl
    }⟩

/-- An access with no declared alignment checks the type's NATURAL one: an
    `i32` load at `a + 1` of an `i64` slot is UB (cell c04). -/
theorem load_misaligned_without_declared_align_is_ub :
    ∃ msg, Sem.run (do
        let a ← semAlloca .I64 none
        let zero ← Sem.bindFresh (.int 64 0)
        semStore .I64 a zero
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 a [one]
        let _ ← semLoad .I32 q
        pure ()) MachineState.empty = .error (.ub msg) :=
  ⟨_, by
    trustIrCompilerProof {
      simp only [Sem.run, sr_bind, alloca32_empty, alloca64_empty, alloca32_second, Except.bind]
      simp only [semGEPUsing, semGEPValuesUsing, pure_bind, bind_assoc]
    } { skip }
    trustIrCompilerProof {
      rfl
    } {
      all_goals
        change StateT.run (semAlloca .I64 none >>= fun a =>
          (Sem.bindFresh (.int 64 0) >>= fun zero =>
            (semStore .I64 a zero >>= fun _stored =>
              (Sem.bindFresh (.int 64 1) >>= fun one =>
                (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 a [one] >>= fun q =>
                  (semLoad .I32 q >>= fun _loaded => pure ())))))) MachineState.empty = _
      all_goals rw [sr_bind, provenanceStack64_run]
      all_goals
        change StateT.run (Sem.bindFresh (.int 64 0) >>= fun zero =>
          (semStore .I64 provenanceStack64Result.1 zero >>= fun _stored =>
            (Sem.bindFresh (.int 64 1) >>= fun one =>
              (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 provenanceStack64Result.1 [one] >>= fun q =>
                (semLoad .I32 q >>= fun _loaded => pure ()))))) provenanceStack64Result.2 = _
      all_goals rw [sr_bind, provenance64Zero_run]
      all_goals
        change StateT.run (semStore .I64 provenanceStack64Result.1 provenance64ZeroResult.1 >>= fun _stored =>
          (Sem.bindFresh (.int 64 1) >>= fun one =>
            (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 provenanceStack64Result.1 [one] >>= fun q =>
              (semLoad .I32 q >>= fun _loaded => pure ())))) provenance64ZeroResult.2 = _
      all_goals rw [sr_bind, provenance64Store_run]
      all_goals
        change StateT.run (Sem.bindFresh (.int 64 1) >>= fun one =>
          (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 provenanceStack64Result.1 [one] >>= fun q =>
            (semLoad .I32 q >>= fun _loaded => pure ()))) provenance64StoredState = _
      all_goals rw [sr_bind, provenance64One_run]
      all_goals
        change StateT.run (semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 provenanceStack64Result.1 [provenance64OneResult.1] >>= fun q =>
          (semLoad .I32 q >>= fun _loaded => pure ())) provenance64OneResult.2 = _
      all_goals rw [sr_bind, provenanceMisalignedGEP_run]
      all_goals
        change StateT.run (semLoad .I32 provenanceMisalignedResult.1 >>= fun _loaded => pure ()) provenanceMisalignedResult.2 = _
      all_goals rw [sr_bind, provenanceMisalignedLoad_run]
      all_goals rfl
    }⟩

set_option maxHeartbeats 16000000 in
/-- Pointer arithmetic keeps a no-provenance pointer one: a `GEP` from a
    dangling pointer that lands inside an allocation does not acquire it, and
    a load through it is UB (cell c06). -/
theorem gep_keeps_no_provenance :
    (match Sem.run (do
        let a ← semAlloca .I32 none
        let ai ← semCast .PtrToInt .Ptr .U64 a
        let four ← Sem.bindFresh (.int 64 4)
        let below ← semBinOp .Sub .U64 ai four
        let d ← semCast .IntToPtr .U64 .Ptr below
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 d [four]
        Sem.lookupValue q) MachineState.empty with
      | .ok (v, _) => some v
      | .error _ => none) = some (.ptr 1024 none) ∧
    ∃ msg, Sem.run (do
        let a ← semAlloca .I32 none
        let seven ← Sem.bindFresh (.int 32 7)
        semStore .I32 a seven
        let ai ← semCast .PtrToInt .Ptr .U64 a
        let four ← Sem.bindFresh (.int 64 4)
        let below ← semBinOp .Sub .U64 ai four
        let d ← semCast .IntToPtr .U64 .Ptr below
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 d [four]
        let _ ← semLoad .I32 q
        pure ()) MachineState.empty = .error (.ub msg) := by
  constructor
  · trustIrReduce
  · refine ⟨"Load: pointer value 1024 has no allocation provenance", ?_⟩
    simp only [Sem.run, sr_bind]
    trustIrReduce

/-- A negative signed integer becomes a LARGE address, never the null
    pointer: `inttoptr i64 -8` is the no-provenance pointer at 2^64 - 8, and
    `ptrtoint` gives that address back (cell c01). -/
theorem inttoptr_negative_is_dangling_not_null :
    (match Sem.run (do
        let m ← Sem.bindFresh (.int 64 (-8))
        let p ← semCast .IntToPtr .I64 .Ptr m
        Sem.lookupValue p) MachineState.empty with
      | .ok (v, _) => some v
      | .error _ => none) = some (.ptr (2 ^ 64 - 8) none) :=
  by
    trustIrCompilerProof {
      rfl
    } {
      change (match StateT.run (Sem.bindFresh (.int 64 (-8)) >>= fun m =>
          semCast .IntToPtr .I64 .Ptr m >>= fun p => Sem.lookupValue p)
          MachineState.empty with
        | .ok (v, _) => some v
        | .error _ => none) = _
      rw [sr_bind, provenanceNegativeInt_run]
      change (match StateT.run
          (semCast .IntToPtr .I64 .Ptr provenanceNegativeIntResult.1 >>= fun p =>
            Sem.lookupValue p) provenanceNegativeIntResult.2 with
        | .ok (v, _) => some v
        | .error _ => none) = _
      rw [sr_bind, provenanceNegativePointer_run]
      change (match StateT.run (Sem.lookupValue provenanceNegativePointerResult.1)
          provenanceNegativePointerResult.2 with
        | .ok (v, _) => some v
        | .error _ => none) = _
      rw [provenanceNegativeLookup_run]
      all_goals rfl
    }


-- =================================================================
-- Fat-pointer trio: Sem-level round trip (B3 depth ledger)
-- =================================================================

/-- SSA ids other than the freshly bound one read through `bindValue`
    unchanged. -/
private theorem lookupValue_bindValue_ne (st : MachineState) (v : Value)
    (id : ValueId) (h : id.index ≠ st.nextValueId) :
    (st.bindValue v).snd.lookupValue id = st.lookupValue id := by
  have hne : (id == ValueId.mk st.nextValueId) = false := by
    first
    | refine (beq_eq_false_iff_ne _ _).mpr ?_
    | refine beq_eq_false_iff_ne.mpr ?_
    intro hEq
    exact h (congrArg ValueId.index hEq)
  simp [MachineState.bindValue, MachineState.lookupValue, ValueMap.get,
    ValueMap.set, hne]

/-- Reading back the SSA value `bindValue` just bound. -/
private theorem lookupValue_bindValue_self (st : MachineState) (v : Value) :
    (st.bindValue v).snd.lookupValue (st.bindValue v).fst = some v := by
  simp [MachineState.bindValue, MachineState.lookupValue, ValueMap.get,
    ValueMap.set]

/-- **Fat-pointer round trip, Sem level (B3 depth ledger "Fat-pointer
    values").** Running the instruction sequence

        d ← PtrData    fatptr<kind> p
        m ← PtrMetadata fatptr<kind> p
        r ← PtrFromParts fatptr<kind> d m

    from ANY state in which `p` holds a fat-pointer value `.fatPtr data
    prov metadata` succeeds and binds `r` to the IDENTICAL value — the
    decompose/recombine round trip at the operational layer, on top of the
    value-level `fatPtr_roundTrip_value` / `fatPtrFromParts_data_metadata`
    (Proofs/MemoryProps.lean).

    Hypotheses, honestly stated:
    * `hLive`: `p` is an already-allocated SSA id (`index < nextValueId`),
      so the three fresh result binds cannot shadow it — the standing SSA
      well-formedness invariant of the evaluator;
    * `hNull`: a null data lane carries no provenance, which every fat
      pointer the semantics constructs keeps (`fatPtrFromPartsValue`,
      `Memory.resolveDecoded`);
    * `hMeta`: the stored metadata inhabits the kind's declared metadata
      type (`U64` length / `Ptr` vtable at the model's 64-bit width) — the
      same guard `PtrFromParts` enforces on injection, so any `.fatPtr`
      the semantics itself constructed satisfies it. -/
theorem semFatPtr_roundTrip (kind : FatPtrKind) (data : Nat) (prov : Option AllocId)
    (metadata : Value) (ptrId : ValueId) (s : MachineState)
    (hP : s.lookupValue ptrId = some (.fatPtr data prov metadata))
    (hNull : data = 0 → prov = none)
    (hLive : ptrId.index < s.nextValueId)
    (hMeta : metadataInhabits kind.metadataTy metadata = true) :
    ∃ (resultId : ValueId) (sEnd : MachineState),
      Sem.run (do
          let dataId ← semPtrData (.FatPtr kind) ptrId
          let metaId ← semPtrMetadata (.FatPtr kind) kind.metadataTy ptrId
          semPtrFromParts (.FatPtr kind) kind.metadataTy dataId metaId) s
        = .ok (resultId, sEnd)
      ∧ sEnd.lookupValue resultId = some (.fatPtr data prov metadata) := by
  -- Reflexivity of the static metadata-type check (structural, so it
  -- reduces per kind).
  have hmt : metadataTyMatches kind.metadataTy kind = true := by
    cases kind <;> rfl
  have hValid :
      fatPtrStoreValueValid (.FatPtr kind) (.fatPtr data prov metadata) = true := by
    exact hMeta
  let dataLane : Value := fatPtrDataLane data prov
  have hRebuild :
      fatPtrFromPartsValue dataLane metadata = some (.fatPtr data prov metadata) := by
    cases data with
    | zero => rw [hNull rfl]; rfl
    | succ _ => rfl
  -- Intermediate ids and states.
  let dId : ValueId := ValueId.mk s.nextValueId
  let s1 : MachineState := (s.bindValue dataLane).snd
  let mId : ValueId := ValueId.mk s1.nextValueId
  let s2 : MachineState := (s1.bindValue metadata).snd
  let rId : ValueId := ValueId.mk s2.nextValueId
  let s3 : MachineState := (s2.bindValue (.fatPtr data prov metadata)).snd
  -- Step 1: PtrData projects the data lane onto the fresh id dId.
  have h1 : Sem.run (semPtrData (.FatPtr kind) ptrId) s = .ok (dId, s1) := by
    unfold semPtrData
    simp only [fatPtrStoreValueValidFor]
    simp only [Sem.run, sr_bind, sr_lookup, hP, hValid, Bool.not_true,
      Bool.false_eq_true, if_false, fatPtrDataValue, Except.bind]
    exact bindFresh_run dataLane s
  -- The original binding survives the fresh bind (hLive).
  have hP1 : s1.lookupValue ptrId = some (.fatPtr data prov metadata) := by
    rw [show s1 = (s.bindValue dataLane).snd from rfl,
      lookupValue_bindValue_ne s dataLane ptrId (Nat.ne_of_lt hLive)]
    exact hP
  -- Step 2: PtrMetadata projects the metadata lane onto the fresh id mId.
  have h2 : Sem.run (semPtrMetadata (.FatPtr kind) kind.metadataTy ptrId) s1
      = .ok (mId, s2) := by
    unfold semPtrMetadata
    simp only [metadataTyMatchesFor, fatPtrStoreValueValidFor]
    simp only [Sem.run, hmt, Bool.not_true, Bool.false_eq_true, if_false,
      sr_bind, sr_lookup, hP1, hValid, fatPtrMetadataValue, Except.bind]
    exact bindFresh_run metadata s1
  -- Lookups in s2: the freshly bound metadata, and the surviving data lane.
  have hM2 : s2.lookupValue mId = some metadata :=
    lookupValue_bindValue_self s1 metadata
  have hD2 : s2.lookupValue dId = some dataLane := by
    rw [show s2 = (s1.bindValue metadata).snd from rfl,
      lookupValue_bindValue_ne s1 metadata dId
        (Nat.ne_of_lt (Nat.lt_succ_self s.nextValueId))]
    exact lookupValue_bindValue_self s dataLane
  have hDataDefined : ∀ op, Sem.rejectPartial dataLane op = pure () := by
    intro op
    cases data <;> rfl
  have hMetadataDefined : ∀ op, Sem.rejectPartial metadata op = pure () := by
    intro op
    cases metadata <;> try rfl
    all_goals cases kind <;> simp [metadataInhabits, FatPtrKind.metadataTy] at hMeta
  -- Step 3: PtrFromParts recombines the lanes onto the fresh id rId.
  have h3 : Sem.run (semPtrFromParts (.FatPtr kind) kind.metadataTy dId mId) s2
      = .ok (rId, s3) := by
    unfold semPtrFromParts
    simp only [metadataTyMatchesFor, metadataInhabitsFor]
    simp only [Sem.run, hmt, Bool.not_true, Bool.false_eq_true, if_false,
      sr_bind, sr_lookup, hM2, hMeta, hD2, hRebuild, Except.bind,
      hDataDefined, hMetadataDefined, sr_pure]
    exact bindFresh_run (.fatPtr data prov metadata) s2
  -- Compose the three runs and read the result back.
  refine ⟨rId, s3, ?_, ?_⟩
  · rw [Sem.run_bind, h1]
    simp only [Except.bind]
    rw [Sem.run_bind, h2]
    simp only [Except.bind]
    exact h3
  · exact lookupValue_bindValue_self s2 (.fatPtr data prov metadata)

-- =================================================================
-- Future work
-- =================================================================

/-
## Theorems for subsequent phases

1. **Full memory safety for well-typed programs:**
   If a program is well-typed (all memory accesses are through valid
   pointers with appropriate permissions), then no UB error is produced.
   This requires the full typing judgment from Phase 6.

2. **Separation logic frame rule:**
   If a computation only accesses allocations in a footprint F, then
   the rest of memory is preserved. This enables modular reasoning.

3. **Temporal safety:**
   No use-after-free: once an allocation is freed, no subsequent
   load/store can access it. This follows from the alive check in
   semLoad/semStore combined with the deallocation marking.

4. **Spatial safety:**
   No out-of-bounds access: all loads/stores are within the bounds of
   the allocation their pointer was derived from (`semAccess_names_provenance`).
-/


end TrustIr
