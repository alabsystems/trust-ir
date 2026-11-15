-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroFreshCursor
import TrustIr.Proofs.GenericCoroProps

namespace TrustIr.GenericCoroAllBlocksPlanner
open GenericCoroFreshCursor GenericCoroFreshIds GenericCoro

/-- The occupied source and prior history are type indices only. The
    executable ready branch carries three numbers, with no history append. -/
inductive TripleOutcome {domain : Nat} {used : List Nat}
    (before after : Cursor domain used) where
  | ready (names : Triple domain (before.reserved ++ used))
      (history : after.reserved = [names.third, names.second, names.first] ++ before.reserved)
  | capacity (delta : List Nat) (short : delta.length < 3)
      (history : after.reserved = delta ++ before.reserved)
      (covers : ∀ key, key < domain → key ∈ after.reserved ++ used)
      (fullCursor : after.next = domain)

structure TripleReservation {domain : Nat} {used : List Nat} (before : Cursor domain used) where
  after : Cursor domain used
  visits : Nat
  work : before.next + visits = after.next
  outcome : TripleOutcome before after

/-- Reserve three identifiers using the held index and monotonically
    advancing cursor. Failure stops after zero, one or two actual successes.
    All concatenation and length arguments below occur only in erased proofs. -/
def reserveTriple {domain : Nat} {used : List Nat}
    (before : Cursor domain used) : TripleReservation before := by
  let first := reserve before
  cases firstKey : first.key with
  | none =>
    have history : first.after.reserved = before.reserved := by
      simpa only [firstKey, Option.toList, List.nil_append] using first.history
    exact ⟨first.after, first.visits, first.work,
      .capacity [] (by decide) history (first.exhausted firstKey) (first.fullCursor firstKey)⟩
  | some one =>
    have firstHistory : first.after.reserved = one :: before.reserved := by
      simpa only [firstKey, Option.toList, List.cons_append, List.nil_append] using first.history
    let second := reserve first.after
    cases secondKey : second.key with
    | none =>
      have history : second.after.reserved = [one] ++ before.reserved := by
        simpa only [secondKey, Option.toList, List.nil_append, firstHistory] using second.history
      exact ⟨second.after, first.visits + second.visits, by
        have firstWork := first.work; have secondWork := second.work; omega,
        .capacity [one] (by change 1 < 3; decide) history (second.exhausted secondKey) (second.fullCursor secondKey)⟩
    | some two =>
      have secondHistory : second.after.reserved = two :: one :: before.reserved := by
        simpa only [secondKey, Option.toList, List.cons_append, List.nil_append, firstHistory]
          using second.history
      let third := reserve second.after
      cases thirdKey : third.key with
      | none =>
        have history : third.after.reserved = [two, one] ++ before.reserved := by
          simpa only [thirdKey, Option.toList, List.nil_append, secondHistory] using third.history
        exact ⟨third.after, first.visits + second.visits + third.visits, by
          have firstWork := first.work; have secondWork := second.work
          have thirdWork := third.work; omega,
          .capacity [two, one] (by change 2 < 3; decide) history (third.exhausted thirdKey) (third.fullCursor thirdKey)⟩
      | some three =>
        have firstFresh := first.fresh one firstKey
        have secondFresh := second.fresh two secondKey
        have thirdFresh := third.fresh three thirdKey
        rw [firstHistory] at secondFresh
        rw [secondHistory] at thirdFresh
        let names : Triple domain (before.reserved ++ used) :=
          { first := one, second := two, third := three
            firstBound := first.inRange one firstKey
            secondBound := second.inRange two secondKey
            thirdBound := third.inRange three thirdKey
            firstUnused := firstFresh
            secondUnused := fun member => secondFresh (List.mem_cons_of_mem one member)
            thirdUnused := fun member => thirdFresh
              (List.mem_cons_of_mem two (List.mem_cons_of_mem one member))
            firstSecond := by intro same; subst two; exact secondFresh ((trustIrListMemConsSelf _ _))
            firstThird := by intro same; subst three
                             exact thirdFresh (List.mem_cons_of_mem two ((trustIrListMemConsSelf _ _)))
            secondThird := by intro same; subst three; exact thirdFresh ((trustIrListMemConsSelf _ _)) }
        have history : third.after.reserved = [three, two, one] ++ before.reserved := by
          simpa only [thirdKey, Option.toList, List.cons_append, List.nil_append, secondHistory]
            using third.history
        exact ⟨third.after, first.visits + second.visits + third.visits, by
          have firstWork := first.work; have secondWork := second.work
          have thirdWork := third.work; omega,
          .ready names history⟩

theorem TripleReservation.monotone {domain : Nat} {used : List Nat}
    {before : Cursor domain used} (allocation : TripleReservation before) :
    before.next ≤ allocation.after.next := by have work := allocation.work; omega

theorem TripleReservation.capacity_excludes_triple {domain : Nat} {used : List Nat}
    {before : Cursor domain used} (allocation : TripleReservation before)
    (delta : List Nat) (short : delta.length < 3)
    (history : allocation.after.reserved = delta ++ before.reserved)
    (covers : ∀ key, key < domain → key ∈ allocation.after.reserved ++ used)
    (names : Triple domain (before.reserved ++ used)) : False := by
  apply GenericCoroFreshIds.capacity_excludes_triple (used := before.reserved ++ used)
    { reserved := delta
      atMostTwo := by omega
      covers := by simpa only [history, List.append_assoc] using covers } names

abbrev Rows := List (BlockId × BasicBlock)
abbrev Trace := List (BlockId × Names)

trustIrDenseMatch
def isSuspend : Inst → Bool
  | .CoroSuspend _ _ _ _ => true
  | _ => false

def reverseNames (names : Names) : List Nat :=
  [names.state.index, names.pointer.index, names.index.index]

/-- A proof-only, occurrence-indexed account of the literal rows emitted.
    Duplicate labels are separate constructors and therefore get separate
    triples. No CFG lookup or reachability filter selects the rows. -/
inductive Plans {domain : Nat} {used : List Nat} :
    Cursor domain used → Cursor domain used → Rows → Rows → Trace → Prop where
  | nil (state : Cursor domain used) : Plans state state [] [] []
  | keep (before after : Cursor domain used) (id : BlockId) (block : BasicBlock)
      (notSuspend : isSuspend block.terminator = false)
      (source target : Rows) (trace : Trace)
      (rest : Plans before after source target trace) :
      Plans before after ((id, block) :: source) ((id, block) :: target) trace
  | expand (before middle after : Cursor domain used) (id : BlockId) (block : BasicBlock)
      (suspend : isSuspend block.terminator = true)
      (names : Triple domain (before.reserved ++ used))
      (history : middle.reserved = [names.third, names.second, names.first] ++ before.reserved)
      (source target : Rows) (trace : Trace)
      (rest : Plans middle after source target trace) :
      Plans before after ((id, block) :: source)
        ((id, expandedEntry (Names.ofTriple names) block) :: target)
        ((id, Names.ofTriple names) :: trace)

inductive Completion {domain : Nat} {used : List Nat} (state : Cursor domain used) where
  | ready
  | capacity (delta : List Nat) (short : delta.length < 3)
      (covers : ∀ key, key < domain → key ∈ state.reserved ++ used)
      (fullCursor : state.next = domain)

structure Result (domain : Nat) (used : List Nat) where
  cursor : Cursor domain used
  rows : Rows
  trace : Trace
  pending : Rows
  visits : Nat
  completion : Completion cursor

/-- A single tail-recursive occurrence traversal. Both output lists are
    consed in reverse and reversed once at the terminal branch. The source
    occupancy index is never rebuilt inside this loop. -/
def lowerRowsLoop {domain : Nat} {used : List Nat} :
    Rows → Cursor domain used → Rows → Trace → Nat → Result domain used
  | [], cursor, reversedRows, reversedTrace, visits =>
    ⟨cursor, reversedRows.reverse, reversedTrace.reverse, [], visits, .ready⟩
  | (id, block) :: rest, cursor, reversedRows, reversedTrace, visits =>
    if isSuspend block.terminator then
      let allocation := reserveTriple cursor
      match allocation.outcome with
      | .ready names _ =>
        let temps := Names.ofTriple names
        lowerRowsLoop rest allocation.after
          ((id, expandedEntry temps block) :: reversedRows)
          ((id, temps) :: reversedTrace) (visits + allocation.visits)
      | .capacity delta short _ covers full =>
        ⟨allocation.after, reversedRows.reverse, reversedTrace.reverse,
          (id, block) :: rest, visits + allocation.visits, .capacity delta short covers full⟩
    else lowerRowsLoop rest cursor ((id, block) :: reversedRows) reversedTrace visits

/-- Prepare the complete original source reservation domain exactly once.
    This includes uses, shadowed rows and unused raw trailing destination rows. -/
def lowerRows (domain : Nat) (blocks : Rows) : Result domain (graphReservations blocks) :=
  lowerRowsLoop blocks (prepare domain (graphReservations blocks)) [] [] 0

def planAllBlocks (blocks : Rows) : Result u32Domain (graphReservations blocks) :=
  lowerRows u32Domain blocks

def suspendCount : Rows → Nat
  | [] => 0
  | (_, block) :: rest => (if isSuspend block.terminator then 1 else 0) + suspendCount rest

/-- Literal row positions, labels and order are preserved, including shadowed
    duplicate labels. -/
theorem Plans.labels {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace) :
    target.map Prod.fst = source.map Prod.fst := by
  induction plan with
  | nil => rfl
  | keep _ _ _ _ _ _ _ _ _ ih => exact congrArg (_ :: ·) ih
  | expand _ _ _ _ _ _ _ _ _ _ _ _ ih => exact congrArg (_ :: ·) ih

theorem Plans.params {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace) :
    graphParams target = graphParams source := by
  induction plan with
  | nil => rfl
  | keep _ _ _ _ _ _ _ _ _ ih =>
    exact congrArg (_ ++ ·) ih
  | expand _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [graphParams, trustIrCoroListLemma List.cons_bind List.flatMap_cons, expandedEntry_params]
    exact congrArg (_ ++ ·) ih

/-- There is exactly one trace entry and therefore exactly three reserved
    names for every actual suspend occurrence, not every distinct label. -/
theorem Plans.trace_count {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace) :
    trace.length = suspendCount source := by
  induction plan with
  | nil => rfl
  | keep _ _ _ _ notSuspend _ _ _ _ ih =>
    simp only [suspendCount, notSuspend, Bool.false_eq_true, if_false, Nat.zero_add, ih]
  | expand _ _ _ _ _ suspend _ _ _ _ _ _ ih =>
    simp only [List.length_cons, suspendCount, suspend, if_true, ih]
    omega

theorem Plans.history {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace) :
    after.reserved = (trustIrListBind trace.reverse (fun row => reverseNames row.2)) ++ before.reserved := by
  induction plan with
  | nil => rfl
  | keep _ _ _ _ _ _ _ _ _ ih => exact ih
  | expand _ _ _ _ _ _ names history _ _ _ _ ih =>
    rw [ih, history]
    simp only [List.reverse_cons, trustIrCoroListLemma List.append_bind List.flatMap_append, trustIrCoroListLemma List.cons_bind List.flatMap_cons, trustIrCoroListLemma List.nil_bind List.flatMap_nil,
      List.append_nil, reverseNames, Names.ofTriple, List.append_assoc]

theorem Plans.history_count {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace) :
    after.reserved.length = before.reserved.length + 3 * suspendCount source := by
  induction plan with
  | nil => simp only [suspendCount, Nat.mul_zero, Nat.add_zero]
  | keep _ _ _ _ notSuspend _ _ _ _ ih =>
    simpa only [suspendCount, notSuspend, Bool.false_eq_true, if_false, Nat.zero_add] using ih
  | expand _ _ _ _ _ suspend names history _ _ _ _ ih =>
    have length := congrArg List.length history
    simp only [List.length_append, List.length_cons, List.length_nil] at length
    simp only [suspendCount, suspend, if_true]
    omega

def Ready {domain : Nat} {used : List Nat} (result : Result domain used) : Prop :=
  match result.completion with
  | .ready => True
  | .capacity _ _ _ _ => False

theorem lowerRowsLoop_work {domain : Nat} {used : List Nat} (source : Rows)
    (cursor : Cursor domain used) (rows : Rows) (trace : Trace) (visits : Nat) :
    cursor.next + (lowerRowsLoop source cursor rows trace visits).visits =
      visits + (lowerRowsLoop source cursor rows trace visits).cursor.next := by
  induction source generalizing cursor rows trace visits with
  | nil => simp only [lowerRowsLoop, Nat.add_comm]
  | cons row rest ih =>
    rcases row with ⟨id, block⟩
    cases classified : isSuspend block.terminator with
    | false =>
      simpa only [lowerRowsLoop, classified, Bool.false_eq_true, if_false] using
        ih cursor ((id, block) :: rows) trace visits
    | true =>
      simp only [lowerRowsLoop, classified, if_true]
      generalize _allocationEq : reserveTriple cursor = allocation
      cases _outcome : allocation.outcome with
      | ready names history =>
        dsimp only
        have tail := ih allocation.after ((id, expandedEntry (Names.ofTriple names) block) :: rows)
          ((id, Names.ofTriple names) :: trace) (visits + allocation.visits)
        have first := allocation.work
        omega
      | capacity delta short history covers full =>
        dsimp only
        have first := allocation.work
        change cursor.next + (visits + allocation.visits) = visits + allocation.after.next
        omega

/-- Successful execution of the accumulator loop has the exact literal
    row-by-row plan, with the original accumulator prefix retained. -/
theorem lowerRowsLoop_ready {domain : Nat} {used : List Nat} (source : Rows)
    (cursor : Cursor domain used) (rows : Rows) (trace : Trace) (visits : Nat)
    (ready : Ready (lowerRowsLoop source cursor rows trace visits)) :
    ∃ target generated,
      (lowerRowsLoop source cursor rows trace visits).rows = rows.reverse ++ target ∧
      (lowerRowsLoop source cursor rows trace visits).trace = trace.reverse ++ generated ∧
      (lowerRowsLoop source cursor rows trace visits).pending = [] ∧
      Plans cursor (lowerRowsLoop source cursor rows trace visits).cursor source target generated := by
  induction source generalizing cursor rows trace visits with
  | nil => exact ⟨[], [], by simp only [lowerRowsLoop, List.append_nil],
      by simp only [lowerRowsLoop, List.append_nil], rfl, .nil cursor⟩
  | cons row rest ih =>
    rcases row with ⟨id, block⟩
    cases classified : isSuspend block.terminator with
    | false =>
      simp only [lowerRowsLoop, classified, Bool.false_eq_true, if_false] at ready ⊢
      obtain ⟨target, generated, targetEq, traceEq, pending, plan⟩ :=
        ih cursor ((id, block) :: rows) trace visits ready
      refine ⟨(id, block) :: target, generated, ?_, traceEq, pending,
        .keep cursor _ id block classified rest target generated plan⟩
      simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using targetEq
    | true =>
      simp only [lowerRowsLoop, classified, if_true] at ready ⊢
      generalize _allocationEq : reserveTriple cursor = allocation at ready ⊢
      cases _outcome : allocation.outcome with
      | capacity delta short history covers full =>
        unfold Ready at ready
        rw [_outcome] at ready
        exact False.elim ready
      | ready names history =>
        simp only [_outcome] at ready ⊢
        obtain ⟨target, generated, targetEq, traceEq, pending, plan⟩ :=
          ih allocation.after ((id, expandedEntry (Names.ofTriple names) block) :: rows)
            ((id, Names.ofTriple names) :: trace) (visits + allocation.visits) ready
        refine ⟨(id, expandedEntry (Names.ofTriple names) block) :: target,
          (id, Names.ofTriple names) :: generated, ?_, ?_, pending,
          .expand cursor allocation.after _ id block classified names history rest target generated plan⟩
        · simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using targetEq
        · simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using traceEq

theorem lowerRows_work (domain : Nat) (blocks : Rows) :
    (lowerRows domain blocks).visits = (lowerRows domain blocks).cursor.next := by
  simpa only [lowerRows, prepare, Nat.zero_add] using
    lowerRowsLoop_work blocks (prepare domain (graphReservations blocks)) [] [] 0

theorem lowerRows_ready (domain : Nat) (blocks : Rows) (ready : Ready (lowerRows domain blocks)) :
    Plans (prepare domain (graphReservations blocks)) (lowerRows domain blocks).cursor
      blocks (lowerRows domain blocks).rows (lowerRows domain blocks).trace := by
  obtain ⟨target, trace, targetEq, traceEq, _, plan⟩ :=
    lowerRowsLoop_ready blocks (prepare domain (graphReservations blocks)) [] [] 0 ready
  simp only [List.reverse_nil, List.nil_append] at targetEq traceEq
  rw [← targetEq, ← traceEq] at plan
  exact plan


theorem TripleReservation.history_bound {domain : Nat} {used : List Nat}
    {before : Cursor domain used} (allocation : TripleReservation before) :
    allocation.after.reserved.length ≤ before.reserved.length + 3 := by
  cases allocation.outcome with
  | ready names history =>
    have census := congrArg List.length history
    simp only [List.length_append, List.length_cons, List.length_nil] at census
    omega
  | capacity delta short history covers full =>
    have census := congrArg List.length history
    simp only [List.length_append] at census
    omega

theorem suspendCount_append (before after : Rows) :
    suspendCount (before ++ after) = suspendCount before + suspendCount after := by
  induction before with
  | nil => exact (Nat.zero_add _).symm
  | cons row rest ih =>
    change (if isSuspend row.2.terminator then 1 else 0) + suspendCount (rest ++ after) =
      ((if isSuspend row.2.terminator then 1 else 0) + suspendCount rest) + suspendCount after
    rw [ih, Nat.add_assoc]

/-- On failure, completed occurrences still have an exact literal plan.
    The only additional reservations are the failed row's actual zero, one
    or two successes. The still-pending suffix contains a suspend occurrence. -/
def CapacityProgress {domain : Nat} {used : List Nat} (before : Cursor domain used)
    (source reversedRows : Rows) (reversedTrace : Trace) (result : Result domain used) : Prop :=
  match result.completion with
  | .ready => True
  | .capacity delta _ _ _ =>
    ∃ processed target generated middle,
      source = processed ++ result.pending ∧
      0 < suspendCount result.pending ∧
      result.rows = reversedRows.reverse ++ target ∧
      result.trace = reversedTrace.reverse ++ generated ∧
      Plans before middle processed target generated ∧
      result.cursor.reserved = delta ++ middle.reserved

theorem lowerRowsLoop_capacity_progress {domain : Nat} {used : List Nat} (source : Rows)
    (cursor : Cursor domain used) (rows : Rows) (trace : Trace) (visits : Nat) :
    CapacityProgress cursor source rows trace (lowerRowsLoop source cursor rows trace visits) := by
  induction source generalizing cursor rows trace visits with
  | nil => trivial
  | cons row rest ih =>
    rcases row with ⟨id, block⟩
    cases classified : isSuspend block.terminator with
    | false =>
      simp only [lowerRowsLoop, classified, Bool.false_eq_true, if_false]
      have tail := ih cursor ((id, block) :: rows) trace visits
      unfold CapacityProgress at tail ⊢
      cases completion : (lowerRowsLoop rest cursor ((id, block) :: rows) trace visits).completion with
      | ready => trivial
      | capacity delta short covers full =>
        simp only [completion] at tail ⊢
        obtain ⟨processed, target, generated, middle, sourceEq, pending, targetEq, traceEq, plan, history⟩ := tail
        refine ⟨(id, block) :: processed, (id, block) :: target, generated, middle,
          by simpa only [List.cons_append] using congrArg ((id, block) :: ·) sourceEq,
          pending, ?_, traceEq, .keep cursor middle id block classified _ _ _ plan, history⟩
        simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using targetEq
    | true =>
      simp only [lowerRowsLoop, classified, if_true]
      generalize _allocationEq : reserveTriple cursor = allocation
      cases _outcome : allocation.outcome with
      | capacity delta short history covers full =>
        dsimp only [CapacityProgress]
        refine ⟨[], [], [], cursor, rfl, ?_, ?_, ?_, .nil cursor, history⟩
        · simp only [suspendCount, classified, if_true]; omega
        · simp only [List.append_nil]
        · simp only [List.append_nil]
      | ready names history =>
        dsimp only
        have tail := ih allocation.after ((id, expandedEntry (Names.ofTriple names) block) :: rows)
          ((id, Names.ofTriple names) :: trace) (visits + allocation.visits)
        unfold CapacityProgress at tail ⊢
        cases completion : (lowerRowsLoop rest allocation.after
            ((id, expandedEntry (Names.ofTriple names) block) :: rows)
            ((id, Names.ofTriple names) :: trace) (visits + allocation.visits)).completion with
        | ready => trivial
        | capacity delta short covers full =>
          simp only [completion] at tail ⊢
          obtain ⟨processed, target, generated, middle, sourceEq, pending, targetEq, traceEq, plan, tailHistory⟩ := tail
          refine ⟨(id, block) :: processed,
            (id, expandedEntry (Names.ofTriple names) block) :: target,
            (id, Names.ofTriple names) :: generated, middle,
            by simpa only [List.cons_append] using congrArg ((id, block) :: ·) sourceEq,
            pending, ?_, ?_, .expand cursor allocation.after middle id block classified names history _ _ _ plan,
            tailHistory⟩
          · simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using targetEq
          · simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using traceEq

theorem lowerRowsLoop_history_bound {domain : Nat} {used : List Nat} (source : Rows)
    (cursor : Cursor domain used) (rows : Rows) (trace : Trace) (visits : Nat) :
    (lowerRowsLoop source cursor rows trace visits).cursor.reserved.length ≤
      cursor.reserved.length + 3 * suspendCount source := by
  induction source generalizing cursor rows trace visits with
  | nil => simp only [lowerRowsLoop, suspendCount, Nat.mul_zero, Nat.add_zero, Nat.le_refl]
  | cons row rest ih =>
    rcases row with ⟨id, block⟩
    cases classified : isSuspend block.terminator with
    | false =>
      simpa only [lowerRowsLoop, suspendCount, classified, Bool.false_eq_true, if_false, Nat.zero_add] using
        ih cursor ((id, block) :: rows) trace visits
    | true =>
      simp only [lowerRowsLoop, suspendCount, classified, if_true]
      generalize _allocationEq : reserveTriple cursor = allocation
      have first := allocation.history_bound
      cases _outcome : allocation.outcome with
      | ready names history =>
        dsimp only
        have tail := ih allocation.after ((id, expandedEntry (Names.ofTriple names) block) :: rows)
          ((id, Names.ofTriple names) :: trace) (visits + allocation.visits)
        omega
      | capacity delta short history covers full =>
        dsimp only
        omega

/-- Candidate queries, not total index/runtime cost: preparing the index is
    separate, and insertion costs are not hidden in this work metric. -/
theorem lowerRows_visit_census_bound (domain : Nat) (blocks : Rows) :
    (lowerRows domain blocks).visits ≤ (graphReservations blocks).length + 3 * suspendCount blocks := by
  have work := lowerRows_work domain blocks
  have census := (lowerRows domain blocks).cursor.next_le_census
  have reserved := lowerRowsLoop_history_bound blocks (prepare domain (graphReservations blocks)) [] [] 0
  change (lowerRows domain blocks).cursor.reserved.length ≤ 0 + 3 * suspendCount blocks at reserved
  omega

theorem lowerRows_visit_domain_bound (domain : Nat) (blocks : Rows) :
    (lowerRows domain blocks).visits ≤ domain := by
  have work := lowerRows_work domain blocks
  have bound := (lowerRows domain blocks).cursor.bound
  omega

/-- Failure rules out any complete schedule of three distinct source-unused
    identifiers per original suspend occurrence. This conclusion is about
    the ORIGINAL graph, not merely the remaining cursor suffix. -/
theorem lowerRows_capacity_excludes_schedule (domain : Nat) (blocks : Rows) :
    match (lowerRows domain blocks).completion with
    | .ready => True
    | .capacity _ _ _ _ =>
      ∀ candidates : List Nat, candidates.length = 3 * suspendCount blocks →
        Distinct candidates → (∀ key ∈ candidates, key < domain) →
        (∀ key ∈ candidates, key ∉ graphReservations blocks) → False := by
  have progress := lowerRowsLoop_capacity_progress blocks
    (prepare domain (graphReservations blocks)) [] [] 0
  change CapacityProgress (prepare domain (graphReservations blocks)) blocks [] []
    (lowerRows domain blocks) at progress
  unfold CapacityProgress at progress
  cases completion : (lowerRows domain blocks).completion with
  | ready => trivial
  | capacity delta short covers full =>
    simp only [completion] at progress ⊢
    obtain ⟨processed, target, generated, middle, sourceEq, pending, _, _, plan, history⟩ := progress
    have count := plan.history_count
    change middle.reserved.length = 0 + 3 * suspendCount processed at count
    have afterCount := congrArg List.length history
    simp only [List.length_append] at afterCount
    have originalCount : suspendCount blocks = suspendCount processed +
        suspendCount (lowerRows domain blocks).pending := by
      exact (congrArg suspendCount sourceEq).trans (suspendCount_append _ _)
    have shortTotal : (lowerRows domain blocks).cursor.reserved.length < 3 * suspendCount blocks := by omega
    intro candidates census distinct inRange unused
    exact capacity_excludes_schedule domain (lowerRows domain blocks).cursor.reserved
      (graphReservations blocks) (3 * suspendCount blocks) covers shortTotal
      candidates census distinct inRange unused

theorem lowerRows_distinct (domain : Nat) (blocks : Rows) :
    Distinct (lowerRows domain blocks).cursor.reserved := (lowerRows domain blocks).cursor.distinct

theorem lowerRows_in_range (domain : Nat) (blocks : Rows) (key : Nat)
    (member : key ∈ (lowerRows domain blocks).cursor.reserved) : key < domain :=
  (lowerRows domain blocks).cursor.reservedBound key member

theorem lowerRows_source_unused (domain : Nat) (blocks : Rows) (key : Nat)
    (member : key ∈ (lowerRows domain blocks).cursor.reserved) : key ∉ graphReservations blocks :=
  (lowerRows domain blocks).cursor.reservedUnused key member


/-- Closed observations are small kernel controls of the actual producer;
    they are not a module validator, evaluator or native execution claim. -/
def tripleObservation {domain : Nat} {used : List Nat} (before : Cursor domain used) :
    Option (List Nat) × List Nat × Nat × Nat :=
  let allocation := reserveTriple before
  let names := match allocation.outcome with
    | .ready names _ => some [names.first, names.second, names.third]
    | .capacity _ _ _ _ _ => none
  (names, allocation.after.reserved, allocation.after.next, allocation.visits)

theorem triple_ready_holes :
    tripleObservation (prepare 9 [0, 2, 2, 4]) =
      (some [1, 3, 5], [5, 3, 1], 6, 6) := rfl

theorem triple_zero_success_capacity :
    tripleObservation (prepare 3 [0, 1, 2]) = (none, [], 3, 3) := rfl

theorem triple_one_success_capacity :
    tripleObservation (prepare 3 [0, 2]) = (none, [1], 3, 3) := rfl

theorem triple_two_success_capacity :
    tripleObservation (prepare 3 [1]) = (none, [2, 0], 3, 3) := rfl

theorem triple_held_cursor_does_not_restart :
    tripleObservation (reserveTriple (prepare 9 [0, 2, 2, 4])).after =
      (some [6, 7, 8], [8, 7, 6, 5, 3, 1], 9, 3) := rfl

private def exampleEntry : BasicBlock :=
  { params := [(⟨0⟩, .Ptr), (⟨1⟩, .I32)]
    body := [.Copy .I32 ⟨1⟩]
    bodyResultDests := [[⟨2⟩], [⟨2^32 - 1⟩]]
    terminator := .Br ⟨1⟩ [] }

private def exampleSuspend : BasicBlock :=
  { params := [], body := [], terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨1⟩ }

private def exampleReturn : BasicBlock := { params := [], body := [], terminator := .Return [⟨1⟩] }

private def exampleRows (duplicate : Bool) : Rows :=
  [(⟨0⟩, exampleEntry), (⟨1⟩, exampleSuspend),
    (⟨if duplicate then 1 else 2⟩, exampleSuspend), (⟨3⟩, exampleReturn)]

def traceObservation (trace : Trace) : List (Nat × List Nat) :=
  trace.map (fun row => (row.1.index,
    [row.2.index.index, row.2.pointer.index, row.2.state.index]))

/-- Both non-entry occurrences are expanded, even though the second one is
    unreachable from the first suspend's Return. The raw trailing destination
    row and maximum-u32 source key remain reserved rather than being dropped. -/
theorem two_nonentry_occurrences :
    let result := planAllBlocks (exampleRows false)
    (traceObservation result.trace, result.cursor.reserved, result.cursor.next,
      result.visits, result.pending) =
      ([(1, [3, 4, 5]), (2, [6, 7, 8])], [8, 7, 6, 5, 4, 3], 9, 9, []) := rfl

theorem two_nonentry_rows_are_actual_expandedEntry :
    (planAllBlocks (exampleRows false)).rows =
      [(⟨0⟩, exampleEntry),
        (⟨1⟩, expandedEntry ⟨⟨3⟩, ⟨4⟩, ⟨5⟩⟩ exampleSuspend),
        (⟨2⟩, expandedEntry ⟨⟨6⟩, ⟨7⟩, ⟨8⟩⟩ exampleSuspend),
        (⟨3⟩, exampleReturn)] := rfl

/-- Shadowed duplicate labels are separate row occurrences, not first-match
    CFG lookups. Their generated names are globally different. -/
theorem duplicate_labels_get_separate_triples :
    traceObservation (planAllBlocks (exampleRows true)).trace =
      [(1, [3, 4, 5]), (1, [6, 7, 8])] := rfl

theorem second_row_partial_capacity :
    let result := lowerRows 8 (exampleRows false)
    (traceObservation result.trace, result.cursor.reserved, result.cursor.next,
      result.visits, result.pending.map (fun row => row.1.index)) =
      ([(1, [3, 4, 5])], [7, 6, 5, 4, 3], 8, 8, [2, 3]) := rfl

/-- The capacity theorem is exercised with the real failed all-row plan,
    not a separately assumed occupied table. -/
theorem example_capacity_excludes_six :
    ¬ ∃ candidates : List Nat, candidates.length = 6 ∧ Distinct candidates ∧
      (∀ key ∈ candidates, key < 8) ∧
      (∀ key ∈ candidates, key ∉ graphReservations (exampleRows false)) := by
  intro proposed
  obtain ⟨candidates, census, distinct, inRange, unused⟩ := proposed
  have capacity := lowerRows_capacity_excludes_schedule 8 (exampleRows false)
  exact capacity candidates census distinct inRange unused

theorem no_suspend_needs_no_fresh_names :
    (lowerRows 0 [(⟨3⟩, exampleReturn)]).rows = [(⟨3⟩, exampleReturn)] ∧
      (lowerRows 0 [(⟨3⟩, exampleReturn)]).visits = 0 ∧
      Ready (lowerRows 0 [(⟨3⟩, exampleReturn)]) := ⟨rfl, rfl, True.intro⟩

/-- Expansion removes only a block's suspend TERMINATOR. This says
    nothing about instructions that may appear in a malformed body. -/
theorem expandedEntry_terminator_noSuspend (names : Names) (block : BasicBlock) :
    isSuspend (expandedEntry names block).terminator = false := by
  cases block with
  | mk params body destinations term termDestinations => cases term <;> rfl

/-- The actual row-by-row plan leaves no suspend terminator in any output
    occurrence, including shadowed duplicate labels and unreachable rows. -/
theorem Plans.noSuspends {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace)
    (row : BlockId × BasicBlock) (member : row ∈ target) :
    isSuspend row.2.terminator = false := by
  induction plan with
  | nil => cases member
  | keep _ _ _ _ notSuspend _ _ _ _ ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same; exact notSuspend
    · exact ih later
  | expand _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same; exact expandedEntry_terminator_noSuspend _ _
    · exact ih later

theorem Plans.suspendCount_target_zero {domain : Nat} {used : List Nat}
    {before after : Cursor domain used} {source target : Rows} {trace : Trace}
    (plan : Plans before after source target trace) : suspendCount target = 0 := by
  induction plan with
  | nil => rfl
  | keep _ _ _ _ notSuspend _ _ _ _ ih =>
    simp only [suspendCount, notSuspend, Bool.false_eq_true, if_false, Nat.zero_add, ih]
  | expand _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [suspendCount, expandedEntry_terminator_noSuspend, Bool.false_eq_true,
      if_false, Nat.zero_add, ih]

/-- A ready actual all-block planner output has no remaining CoroSuspend
    TERMINATORS. Body instruction inspection and evaluator correctness are
    separate obligations. -/
theorem planAllBlocks_ready_noSuspends (blocks : Rows) (ready : Ready (planAllBlocks blocks)) :
    suspendCount (planAllBlocks blocks).rows = 0 :=
  (lowerRows_ready u32Domain blocks ready).suspendCount_target_zero

end TrustIr.GenericCoroAllBlocksPlanner

#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.isSuspend == []
