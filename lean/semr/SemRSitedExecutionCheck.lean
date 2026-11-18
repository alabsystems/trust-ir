/- Copyright 2026 Andrew Yates. Apache-2.0.
   Questions over complete quoted programs, with concrete counterexamples. -/
import SemRSitedExecution

namespace SemR.SitedExecution.Check

def site : SitedDivPanic.Site := ⟨41, 1⟩

def DivContract : Prop := ∀ (s : SitedDivPanic.Site) (a b : Nat),
  a < modulus 64 → b < modulus 64 → b ≠ 0 →
  runFunction (model .divByZero s) 7 [.int .u64 a, .int .u64 b] 5 1 =
    .ret [.int .u64 (a / b)]

def RemContract : Prop := ∀ (s : SitedDivPanic.Site) (a b : Nat),
  a < modulus 64 → b < modulus 64 → b ≠ 0 →
  runFunction (model .remByZero s) 7 [.int .u64 a, .int .u64 b] 5 1 =
    .ret [.int .u64 (a % b)]

def ZeroContract : Prop := ∀ (kind : DivPanicKind) (s : SitedDivPanic.Site) (a : Nat),
  a < modulus 64 →
  runFunction (model kind s) 7 [.int .u64 a, .int .u64 0] 5 1 =
    .globalDivPanic ⟨kind, none, s.entry, s.global, 0⟩

def NoBadContract : Prop := ∀ (kind : DivPanicKind) (s : SitedDivPanic.Site) (a b : Nat),
  a < modulus 64 → b < modulus 64 → b ≠ 0 →
  ¬ BodyViolation (model kind s) (initial kind s a b)

theorem div_contract : DivContract := nonzero_run .divByZero
theorem rem_contract : RemContract := nonzero_run .remByZero
theorem zero_contract : ZeroContract := zero_run
theorem no_bad_contract : NoBadContract := nonzero_excludes_body_violation

def DivSample : Prop := execute .divByZero site 37 5 = .ret [.int .u64 7]
def RemSample : Prop := execute .remByZero site 37 5 = .ret [.int .u64 2]
def ZeroSample : Prop := execute .divByZero site 37 0 =
  .globalDivPanic ⟨.divByZero, none, 41, 1, 0⟩

theorem div_sample : DivSample := by rfl
theorem rem_sample : RemSample := by rfl
theorem zero_sample : ZeroSample := by rfl
theorem upper_word_boundary : execute .divByZero site 18446744073709551615 1 =
    .ret [.int .u64 18446744073709551615] := by rfl
theorem remainder_boundary : execute .remByZero site 18446744073709551615 2 =
    .ret [.int .u64 1] := by rfl

def bodyModel (body : List Node) : Module :=
  { model .divByZero site with functions :=
    [{ function .divByZero site with blocks :=
        [{ block .divByZero site with body := body }] },
     ⟨41, 1, 0, [], []⟩, ⟨42, 1, 0, [], []⟩] }

def swappedNodes : List Node := (nodes .divByZero site).map fun node =>
  match node.inst with
  | .binop _ ty lhs rhs => { node with inst := .binop .urem ty lhs rhs }
  | _ => node

def unguardedNodes : List Node := (nodes .divByZero site).filter fun node =>
  match node.inst with
  | .assertSitedDiv _ _ _ => false
  | _ => true

theorem actual_swapped_body :
    runFunction (bodyModel swappedNodes) 7 [.int .u64 37, .int .u64 5] 5 1 =
      .ret [.int .u64 2] := by rfl
theorem actual_removed_guard :
    runFunction (bodyModel unguardedNodes) 7 [.int .u64 37, .int .u64 0] 5 1 =
      .ub "unsigned division by zero" := by rfl
theorem actual_other_receiver :
    runFunction (model .divByZero site) 42 [.int .u64 37, .int .u64 5] 5 1 =
      .unsupported "interprocedural_call" := by rfl
theorem actual_short_budget :
    runFunction (model .divByZero site) 7 [.int .u64 37, .int .u64 5] 2 1 =
      .outOfFuel := by rfl

def WrongDivResult : Prop := execute .divByZero site 37 5 = .ret [.int .u64 8]
def WrongRemResult : Prop := execute .remByZero site 37 5 = .ret [.int .u64 3]
def WrongEntry : Prop := execute .divByZero site 37 0 =
  .globalDivPanic ⟨.divByZero, none, 42, 1, 0⟩
def WrongGlobal : Prop := execute .divByZero site 37 0 =
  .globalDivPanic ⟨.divByZero, none, 41, 0, 0⟩
def WrongKind : Prop := execute .divByZero site 37 0 =
  .globalDivPanic ⟨.remByZero, none, 41, 1, 0⟩
def WrongOperands : Prop := execute .divByZero site 37 0 =
  .globalDivPanic ⟨.divByZero, some [], 41, 1, 0⟩
def WrongSwappedBody : Prop :=
  runFunction (bodyModel swappedNodes) 7 [.int .u64 37, .int .u64 5] 5 1 =
    .ret [.int .u64 7]
def WrongRemovedGuard : Prop :=
  runFunction (bodyModel unguardedNodes) 7 [.int .u64 37, .int .u64 0] 5 1 =
    .globalDivPanic ⟨.divByZero, none, 41, 1, 0⟩
def WrongReceiver : Prop :=
  runFunction (model .divByZero site) 42 [.int .u64 37, .int .u64 5] 5 1 =
    .ret [.int .u64 7]
def WrongBudget : Prop :=
  runFunction (model .divByZero site) 7 [.int .u64 37, .int .u64 5] 2 1 =
    .ret [.int .u64 7]
def MissingNonzero : Prop := ∀ (kind : DivPanicKind) (s : SitedDivPanic.Site) (a b : Nat),
  a < modulus 64 → b < modulus 64 →
  execute kind s a b = .ret [.int .u64 (result kind a b)]

theorem wrong_div_result : ¬ WrongDivResult := by intro h; cases h
theorem wrong_rem_result : ¬ WrongRemResult := by intro h; cases h
theorem wrong_entry : ¬ WrongEntry := by intro h; cases h
theorem wrong_global : ¬ WrongGlobal := by intro h; cases h
theorem wrong_kind : ¬ WrongKind := by intro h; cases h
theorem wrong_operands : ¬ WrongOperands := by intro h; cases h
theorem wrong_swapped_body : ¬ WrongSwappedBody := by intro h; cases h
theorem wrong_removed_guard : ¬ WrongRemovedGuard := by intro h; cases h
theorem wrong_receiver : ¬ WrongReceiver := by intro h; cases h
theorem wrong_budget : ¬ WrongBudget := by intro h; cases h
theorem nonzero_is_essential : ¬ MissingNonzero := by
  intro allInputs
  have impossible := allInputs .divByZero site 37 0 (by decide) (by decide)
  cases impossible

end SemR.SitedExecution.Check
