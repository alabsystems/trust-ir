/- Copyright 2026 Andrew Yates. Apache-2.0.
   Complete quoted function execution, not a Rust or emitted-byte binding. -/
import SemRSitedDivPanic

namespace SemR.SitedExecution

def operation : DivPanicKind → BinOp
  | .divByZero => .udiv
  | .remByZero => .urem

def result : DivPanicKind → Nat → Nat → Nat
  | .divByZero, a, b => a / b
  | .remByZero, a, b => a % b

def nodes (kind : DivPanicKind) (site : SitedDivPanic.Site) : List Node :=
  [⟨.const (.int .u64) (.int 0), [2]⟩,
   ⟨.icmp .ne (.int .u64) 1 2, [3]⟩,
   ⟨.assertSitedDiv 3 kind site, []⟩,
   ⟨.binop (operation kind) (.int .u64) 0 1, [4]⟩,
   ⟨.ret [4], []⟩]

def block (kind : DivPanicKind) (site : SitedDivPanic.Site) : Block :=
  ⟨0, [(0, .int .u64), (1, .int .u64)], nodes kind site⟩

def function (kind : DivPanicKind) (site : SitedDivPanic.Site) : Func :=
  ⟨7, 0, 0, [block kind site], []⟩

def model (kind : DivPanicKind) (site : SitedDivPanic.Site) : Module :=
  { funcTys := [⟨[.int .u64, .int .u64], [.int .u64], false⟩,
                 ⟨[.ptr], [], false⟩],
    enums := [],
    functions := [function kind site, ⟨41, 1, 0, [], []⟩, ⟨42, 1, 0, [], []⟩] }

def initial (kind : DivPanicKind) (site : SitedDivPanic.Site) (a b : Nat) : Core :=
  { fn := function kind site,
    sig := ⟨[.int .u64, .int .u64], [.int .u64], false⟩,
    block := block kind site, pc := 0,
    env := [(1, .int .u64 b), (0, .int .u64 a)], depth := 1,
    stack := [], openFrames := [], nextFrame := 0, mem := Mem.empty }

def execute (kind : DivPanicKind) (site : SitedDivPanic.Site) (a b : Nat) : Out :=
  runFunction (model kind site) 7 [.int .u64 a, .int .u64 b] 5 1

theorem word_typed (a : Nat) (bound : a < modulus 64) :
    expectTy 64 (.int .u64 a) (.int .u64) = .ok () := by
  change (if a < modulus 64 then R.ok () else
    tyR "TypeError: integer value is out of range for the target width") = .ok ()
  exact if_pos bound

theorem result_le (kind : DivPanicKind) (a b : Nat) : result kind a b ≤ a := by
  cases kind with
  | divByZero => exact Nat.div_le_self a b
  | remByZero => exact Nat.mod_le a b

theorem result_bound (kind : DivPanicKind) (a b : Nat) (bound : a < modulus 64) :
    result kind a b < modulus 64 :=
  Nat.lt_of_le_of_lt (result_le kind a b) bound

theorem guard_value (b : Nat) (bound : b < modulus 64) :
    evalIcmp 64 .ne (.int .u64) (.int .u64 b) (.int .u64 0) =
      .ok (.bool (b != 0)) := by
  simp [evalIcmp, word_typed b bound, word_typed 0 (by decide),
    isBoolTy, expectInt, rejectPoison, icmpR, pure, ok_bind] <;> rfl

theorem arithmetic_value (kind : DivPanicKind) (a b : Nat)
    (ha : a < modulus 64) (hb : b < modulus 64) (nonzero : b ≠ 0) :
    evalBinop 64 (operation kind) (.int .u64) (.int .u64 a) (.int .u64 b) =
      .ok (.int .u64 (result kind a b)) := by
  cases kind <;>
    simp [operation, result, evalBinop, word_typed a ha, word_typed b hb,
      isBoolTy, expectInt, rejectPoison, intBin, nonzero, liftOp, pure, ok_bind] <;> rfl

theorem start_exact (kind : DivPanicKind) (site : SitedDivPanic.Site) (a b : Nat)
    (ha : a < modulus 64) (hb : b < modulus 64) :
    start (model kind site) 7 [.int .u64 a, .int .u64 b] 1 = .ok (initial kind site a b) := by
  simp [start, model, function, block, initial, nth?, Module.pointerBits, Module.executableTarget,
    checkSig, rejectPoison, word_typed a ha, word_typed b hb,
    Val.ty, Ty.beq, IntTy.code, findBlock, bindParams] <;> rfl

theorem nonzero_run (kind : DivPanicKind) (site : SitedDivPanic.Site) (a b : Nat)
    (ha : a < modulus 64) (hb : b < modulus 64) (nonzero : b ≠ 0) :
    execute kind site a b = .ret [.int .u64 (result kind a b)] := by
  have guard : (b != 0) = true := by
    change (!(b == 0)) = true
    cases h : (b == 0) with
    | false => rfl
    | true => exact False.elim (nonzero (eq_of_beq h))
  unfold execute runFunction
  rw [start_exact kind site a b ha hb]
  simp [run, stepCore, initial, model, function, block, nodes, nth?, execNode,
    constStep, constVal, Module.pointerBits, binopStep, icmpStep, getV, lookupEnv,
    guard_value b hb, arithmetic_value kind a b ha hb nonzero, bindResults, next,
    SitedDivPanic.step, SitedDivPanic.on, asBool, rejectPoison, guard, ofR,
    retStep, getVs, checkSig, returnTo, word_typed _ (result_bound kind a b ha),
    Val.ty, Ty.beq, IntTy.code, pure, ok_bind] <;> rfl

theorem zero_run (kind : DivPanicKind) (site : SitedDivPanic.Site) (a : Nat)
    (ha : a < modulus 64) :
    execute kind site a 0 = .globalDivPanic ⟨kind, none, site.entry, site.global, 0⟩ := by
  unfold execute runFunction
  rw [start_exact kind site a 0 ha (by decide)]
  simp [run, stepCore, initial, model, function, block, nodes, nth?, execNode,
    constStep, constVal, Module.pointerBits, icmpStep, getV, lookupEnv,
    guard_value 0 (by decide), bindResults, next, SitedDivPanic.step,
    SitedDivPanic.on, SitedDivPanic.failure, asBool, rejectPoison, ofR,
    pure, ok_bind] <;> rfl

theorem nonzero_exec (kind : DivPanicKind) (site : SitedDivPanic.Site) (a b : Nat)
    (ha : a < modulus 64) (hb : b < modulus 64) (nonzero : b ≠ 0) :
    Exec (model kind site) 5 (initial kind site a b)
      (.ret [.int .u64 (result kind a b)]) := by
  have returned := nonzero_run kind site a b ha hb nonzero
  unfold execute runFunction at returned
  rw [start_exact kind site a b ha hb] at returned
  dsimp only at returned
  have execution := run_sound (model kind site) 5 (initial kind site a b)
  rw [returned] at execution
  exact execution

theorem zero_exec (kind : DivPanicKind) (site : SitedDivPanic.Site) (a : Nat)
    (ha : a < modulus 64) :
    Exec (model kind site) 5 (initial kind site a 0)
      (.globalDivPanic ⟨kind, none, site.entry, site.global, 0⟩) := by
  have returned := zero_run kind site a ha
  unfold execute runFunction at returned
  rw [start_exact kind site a 0 ha (by decide)] at returned
  dsimp only at returned
  have execution := run_sound (model kind site) 5 (initial kind site a 0)
  rw [returned] at execution
  exact execution

theorem nonzero_excludes_body_violation (kind : DivPanicKind) (site : SitedDivPanic.Site)
    (a b : Nat) (ha : a < modulus 64) (hb : b < modulus 64) (nonzero : b ≠ 0) :
    ¬ BodyViolation (model kind site) (initial kind site a b) := by
  have returned := nonzero_run kind site a b ha hb nonzero
  unfold execute runFunction at returned
  rw [start_exact kind site a b ha hb] at returned
  dsimp only at returned
  exact returned_excludes_body_violation (model kind site) (initial kind site a b)
    5 [.int .u64 (result kind a b)] returned

end SemR.SitedExecution
