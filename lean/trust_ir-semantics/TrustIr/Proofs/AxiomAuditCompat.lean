-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.CompilerCompat

/-- Select a diagnostic command before elaboration on the two pinned compilers.
    Both branches remain explicit; an unsupported compiler is refused. -/
macro "trustIrCompilerCommand " "(" legacy:command ")" "(" newer:command ")" : command => do
  if Lean.versionString == "4.8.0" then pure legacy
  else if Lean.versionString == "4.30.0-rc2" then pure newer
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR command selection"

/-- Preserve checks of compiler-generated names absent from the other pin.
    A separate exact modern family roster accounts for their replacements. -/
macro "trustIrCanonicalOnly " declaration:command : command => do
  if Lean.versionString == "4.8.0" then pure declaration
  else if Lean.versionString == "4.30.0-rc2" then pure ⟨Lean.mkNullNode #[]⟩
  else Lean.Macro.throwError "unsupported Lean compiler for canonical declaration audit"

macro "trustIrModernOnly " declaration:command : command => do
  if Lean.versionString == "4.8.0" then pure ⟨Lean.mkNullNode #[]⟩
  else if Lean.versionString == "4.30.0-rc2" then pure declaration
  else Lean.Macro.throwError "unsupported Lean compiler for modern declaration audit"

/-- Exact footprints for both pinned foundation libraries. Unlike the monotone
    port check above, this permits changes among the already accepted Lean-core
    trio: modern Float primitives and library proofs have different footprints.
    No other axiom can enter, and the project axiom is available only where the
    original canonical declaration already depended on it. -/
elab "#trustIrAxiomsByCompiler " subject:ident " == " "[" legacy:ident,* "]"
    " modern " "[" newer:ident,* "]" : command => do
  let canonical := legacy.getElems.map (·.getId)
  let newer := newer.getElems.map (·.getId)
  let core := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in canonical ++ newer do
    unless core.contains axiomName ||
        (axiomName == `TrustIr.ay_sound_unsat && canonical.contains axiomName) do
      Lean.throwError m!"axiom outside canonical TrustIR boundary: {axiomName}"
  let required ← if Lean.versionString == "4.8.0" then pure canonical
    else if Lean.versionString == "4.30.0-rc2" then pure newer
    else Lean.throwError "unsupported Lean compiler for exact foundation audit"
  let names ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstWithInfos subject
  for name in names do
    let actual ← trustIrCollectAxioms name
    for axiomName in actual do
      unless required.contains axiomName do
        Lean.throwError m!"unexpected axiom {axiomName} in {name}"
    for axiomName in required do
      unless actual.contains axiomName do
        Lean.throwError m!"missing expected axiom {axiomName} in {name}"
    Lean.logInfo m!"TrustIR compiler exact axiom audit: {name}: {actual.toList}"

/-- Refuse missing or newly generated members of an explicitly audited family.
    Each listed member has its own exact axiom check at the call site. -/
elab "#trustIrModernAxiomFamily " parent:ident " == " "[" expected:ident,* "]" : command => do
  unless Lean.versionString == "4.30.0-rc2" do
    Lean.throwError "modern axiom family must be selected only on its pinned compiler"
  let env ← Lean.getEnv
  let required := expected.getElems.map (·.getId)
  let familyRoot := parent.getId
  let mut actual : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if familyRoot.isPrefixOf name && name != familyRoot then
      actual := actual.push name
      unless required.contains name do
        Lean.throwError m!"unexpected generated declaration {name} in {familyRoot}"
  for name in required do
    unless actual.contains name do
      Lean.throwError m!"missing generated declaration {name} in {familyRoot}"
  Lean.logInfo m!"TrustIR exact modern family: {familyRoot}: {actual.size} declarations"

namespace TrustIr.AxiomAuditCompatControls
theorem no_axioms : True := True.intro
theorem uses_propext (p q : Prop) (equivalent : p ↔ q) : p = q := propext equivalent
namespace Family
def member : Nat := 0
end Family
end TrustIr.AxiomAuditCompatControls

-- Negative controls exercise the boundary and both directions of exactness.
/-- error: axiom outside canonical TrustIR boundary: sorryAx -/
#guard_msgs in
#trustIrAxiomsByCompiler TrustIr.AxiomAuditCompatControls.no_axioms == [] modern [sorryAx]

/-- error: axiom outside canonical TrustIR boundary: TrustIr.ay_sound_unsat -/
#guard_msgs in
#trustIrAxiomsByCompiler TrustIr.AxiomAuditCompatControls.no_axioms == [] modern [TrustIr.ay_sound_unsat]

/-- error: unexpected axiom propext in TrustIr.AxiomAuditCompatControls.uses_propext -/
#guard_msgs in
#trustIrAxiomsByCompiler TrustIr.AxiomAuditCompatControls.uses_propext == [] modern []

/-- error: missing expected axiom propext in TrustIr.AxiomAuditCompatControls.no_axioms -/
#guard_msgs in
#trustIrAxiomsByCompiler TrustIr.AxiomAuditCompatControls.no_axioms == [propext] modern [propext]

trustIrModernOnly
/-- error: unexpected generated declaration TrustIr.AxiomAuditCompatControls.Family.member in TrustIr.AxiomAuditCompatControls.Family -/
#guard_msgs in
#trustIrModernAxiomFamily TrustIr.AxiomAuditCompatControls.Family == []

trustIrModernOnly
/-- error: missing generated declaration TrustIr.AxiomAuditCompatControls.Family.absent in TrustIr.AxiomAuditCompatControls.Family -/
#guard_msgs in
#trustIrModernAxiomFamily TrustIr.AxiomAuditCompatControls.Family ==
  [TrustIr.AxiomAuditCompatControls.Family.member, TrustIr.AxiomAuditCompatControls.Family.absent]

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.AxiomAuditCompatControls.Family ==
  [TrustIr.AxiomAuditCompatControls.Family.member]

