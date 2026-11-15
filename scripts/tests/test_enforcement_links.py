"""Regressions for `scripts/check_enforcement_links.py`.

Two halves.  The SYNTHETIC half builds a tiny tree and pins each rule in
isolation.  The LIVE half mutates the repository's real governed documents IN
MEMORY (nothing is written) and proves the gate fires on them: a gate that has
only ever been seen green has not been seen to work.
"""

from __future__ import annotations

import importlib.util
import os
import re
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from typing import Dict, List, Optional
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
TOOL_PATH = ROOT / "scripts" / "check_enforcement_links.py"

SPEC = importlib.util.spec_from_file_location("check_enforcement_links", TOOL_PATH)
assert SPEC is not None and SPEC.loader is not None
TOOL = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = TOOL
SPEC.loader.exec_module(TOOL)

SPEC_DOC = "docs/SPEC_RATIFICATIONS.md"

LIB_RS = """
pub enum Shape { Circle, Square { side: u32 } }
pub struct Config { pub name: String, pub table: std::collections::HashMap<u8, Vec<u8>> }
impl Config { pub fn validate(&self) -> bool { true } }
impl<const N: usize> Buffer<N> { pub fn capacity(&self) -> usize { N } }
pub struct Buffer<const N: usize>;
pub const KERNEL_ANCHOR_DEMO: &str = "demo";
pub const LIMIT: u32 = 4;
pub const fn helper() -> u32 { 1 }
pub struct Report<'a> { module: &'a str }
impl<'a> Report<'a> { pub fn surface(&self) -> &'a str { self.module } }
pub enum LeafG<X> { Plain, Holder(X) }
pub type Leaf = LeafG<Never>;
pub type Other = LeafG<u8>;
macro_rules! typed_id { ($name:ident) => { pub struct $name(u32); }; }
typed_id! {
    /// A macro-defined id.
    HandleId
}
typed_id!(
    /// The paren form.
    SlotId
);
fn uses_a_macro() { let _ = vec! { NotAType }; drop(format!(NorThis)); }
// fn commented_out() {}
const TEXT: &str = "fn in_a_string() {}";
#[cfg(test)]
mod tests {
    #[test]
    fn config_validates() { assert!(super::helper() == 1); }
    fn not_a_test() {}
}
"""

VALIDATE_RS = """
pub enum ValidationError {
    /// Tested and constructed.
    Tested { block: u32 },
    /// Constructed, but no test names it.
    Untested,
    /// Defined and displayed, never built: a refusal that cannot fire.
    Dead(u32),
}
impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValidationError::Tested { block } => write!(f, "{block}"),
            ValidationError::Untested => write!(f, "untested"),
            ValidationError::Dead(n) => write!(f, "{n}"),
        }
    }
}
pub fn validate(flag: bool) -> Vec<ValidationError> {
    let mut errors = vec![ValidationError::Tested { block: 0 }];
    if flag { errors.push(ValidationError::Untested); }
    if let Some(ValidationError::Dead(_)) = errors.first() {}
    errors
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn the_tested_rule_fires() {
        assert!(matches!(validate(false)[0], ValidationError::Tested { .. }));
    }
}
"""

LEDGER = """
# comment
units-without-checked-evidence               2026-01-01 1 initial census
validation-error-variants-unnamed            2026-01-01 2 initial census
validation-error-variants-never-constructed  2026-01-01 1 initial census
member units-without-checked-evidence docs/SPEC_RATIFICATIONS.md §2
member validation-error-variants-unnamed Dead
member validation-error-variants-unnamed Untested
member validation-error-variants-never-constructed Dead
"""
SECTION_3 = "member units-without-checked-evidence docs/SPEC_RATIFICATIONS.md §3\n"

GOOD_SPEC = """
# Ratifications

Preamble, not a unit.

## 1. Backed by a test

Rule one.

*Enforcement (test):* `config_validates` and the file
`crates/demo/tests/rules.rs`.

## 2. Backed by nothing

Rule two.

*Enforcement (prose-only):* nothing; `Config` is merely mentioned.
"""


# Parsed, never compiled.  Rule E5 reads these statements: `demo_is_ub`
# reads UB (and holds `zero` only after a `≠`), `demo_runs` runs,
# `demo_quoted` names `zero` only inside a string literal, `demo_odd` is
# outside the reader (names only), `demo_undelimited` has no `:=` to end its
# statement, and `demo_holds : True` names nothing.
DEMO_LEAN = """\
namespace Demo
theorem demo_holds : True := trivial
def demo_def := 1
def zero : Nat := 0
def op (n : Nat) : Nat := n
def run (n : Nat) : Except Err Nat := .ok n
def outcome (n : Nat) : String := s!"ok:{n}"
theorem demo_is_ub (s : Nat) (h : s ≠ zero) : run (op s) = .error (.ub "zero") := sorry
theorem demo_runs : run (op zero) = .ok 0 := rfl
theorem demo_quoted : run (op 1) = .error (.ub "zero") := sorry
-- a conclusion no rule of the reader classifies
theorem demo_odd (a : Nat) : op a = op a + 0 := rfl
-- no `:=` follows: the reader cannot delimit this statement
theorem demo_undelimited (n : Nat) : op n = n
end Demo
"""


LEAN_CENSUS = """\
-- `Lean.ofReduceBool` is admitted only in these (a comment naming `TrustIr.NotThis`).
def nativeDecideModules : List Name :=
  [`TrustIr.Fixtures]
"""


def write_tree(root: Path, files: Dict[str, str]) -> None:
    for name, text in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(text).lstrip("\n"), encoding="utf-8")


def synthetic(root: Path, spec: str = GOOD_SPEC, extra: Optional[Dict[str, str]] = None) -> None:
    files = {
        "Cargo.toml": '[workspace]\nmembers = [\n    "crates/demo",\n    "crates/trust-ir-build",\n]\n',
        "crates/demo/Cargo.toml": (
            '[package]\nname = "demo"\n\n[features]\ndefault = [\n    "std",  # a multi-line array\n]\n'
            'std = ["always-on", "dep:serde", "other/feature"]\nalways-on = []\nextra = []\n'
        ),
        "crates/demo/src/lib.rs": LIB_RS,
        "crates/demo/tests/rules.rs": "#[test]\nfn shape_is_checked() {}\n",
        "crates/demo/tests/fixtures/golden_one.tmbc": "x",
        "crates/trust-ir-build/Cargo.toml": '[package]\nname = "trust-ir-build"\n',
        "crates/trust-ir-build/src/validate.rs": VALIDATE_RS,
        "reports/old/tests/ghost.rs": "#[test]\nfn ghost_test() {}\n",
        # The Lean package the `lean-proofs` gate builds: the import closure of
        # its root, with one native_decide fixture module named by the census.
        "lean/trust_ir-semantics/TrustIr.lean": "import TrustIr.Demo\nimport TrustIr.Audit\nimport TrustIr.Fixtures\n",
        "lean/trust_ir-semantics/TrustIr/Demo.lean": DEMO_LEAN,
        "lean/trust_ir-semantics/TrustIr/Audit.lean": "#guard_msgs in\n#print axioms Demo.demo_holds\n",
        "lean/trust_ir-semantics/TrustIr/Fixtures.lean": "namespace Fixtures\ntheorem fixture_evaluates : Demo.outcome 4 = \"ok:4\" := by native_decide\nend Fixtures\n",
        "lean/trust_ir-semantics/ProofCensus.lean": LEAN_CENSUS,
        # ... and Lean no standing gate compiles.
        "lean/Stray.lean": "namespace Stray\ntheorem stray_holds : True := trivial\nend Stray\n",
        "lean/StrayAudit.lean": "#guard_msgs in\n#print axioms Stray.stray_holds\n",
        "scripts/ci_gates.sh": "gate demo-gate true\n",
        "scripts/gates/enforcement-ratchet.txt": LEDGER,
        SPEC_DOC: spec,
    }
    files.update(extra or {})
    write_tree(root, files)


ONLY_SPEC = (TOOL.Doc(SPEC_DOC, "sections", exported=False),)


def findings(spec: str = GOOD_SPEC, extra: Optional[Dict[str, str]] = None, governed=ONLY_SPEC, **kwargs) -> List[str]:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        synthetic(root, spec, extra)
        report = TOOL.run(root, base_ref=None, governed=governed, **kwargs)
        return [str(f) for f in report.findings]


def section(entry: str) -> str:
    return GOOD_SPEC + "\n## 3. Under test\n\nRule three.\n\n" + entry + "\n"


def besides_the_ratchet(found: List[str]) -> List[str]:
    """A `(code)` or `(external)` section is NOT checked evidence, so adding one
    correctly trips E4.  Tests of E2/E3 look past that one finding."""
    return [f for f in found if "[E4]" not in f]


class TheSyntheticTreeIsGreen(unittest.TestCase):
    def test_a_well_formed_tree_passes(self) -> None:
        self.assertEqual(findings(), [])


class TheLeanBuildScopeFailsClosed(unittest.TestCase):
    CENSUS = "lean/trust_ir-semantics/ProofCensus.lean"

    def test_an_unreadable_fixture_list_is_a_finding(self) -> None:
        found = findings(extra={self.CENSUS: "-- the list was deleted\n"})
        self.assertTrue(any("cannot read the native_decide fixture modules" in f for f in found), found)

    def test_a_fixture_module_nothing_builds_is_a_finding(self) -> None:
        found = findings(extra={self.CENSUS: LEAN_CENSUS.replace("TrustIr.Fixtures]", "TrustIr.Fixtures, `TrustIr.Gone]")})
        self.assertTrue(any("`TrustIr.Gone`" in f and "does not build" in f for f in found), found)

    def test_a_package_without_its_census_is_a_finding(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            synthetic(root)
            (root / self.CENSUS).unlink()
            report = TOOL.run(root, base_ref=None, governed=ONLY_SPEC)
            self.assertTrue(any("has no census file" in str(f) for f in report.findings), report.findings)


class E1EveryUnitNamesItsEnforcement(unittest.TestCase):
    def test_a_section_without_an_entry_is_refused(self) -> None:
        found = findings(GOOD_SPEC + "\n## 3. Silent\n\nA rule nobody enforces.\n")
        self.assertEqual(len(found), 1, found)
        self.assertIn("[E1] §3", found[0])
        self.assertIn("no Enforcement entry", found[0])

    def test_the_legacy_unclassified_line_is_refused(self) -> None:
        found = findings(section("*Enforcement:* `config_validates`."))
        self.assertTrue(any("no evidence class" in f for f in found), found)

    def test_an_unknown_class_is_refused(self) -> None:
        found = findings(section("*Enforcement (proven):* `config_validates`."))
        self.assertTrue(any("unknown evidence class `proven`" in f for f in found), found)

    def test_a_label_buried_mid_paragraph_is_refused(self) -> None:
        found = findings(section("Some prose. *Enforcement (test):* `config_validates`."))
        self.assertTrue(any("must START its paragraph" in f for f in found), found)

    def test_a_reasoned_opt_out_is_honoured_and_a_bare_one_is_not(self) -> None:
        reasoned = GOOD_SPEC + "\n## Changelog\n\n<!-- enforcement-links: not-normative a dated list, states no rule -->\n\nText.\n"
        self.assertEqual(findings(reasoned), [])
        bare = GOOD_SPEC + "\n## Changelog\n\n<!-- enforcement-links: not-normative -->\n\nText.\n"
        self.assertTrue(any("must say WHY" in f for f in findings(bare)))


class E2EveryCitationResolves(unittest.TestCase):
    def test_a_missing_path_is_refused(self) -> None:
        found = findings(section("*Enforcement (test):* `config_validates`, `crates/demo/tests/gone.rs`."))
        self.assertTrue(any("[E2]" in f and "gone.rs" in f for f in found), found)

    def test_a_renamed_test_function_is_refused(self) -> None:
        found = findings(section("*Enforcement (test):* `config_validates_renamed`."))
        self.assertTrue(any("no item named `config_validates_renamed`" in f for f in found), found)

    def test_a_qualifier_must_match_where_the_item_lives(self) -> None:
        self.assertEqual(findings(section("*Enforcement (test):* `demo::tests::config_validates`.")), [])
        found = findings(section("*Enforcement (test):* `validate::tests::config_validates`."))
        self.assertTrue(any("but not under `validate::tests`" in f for f in found), found)

    def test_a_test_no_package_owns_is_not_in_the_tree(self) -> None:
        # reports/old/tests/ghost.rs is no workspace member: nothing can run it.
        found = findings(section("*Enforcement (test):* `ghost_test`."))
        self.assertTrue(any("no item named `ghost_test`" in f for f in found), found)

    def test_an_excluded_package_test_counts_only_where_a_gate_runs_it(self) -> None:
        # `frontend/` is excluded from the workspace: its tests are code only
        # when a registry lists their target AND ci_gates.sh runs that
        # registry by the package's manifest path.
        excluded = {
            "Cargo.toml": (
                '[workspace]\nmembers = [\n    "crates/demo",\n    "crates/trust-ir-build",\n]\n'
                'exclude = ["frontend"]\n'
            ),
            "frontend/Cargo.toml": '[package]\nname = "frontend"\n\n[workspace]\n',
            "frontend/tests/gated.rs": "#[test]\nfn gated_test() {}\n",
            "frontend/tests/ungated.rs": "#[test]\nfn ungated_test() {}\n",
            "scripts/gates/fl.frontend.tests": "# gate fl\ngated  # the one target it runs\n",
            "scripts/ci_gates.sh": "gate demo-gate true\ngate fl run_excluded_registry fl frontend\n",
        }
        self.assertEqual(findings(section("*Enforcement (test):* `gated_test`."), extra=excluded), [])
        found = findings(section("*Enforcement (test):* `ungated_test`."), extra=excluded)
        self.assertTrue(any("no item named `ungated_test`" in f for f in found), found)
        # The registry alone is not a run: without the gate line nothing runs it.
        unwired = dict(excluded, **{"scripts/ci_gates.sh": "gate demo-gate true\n"})
        found = findings(section("*Enforcement (test):* `gated_test`."), extra=unwired)
        self.assertTrue(any("no item named `gated_test`" in f for f in found), found)
        # A package the workspace does not exclude is not read this way.
        not_excluded = dict(excluded, **{"Cargo.toml": excluded["Cargo.toml"].replace('exclude = ["frontend"]\n', "")})
        found = findings(section("*Enforcement (test):* `gated_test`."), extra=not_excluded)
        self.assertTrue(any("no item named `gated_test`" in f for f in found), found)

    def test_comments_and_strings_define_nothing(self) -> None:
        for ghost in ("commented_out", "in_a_string"):
            found = findings(section(f"*Enforcement (code):* `{ghost}`."))
            self.assertTrue(any(f"no item named `{ghost}`" in f for f in found), (ghost, found))

    def test_methods_variants_fields_features_gates_and_fixtures_resolve(self) -> None:
        entry = (
            "*Enforcement (code):* `Config::validate`, `Shape::Square`, `Config.name`, `helper`,\n"
            "`Buffer::capacity`, `LIMIT`, `extra`, `demo-gate`, `golden_one`, `demo`."
        )
        self.assertEqual(besides_the_ratchet(findings(section(entry))), [])

    def test_a_level_alias_carries_its_carriers_variants(self) -> None:
        # Amendment S: `type Leaf = LeafG<..>;` is the level-R spelling of the
        # level-generic carrier, so `Leaf::Plain` resolves to `LeafG`'s variant.
        self.assertEqual(besides_the_ratchet(findings(section("*Enforcement (code):* `Leaf::Plain`, `LeafG::Holder`."))), [])
        # Only the `NAME = NAMEG<..>` shape is followed: another alias is not.
        found = findings(section("*Enforcement (code):* `Other::Plain`."))
        self.assertTrue(any("not under `Other`" in f for f in found), found)

    def test_a_lifetime_generic_impl_keeps_its_type(self) -> None:
        # `impl<'a> Report<'a>`: two lifetimes on one line read as a char literal.
        self.assertEqual(besides_the_ratchet(findings(section("*Enforcement (code):* `Report::surface`."))), [])

    def test_an_item_level_macro_defines_the_type_it_leads_with(self) -> None:
        self.assertEqual(besides_the_ratchet(findings(section("*Enforcement (code):* `HandleId`, `SlotId`."))), [])
        self.assertTrue(any("`NorThis`" in f for f in findings(section("*Enforcement (code):* `NorThis`."))))
        # ... but a macro CALL inside a function body defines nothing.
        found = findings(section("*Enforcement (code):* `NotAType`."))
        self.assertTrue(any("no item named `NotAType`" in f for f in found), found)

    def test_a_generic_comma_mints_no_field(self) -> None:
        found = findings(section("*Enforcement (code):* `Config`, `Config.Vec`."))
        self.assertTrue(any("`Vec`" in f for f in found), found)

    def test_an_external_entry_is_not_resolved_but_must_name_something(self) -> None:
        external = section("*Enforcement (external):* `../other/src/thing.rs`, `not_here`.")
        self.assertEqual(besides_the_ratchet(findings(external)), [])
        found = findings(section("*Enforcement (external):* somebody else checks it."))
        self.assertTrue(any("must NAME the artifact" in f for f in found), found)


class E3AClassIsWitnessedNotAsserted(unittest.TestCase):
    def refused(self, entry: str) -> None:
        found = findings(section(entry))
        self.assertTrue(any("[E3]" in f and "is not witnessed" in f for f in found), (entry, found))

    def test_a_plain_function_does_not_witness_a_test(self) -> None:
        self.refused("*Enforcement (test):* `helper`.")
        self.refused("*Enforcement (test):* `not_a_test`.")

    def test_a_source_file_holding_an_inline_test_module_does_not_witness_a_test(self) -> None:
        self.refused("*Enforcement (test):* `crates/demo/src/lib.rs`.")

    def test_each_test_artifact_kind_witnesses_a_test(self) -> None:
        for cited in (
            "config_validates",
            "crates/demo/tests/rules.rs",
            "demo::tests",
            "lean/trust_ir-semantics/TrustIr/Audit.lean",
            "lean/trust_ir-semantics/ProofCensus.lean",
        ):
            self.assertEqual(findings(section(f"*Enforcement (test):* `{cited}`.")), [], cited)

    def test_a_gate_name_or_a_fixture_witnesses_nothing_on_its_own(self) -> None:
        # Both RESOLVE (they exist), and naming one is a rewording: `workspace-format`
        # is a gate, and it is not evidence that an interpreter is normative.
        for cited in ("demo-gate", "golden_one"):
            self.refused(f"*Enforcement (test):* the `{cited}` gate runs it.")
            self.assertEqual(besides_the_ratchet(findings(section(f"*Enforcement (code):* `{cited}`."))), [], cited)
        # Beside the test it runs, a gate name is fine.
        self.assertEqual(findings(section("*Enforcement (test):* `config_validates`, run by `demo-gate`.")), [])

    def test_a_lean_definition_is_not_a_theorem(self) -> None:
        self.refused("*Enforcement (lean-theorem):* `demo_def`.")
        self.assertEqual(findings(section("*Enforcement (lean-theorem):* `op` of `zero` runs (`Demo.demo_runs`).")), [])

    def test_a_theorem_no_standing_gate_builds_is_not_a_lean_theorem(self) -> None:
        # `lean/Stray.lean` is outside the TrustIr import closure: it RESOLVES
        # (it exists, so a `(code)` entry may name it) and proves nothing.
        self.refused("*Enforcement (lean-theorem):* `Stray.stray_holds`.")
        self.assertEqual(besides_the_ratchet(findings(section("*Enforcement (code):* `Stray.stray_holds`."))), [])
        # ... and a `#guard_msgs` file nothing compiles is not a test.
        self.refused("*Enforcement (test):* `lean/StrayAudit.lean`.")

    def test_a_native_decide_fixture_is_a_test_and_not_a_theorem(self) -> None:
        # The census admits `Lean.ofReduceBool` in `TrustIr.Fixtures` only: its
        # theorems are evaluations the Lean compiler decides.
        self.refused("*Enforcement (lean-theorem):* `fixture_evaluates`.")
        self.assertEqual(findings(section("*Enforcement (test):* `fixture_evaluates`.")), [])
        # Beside a kernel-checked theorem, citing one is fine.
        self.assertEqual(
            findings(section("*Enforcement (lean-theorem):* `op` of `zero` runs (`Demo.demo_runs`), and `outcome` of 4 runs (`fixture_evaluates`).")),
            [],
        )

    def test_a_kernel_certificate_needs_a_kernel_anchor(self) -> None:
        self.refused("*Enforcement (kernel-certificate):* `LIMIT`.")
        self.assertEqual(findings(section("*Enforcement (kernel-certificate):* `KERNEL_ANCHOR_DEMO`.")), [])

    def test_type_level_needs_a_type_or_a_feature_that_is_really_off_by_default(self) -> None:
        self.refused("*Enforcement (type-level):* `helper`.")
        self.assertEqual(findings(section("*Enforcement (type-level):* `Shape` has no such variant.")), [])
        self.assertEqual(findings(section("*Enforcement (type-level):* the `extra` feature is off.")), [])
        # "Off by default" is CHECKED against the manifest's `default` closure
        # (here through a multi-line array and one hop), not read off the name.
        for on in ("std", "always-on"):
            self.refused(f"*Enforcement (type-level):* the `{on}` feature is off.")
            self.assertEqual(besides_the_ratchet(findings(section(f"*Enforcement (code):* `{on}`."))), [], on)

    def test_the_default_closure_ignores_optional_deps_and_other_crates(self) -> None:
        features = TOOL.manifest_features('[features]\ndefault = ["a"]\na = ["dep:x", "y/z", "b"]\nb = []\n[dependencies]\nc = "1"\n')
        self.assertEqual({k: v[1] for k, v in features.items()}, {"default": ["a"], "a": ["b"], "b": []})

    def test_rewording_cannot_raise_a_class(self) -> None:
        # The same citation, relabelled: the witness rule is what refuses it.
        self.assertEqual(besides_the_ratchet(findings(section("*Enforcement (code):* `Config::validate`."))), [])
        self.refused("*Enforcement (test):* `Config::validate` is thoroughly tested.")


# The REAL laws file: gate 13's MUTANTS name its laws, so a synthetic tree that
# is to hold any law carries this text (and a mutation of it), never a fake.
LAWS_FILE = "crates/trust-ir-laws/src/laws.rs"
LAWS_TEXT = (ROOT / LAWS_FILE).read_text(encoding="utf-8")
IR_INST_RS = """
impl AllocOrigin {
    pub const fn is_reference_counted(self) -> bool { matches!(self, AllocOrigin::SwiftHeap | AllocOrigin::CleanHeap) }
}
"""
IR_LIB_RS = """
impl Linkage {
    pub const fn is_interposable(self) -> bool { matches!(self, Linkage::Weak) }
    pub const fn is_module_local(self) -> bool { matches!(self, Linkage::Internal) }
}
impl ExternRefSite {
    pub const fn admits_shape(self, kind: ObligationKindShape) -> bool { false }
}
"""
LAWS_LIB_RS = """
pub fn coverage_supports(far: u64, needs: u64) -> bool { far >= needs }
pub fn proof_ref_kind_is_ambiguous(kind: ObligationKindShape) -> bool { false }
pub fn license_admits_body(gate: GateShape, unlicensed: UnlicensedBodyPolicy) -> bool { false }
#[cfg(trust_verify)]
pub mod laws;
"""
# The validator's private by-reference wrapper: the table's name, not the table.
BUILD_KINDS_RS = """
fn proof_ref_kind_is_ambiguous(kind: &ObligationKind) -> bool { trust_ir_laws::proof_ref_kind_is_ambiguous(kind.shape()) }
"""


def law_enums_rs() -> str:
    """Every enum the real laws' cell tables range over, with the variants
    gate 13 reads for it in THIS tree: a synthetic tree carries the real laws
    file, so it must carry their real domains (`holding` holds every cell)."""
    gate13 = TOOL.gate13
    defs, errors = gate13.enum_definitions(ROOT, gate13.cell_enum_names(LAWS_TEXT))
    assert not errors, errors
    return "".join(f"pub enum {name} {{ {', '.join(ds[0].variants)} }}\n" for name, ds in sorted(defs.items()))


LAW_ENUMS_RS = law_enums_rs()
UNFLIPPED_LAW = "\npub fn coverage_unflipped() -> bool\n    ensures result\n{\n    coverage_supports(CoverageBound::Unbounded, CoverageBound::Unbounded)\n}\n"
RC_LAWS = "`laws::rc_swift_heap`, `laws::rc_clean_heap`, `laws::rc_rust_heap`, `laws::rc_c_malloc`"
# The same four laws, each given the verdict its `ensures` states (rule E5).
RC_VERDICTS = "true at `laws::rc_swift_heap`, `laws::rc_clean_heap`; false at `laws::rc_rust_heap`, `laws::rc_c_malloc`"


def with_laws(laws_text: Optional[str] = LAWS_TEXT) -> Dict[str, str]:
    files = {
        "Cargo.toml": (
            '[workspace]\nmembers = [\n    "crates/demo",\n    "crates/trust-ir-build",\n'
            '    "crates/trust-ir",\n    "crates/trust-ir-laws",\n]\n'
        ),
        "crates/trust-ir/Cargo.toml": '[package]\nname = "trust-ir"\n',
        "crates/trust-ir/src/inst.rs": IR_INST_RS,
        "crates/trust-ir/src/lib.rs": IR_LIB_RS,
        "crates/trust-ir/src/shapes.rs": LAW_ENUMS_RS,
        "crates/trust-ir-laws/Cargo.toml": '[package]\nname = "trust-ir-laws"\n',
        "crates/trust-ir-laws/src/lib.rs": LAWS_LIB_RS,
        "crates/trust-ir-build/src/validate/kinds.rs": BUILD_KINDS_RS,
    }
    if laws_text is not None:
        files[LAWS_FILE] = laws_text
    return files


class ProvedContractIsALawGate13Holds(unittest.TestCase):
    """`(proved-contract)`: witnessed only by a law gate 13 HOLDS (it exists in
    the laws file, every law is wired to its own table and named by a
    mutant's flips) whose TABLE the entry also cites."""

    def pc(self, body: str, laws_text: Optional[str] = LAWS_TEXT) -> List[str]:
        return findings(section(f"*Enforcement (proved-contract):* {body}"), extra=with_laws(laws_text))

    def refused(self, body: str, why: str, laws_text: Optional[str] = LAWS_TEXT) -> List[str]:
        found = self.pc(body, laws_text)
        self.assertTrue(any("[E3]" in f and why in f for f in found), (body, found))
        return found

    def test_a_held_law_of_the_cited_table_witnesses_the_class(self) -> None:
        self.assertEqual(self.pc(f"`AllocOrigin::is_reference_counted` holds exactly two origins: {RC_VERDICTS}."), [])
        # A glob names every law of the family, as gate 13's `flips` do.
        self.assertEqual(
            self.pc("`AllocOrigin::is_reference_counted`: true at `laws::rc_swift_heap` and `laws::rc_clean_heap`, false at every other law of `laws::rc_*`."),
            [],
        )
        # A qualified table citation ends with the table's path.
        self.assertEqual(self.pc("`trust_ir::inst::AllocOrigin::is_reference_counted`: false at `laws::rc_rust_heap`."), [])
        # Two tables in one entry: each law follows a citation of its own table.
        self.assertEqual(
            self.pc("`AllocOrigin::is_reference_counted`: false at `laws::rc_rust_heap`; `Linkage::is_interposable`: true at `laws::interposable_weak`."),
            [],
        )
        # A non-table citation between them changes nothing.
        self.assertEqual(self.pc("`AllocOrigin::is_reference_counted` (`helper`, not a table, aside): false at `laws::rc_rust_heap`."), [])

    def test_a_deref_is_prose_and_not_a_glob(self) -> None:
        # A glob leads with an identifier (`rc_*`). `*mut` is prose: read as a
        # glob it would name every law ending in `mut` (`terminator_borrow_mut`).
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            synthetic(root, GOOD_SPEC, with_laws())
            index = TOOL.build_index(root)
            self.assertEqual(TOOL.resolve(index, root, "*mut")[0], "opaque")
            self.assertEqual(TOOL.resolve(index, root, "laws::terminator_*_mut")[1], {"law"})

    def test_a_fake_law_name_is_refused(self) -> None:
        found = self.pc("`AllocOrigin::is_reference_counted`: `laws::rc_imaginary`.")
        self.assertTrue(any("[E2]" in f and "rc_imaginary" in f for f in found), found)
        found = self.pc("`AllocOrigin::is_reference_counted`: `laws::rc_imaginary_*`.")
        self.assertTrue(any("[E2]" in f and "matches no law" in f for f in found), found)
        # A real function that is not a law (the table itself) witnesses nothing.
        self.refused("`AllocOrigin::is_reference_counted` and `coverage_supports`.", "is not witnessed")
        # ... nor does a law qualified into another module.
        found = self.pc("`AllocOrigin::is_reference_counted`: `inst::rc_rust_heap`.")
        self.assertTrue(any("[E2]" in f for f in found), found)

    def test_a_law_no_mutant_refutes_is_refused(self) -> None:
        # Gate 13 refuses to run on such a file, so it holds NO law: citing
        # the new law, or any other, is refused, and the finding names why.
        mutated = LAWS_TEXT + UNFLIPPED_LAW
        self.refused("`coverage_supports`: `laws::coverage_unflipped`.", "coverage_unflipped", mutated)
        self.refused("`coverage_supports`: `laws::coverage_reflexive_unbounded`.", "gate 13 holds no law", mutated)

    def test_a_miswired_law_is_refused(self) -> None:
        wired = "{\n    AllocOrigin::RustHeap.is_reference_counted()\n}"
        self.assertEqual(LAWS_TEXT.count(wired), 1)
        mutated = LAWS_TEXT.replace(wired, "{\n    AllocOrigin::SwiftHeap.is_reference_counted()\n}")
        self.refused(f"`AllocOrigin::is_reference_counted`: {RC_LAWS}.", "rc_rust_heap", mutated)

    def test_a_law_of_another_table_is_refused(self) -> None:
        self.refused("`AllocOrigin::is_reference_counted`: `laws::interposable_weak`.", "Linkage::is_interposable")
        # ... a whole family of another table, by glob, too.
        self.refused("`Linkage::is_interposable`: `laws::rc_*`.", "AllocOrigin::is_reference_counted")
        # The method alone is not the table: `Type::method` is.
        self.refused("`is_reference_counted`: `laws::rc_rust_heap`.", "AllocOrigin::is_reference_counted")

    def test_a_law_is_read_under_the_table_cited_most_recently_before_it(self) -> None:
        # The review's M1 (a8, a11, a12): the law's table is cited in the
        # entry, but another table was cited after it, so the law would be
        # read as witnessing a claim about that other table.
        self.refused(
            "`AllocOrigin::is_reference_counted` and `Linkage::is_interposable`: `laws::rc_rust_heap`.",
            "the table citation it follows is `Linkage::is_interposable`",
        )
        self.refused(
            "`Linkage::is_interposable`: `laws::interposable_weak`, `laws::module_local_internal` (unlike `Linkage::is_module_local`).",
            "`module_local_internal` (cited as `laws::module_local_internal`) is a law of `Linkage::is_module_local`",
        )
        # ... and a law cited before any table is read under none.
        self.refused("`laws::rc_rust_heap`, a law of `AllocOrigin::is_reference_counted`.", "no table citation precedes it")
        # A glob is one finding, naming its laws.
        found = self.refused("`Linkage::is_interposable`: `laws::rc_*`.", "`rc_c_malloc`, `rc_clean_heap`, `rc_rust_heap` and 1 more")
        self.assertEqual(len([f for f in found if "[E3]" in f]), 1, found)

    def test_a_table_is_cited_by_a_spelling_that_resolves_to_it_alone(self) -> None:
        # The review's L4 (a9): the table's name also names the validator's
        # private wrapper, so only a spelling that resolves to the table's own
        # definition (in the source a law can call) cites it.
        self.assertEqual(self.pc("`trust_ir_laws::proof_ref_kind_is_ambiguous`: false at `laws::ambiguous_custom`."), [])
        self.refused("`validate::proof_ref_kind_is_ambiguous`: `laws::ambiguous_custom`.", "no table citation precedes it")
        self.refused("`proof_ref_kind_is_ambiguous`: `laws::ambiguous_custom`.", "no table citation precedes it")
        # A table with no definition in that source cannot be cited at all.
        found = self.refused("`ProofStatus::is_kernel_tier`: `laws::kernel_tier_certified`.", "has no definition in")
        self.assertTrue(any("[E2]" in f and "ProofStatus::is_kernel_tier" in f for f in found), found)

    def test_a_law_whose_family_calls_no_table_witnesses_no_claim(self) -> None:
        self.refused("`coverage_supports`: `laws::u64_ge_is_transitive`.", "calls no table")

    def test_a_tree_without_the_laws_file_holds_no_law(self) -> None:
        found = self.pc("`AllocOrigin::is_reference_counted`: `rc_rust_heap`.", laws_text=None)
        self.assertTrue(any("[E2]" in f or "[E3]" in f for f in found), found)

    def test_a_law_witnesses_the_proved_contract_class_only(self) -> None:
        for cls in ("test", "type-level", "lean-theorem", "kernel-certificate"):
            found = findings(section(f"*Enforcement ({cls}):* `AllocOrigin::is_reference_counted`: `laws::rc_rust_heap`."), extra=with_laws())
            self.assertTrue(any("[E3]" in f and "is not witnessed" in f for f in found), (cls, found))
        # A `(code)` entry may name a law: it names code, and claims nothing.
        found = findings(section("*Enforcement (code):* `laws::rc_rust_heap`."), extra=with_laws())
        self.assertEqual(besides_the_ratchet(found), [])

    def test_rewording_cannot_raise_a_code_entry_to_a_proved_contract(self) -> None:
        # The same citation relabelled: without its table cited, the law is
        # not about the claim, and the class is refused.
        self.refused("`laws::rc_rust_heap` proves it.", "AllocOrigin::is_reference_counted")

    def test_the_class_is_checked_evidence_ranked_below_the_kernel_classes_and_above_type_level(self) -> None:
        self.assertIn("proved-contract", TOOL.IN_TREE)
        order = list(TOOL.CLASSES)
        self.assertLess(order.index("lean-theorem"), order.index("proved-contract"))
        self.assertLess(order.index("kernel-certificate"), order.index("proved-contract"))
        self.assertLess(order.index("proved-contract"), order.index("type-level"))
        self.assertLess(order.index("proved-contract"), order.index("test"))
        # A section backed only by a proved contract is not a ratchet debt.
        spec = GOOD_SPEC.replace(
            "*Enforcement (prose-only):* nothing; `Config` is merely mentioned.",
            "*Enforcement (proved-contract):* `AllocOrigin::is_reference_counted`: false at `laws::rc_rust_heap`.",
        )
        found = findings(spec, extra=with_laws())
        self.assertTrue(any("[E4]" in f and "measured 0, ledger still says 1" in f for f in found), found)


class E5AnEntrySaysWhatItsStatementSays(unittest.TestCase):
    """Rule E5: a `(proved-contract)` / `(lean-theorem)` entry gives each law
    the verdict its `ensures` states and each theorem the verdict its
    conclusion states (when the reader classifies it), naming identifiers of
    its statement.  Every test is a pair: a CONTROL green before and after the
    rule, and a MUTATION whose assertion names the rule (`[E5]`, `F1`..`F3`,
    or the names-only wording), which the gate before E5 did not raise.  One
    synthetic tree (the real laws file, the Demo Lean) is indexed once."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.tmp = tempfile.TemporaryDirectory()
        cls.root = Path(cls.tmp.name)
        synthetic(cls.root, GOOD_SPEC, with_laws())
        cls.index = TOOL.build_index(cls.root)

    @classmethod
    def tearDownClass(cls) -> None:
        cls.tmp.cleanup()

    def run_entry(self, cls_: str, body: str, index=None) -> List[str]:
        report = TOOL.run(self.root, base_ref=None, governed=ONLY_SPEC, index=index or self.index, overrides={SPEC_DOC: section(f"*Enforcement ({cls_}):* {body}")})
        return [str(f) for f in report.findings]

    def pc(self, body: str) -> List[str]:
        return self.run_entry("proved-contract", body)

    def lt(self, body: str) -> List[str]:
        return self.run_entry("lean-theorem", body)

    def says(self, found: List[str], *needles: str) -> None:
        self.assertTrue(any("[E5]" in f and all(n in f for n in needles) for f in found), (needles, found))

    def counts(self, cls_: str, body: str) -> Dict[str, int]:
        report = TOOL.run(self.root, base_ref=None, governed=ONLY_SPEC, index=self.index, overrides={SPEC_DOC: section(f"*Enforcement ({cls_}):* {body}")})
        self.assertEqual(report.findings, [])
        return report.says

    # --- laws ----------------------------------------------------------

    def test_1_a_law_is_given_the_verdict_its_ensures_states(self) -> None:
        self.assertEqual(self.pc(f"`AllocOrigin::is_reference_counted`: {RC_VERDICTS}."), [])
        found = self.pc("`AllocOrigin::is_reference_counted`: true at `laws::rc_rust_heap`.")
        self.says(found, "rc_rust_heap", "ensures result == false")

    def test_2_a_law_no_phrase_governs_is_refused(self) -> None:
        found = self.pc(f"`AllocOrigin::is_reference_counted` holds exactly two origins: {RC_LAWS}.")
        self.assertEqual(len([f for f in found if "[E5]" in f and "no verdict phrase governs it" in f]), 4, found)

    def test_3_a_closing_phrase_governs_the_citations_before_it(self) -> None:
        control = "`AllocOrigin::is_reference_counted`: a cell of `laws::rc_swift_heap` is counted (true), and one of `laws::rc_rust_heap` is not (false)."
        self.assertEqual(self.pc(control), [])
        swapped = control.replace("(true)", "(TRUE)").replace("(false)", "(true)").replace("(TRUE)", "(false)")
        self.says(self.pc(swapped), "rc_swift_heap")
        self.says(self.pc(swapped), "rc_rust_heap")

    def test_4_a_relation_is_the_ensures_relation(self) -> None:
        self.assertEqual(self.pc("`coverage_supports`: true exactly when have >= need at `laws::coverage_unwind_is_magnitude_order`."), [])
        for wrong in ("have > need", "need >= have"):
            self.says(self.pc(f"`coverage_supports`: true exactly when {wrong} at `laws::coverage_unwind_is_magnitude_order`."), "ensures result == (have >= need)")
        # ... and a relation law is not merely `true`.
        self.says(self.pc("`coverage_supports`: true at `laws::coverage_unwind_is_magnitude_order`."), "coverage_unwind_is_magnitude_order")

    def test_5_the_other_laws_of_a_glob_are_counted(self) -> None:
        true_three = "`laws::backed_by_precondition`, `laws::backed_by_postcondition` and `laws::backed_by_termination`"
        control = f"`ExternRefSite::admits_shape`: true at {true_three}, false at the thirteen other laws of `laws::backed_by_*`."
        self.assertEqual(self.pc(control), [])
        self.says(self.pc(control.replace("thirteen", "twelve")), "the twelve other laws of", "are 13")
        self.assertEqual(self.pc(control.replace("thirteen", "13")), [])
        # A true law dropped from the list falls into the false glob.
        dropped = control.replace(" and `laws::backed_by_termination`", "")
        self.says(self.pc(dropped), "backed_by_termination", "ensures result")

    def test_6_exactly_at_names_every_law_of_its_family_with_that_verdict(self) -> None:
        control = (
            "`Linkage::is_interposable`, one law per linkage: it is true exactly at `laws::interposable_weak`, "
            "`laws::interposable_link_once` and `laws::interposable_external_weak`, and false at every other law of `laws::interposable_*`."
        )
        self.assertEqual(self.pc(control), [])
        self.says(self.pc(control.replace(" and `laws::interposable_external_weak`", "")), "exactly at", "interposable_external_weak")

    def test_7_one_law_per_needs_a_cell_table(self) -> None:
        self.assertEqual(self.pc("`coverage_supports`: true at `laws::coverage_reflexive_unbounded`."), [])
        self.says(self.pc("`coverage_supports`, one law per bound: true at `laws::coverage_reflexive_unbounded`."), "one law per bound")

    def test_8_a_variant_named_beside_laws_is_a_cell_of_them(self) -> None:
        control = "`license_admits_body` is false at `Ungated` (`laws::license_ungated_refused_under_any_policy`)."
        self.assertEqual(self.pc(control), [])
        self.says(self.pc(control.replace("`Ungated`", "`Absent`")), "`Absent`", "no cell")

    # --- theorems ------------------------------------------------------

    def test_9_a_theorem_is_given_the_verdict_its_conclusion_states(self) -> None:
        control = "`op` is UB at an argument other than `zero` (`Demo.demo_is_ub`); `op` of `zero` runs (`Demo.demo_runs`)."
        self.assertEqual(self.lt(control), [])
        self.says(self.lt(control.replace("is UB at", "runs at")), "Demo.demo_is_ub", "says `ub`")

    def test_10_a_bare_theorem_list_is_refused(self) -> None:
        self.says(self.lt("`Demo.demo_is_ub`, in `TrustIr/Demo.lean`."), "Demo.demo_is_ub", "no verdict phrase governs it")

    def test_11_a_theorem_citation_names_an_identifier(self) -> None:
        self.says(self.lt("is UB (`Demo.demo_is_ub`)."), "names no identifier")

    def test_12_a_named_identifier_occurs_in_the_statement_outside_strings(self) -> None:
        self.says(self.lt("`demo_def` is UB at an argument other than `zero` (`Demo.demo_is_ub`)."), "`demo_def`", "does not occur")
        # `zero` occurs in `demo_quoted` only inside its string literal.
        self.assertEqual(self.lt("`op` at 1 is UB (`Demo.demo_quoted`)."), [])
        self.says(self.lt("`op` at `zero` is UB (`Demo.demo_quoted`)."), "`zero`", "does not occur")

    def test_13_a_named_identifier_is_negated_where_the_statement_negates_it(self) -> None:
        self.says(self.lt("`op` is UB at `zero` (`Demo.demo_is_ub`)."), "`zero`", "only after a `≠` or `¬`")
        self.says(self.lt("`op` of an argument other than `zero` runs (`Demo.demo_runs`)."), "`zero`", "negated in the entry")

    def test_14_the_reader_decides_the_tier(self) -> None:
        # Outside the reader: no verdict phrase may govern it, it is held to
        # names only, and it is counted apart.
        self.says(self.lt("`op` is UB (`Demo.demo_odd`)."), "reads no verdict")
        self.says(self.lt("equal to itself (`Demo.demo_odd`)."), "names no identifier")
        said = self.counts("lean-theorem", "`op` equals itself plus nothing (`Demo.demo_odd`).")
        self.assertEqual((said["names_only"], said["theorems"]), (1, 0))
        said = self.counts("lean-theorem", "`op` of `zero` runs (`Demo.demo_runs`).")
        self.assertEqual((said["names_only"], said["theorems"], said["identifiers"]), (0, 1, 2))
        # The reader's shapes.
        read = TOOL.lean_conclusion_verdict
        self.assertIsNone(read("¬ run s = .ok 0 ↔ p"))
        self.assertIsNone(read("run s = .ok 0 ∧ q = true"))
        self.assertEqual(read("∃ post, Sem.run (semFence ord) s = .ok ((), post)"), "runs")
        self.assertEqual(read("Sem.run (semFence ord) s = .ok ((), s)"), "noop")
        self.assertEqual(read('stepOutcome x = "error:ub"'), "ub")
        self.assertEqual(read("canDealloc arcRef = false"), "false")
        # A `match` left-hand side has one rule, and `true` there reads runs.
        match = "(match Sem.run (do semDealloc p) s with | .ok _ => true | .error _ => false) = true"
        self.assertEqual(read(match), "runs")
        self.assertIsNone(read(match.replace(".error _ => false", ".error _ => true")))
        self.assertEqual(read("(match Sem.run x s with | .ok (v, _) => some v | .error _ => none) = some (.int 32 7)"), "runs")

    def test_14b_a_statement_the_reader_cannot_delimit_is_refused(self) -> None:
        self.assertEqual(self.lt("`op` of `zero` runs (`Demo.demo_runs`)."), [])
        self.says(self.lt("`op` of anything is itself (`Demo.demo_undelimited`)."), "cannot delimit its statement")

    def test_15_e_g_does_not_end_a_clause(self) -> None:
        control = "`AllocOrigin::is_reference_counted` is true at a reference-counted origin, e.g. `laws::rc_swift_heap`."
        self.assertEqual(self.pc(control), [])
        self.says(self.pc(control.replace("rc_swift_heap", "rc_rust_heap")), "rc_rust_heap")

    def test_16_f1_a_negated_verdict_phrase_is_refused(self) -> None:
        self.says(self.pc("`AllocOrigin::is_reference_counted` is not true at `laws::rc_swift_heap`."), "F1")
        self.says(self.lt("`op` of `zero` never runs (`Demo.demo_runs`)."), "F1")
        # A spelling rule, not a judgement of truth: this English is true.
        self.says(self.pc("`AllocOrigin::is_reference_counted` is not true at `laws::rc_rust_heap`."), "F1")
        self.assertEqual(self.pc("`AllocOrigin::is_reference_counted` is false at `laws::rc_rust_heap`."), [])

    def test_17_f2_a_closer_that_governs_nothing_is_refused(self) -> None:
        self.assertEqual(self.pc("`AllocOrigin::is_reference_counted` is true at `laws::rc_swift_heap`."), [])
        self.says(self.pc("`AllocOrigin::is_reference_counted` is true at `laws::rc_swift_heap` (false)."), "F2")

    def test_18_f3_a_negated_citation_is_refused(self) -> None:
        self.assertEqual(self.pc("`AllocOrigin::is_reference_counted` is true at `laws::rc_swift_heap` and `laws::rc_clean_heap`."), [])
        self.says(self.pc("`AllocOrigin::is_reference_counted` is true at `laws::rc_swift_heap` but not `laws::rc_clean_heap`."), "F3", "rc_clean_heap")
        self.says(self.lt("`op` of `zero` runs, except `Demo.demo_runs`."), "F3")

    def test_19_undefined_behaviour_is_a_ub_phrase(self) -> None:
        self.assertEqual(self.lt("`op` is undefined behaviour at an argument other than `zero` (`Demo.demo_is_ub`)."), [])
        self.says(self.lt("`op` of `zero` is undefined behaviour (`Demo.demo_runs`)."), "says `runs`")

    def test_20_the_lean_half_runs_while_gate_13_holds_nothing(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            synthetic(root, GOOD_SPEC, with_laws(LAWS_TEXT + UNFLIPPED_LAW))
            refusing = TOOL.build_index(root)
            self.assertEqual(refusing.gate13.held, ())
            spec = section(
                "*Enforcement (proved-contract):* `AllocOrigin::is_reference_counted`: true at `laws::rc_rust_heap`.\n\n"
                "*Enforcement (lean-theorem):* `op` runs at an argument other than `zero` (`Demo.demo_is_ub`)."
            )
            found = [str(f) for f in TOOL.run(root, base_ref=None, governed=ONLY_SPEC, index=refusing, overrides={SPEC_DOC: spec}).findings]
        self.says(found, "Demo.demo_is_ub")
        self.assertFalse(any("[E5]" in f and "rc_rust_heap" in f for f in found), found)
        self.assertTrue(any("[E3]" in f and "gate 13 holds no law" in f for f in found), found)

    def test_the_vocabulary_is_one_table_and_every_message_renders_it(self) -> None:
        found = [f for f in self.pc("`AllocOrigin::is_reference_counted`: true at `laws::rc_rust_heap`.") if "[E5]" in f]
        self.assertTrue(found)
        self.assertTrue(all(TOOL.vocabulary() in f for f in found), found)
        for spellings, kind, verdict in TOOL.VERDICTS:
            self.assertIn(kind, ("leading", "closing"))
            for spelling in spellings:
                self.assertIn(f"`{spelling}`", TOOL.vocabulary())


class E4TheRatchetOnlyGoesDown(unittest.TestCase):
    def ledger(self, units: int, extra_rows: str = "") -> str:
        return LEDGER.replace("2026-01-01 1 initial census\nvalidation-error-variants-unnamed", f"2026-01-01 {units} initial census\n{extra_rows}validation-error-variants-unnamed")

    def test_a_new_unbacked_section_is_a_regression(self) -> None:
        found = findings(section("*Enforcement (prose-only):* nothing."))
        self.assertEqual(len(found), 1, found)
        self.assertIn("measured 2, ledger says 1", found[0])
        self.assertIn("§3", found[0])

    def test_code_and_external_do_not_count_as_checked_evidence(self) -> None:
        for entry in ("*Enforcement (code):* `helper`.", "*Enforcement (external):* `../x/y.rs`."):
            found = findings(section(entry))
            self.assertTrue(any("measured 2, ledger says 1" in f for f in found), (entry, found))

    def test_a_gain_must_be_written_down(self) -> None:
        found = findings(ledger_text=self.ledger(3))
        self.assertEqual(len(found), 1, found)
        self.assertIn("measured 1, ledger still says 3", found[0])
        self.assertIn("append", found[0])

    def test_a_row_that_raises_the_count_is_refused_even_when_it_matches(self) -> None:
        # The measured count IS 2 here, and the last row says 2: only the
        # non-increasing rule stands between a new unbacked claim and green.
        spec = section("*Enforcement (prose-only):* nothing.")
        rows = "units-without-checked-evidence               2026-02-01 2 we added an unbacked claim\n"
        found = findings(spec, ledger_text=self.ledger(1, rows) + SECTION_3)
        self.assertEqual(len(found), 1, found)
        self.assertIn("rose from 1 to 2", found[0])

    def test_the_member_lines_are_exactly_what_is_measured(self) -> None:
        # Backed, but still listed as a debt.
        stale = findings(ledger_text=LEDGER + SECTION_3)
        self.assertEqual(len(stale), 1, stale)
        self.assertIn("is backed now: delete this line", stale[0])
        # A debt, but not listed.
        unlisted = findings(ledger_text=LEDGER.replace("member validation-error-variants-unnamed Untested\n", ""))
        self.assertEqual(len(unlisted), 1, unlisted)
        self.assertIn("`Untested` has no checked evidence but is not a listed member", unlisted[0])

    def test_retiring_one_debt_does_not_buy_another(self) -> None:
        # Same COUNT before and after; only the member set betrays the swap.
        swapped = LEDGER.replace("SPEC_RATIFICATIONS.md §2", "SPEC_RATIFICATIONS.md §3")
        self.assertEqual(TOOL.count_rows(swapped), TOOL.count_rows(LEDGER))
        found = [str(f) for f in TOOL.check_ledger_prefix(LEDGER, swapped, "base")]
        self.assertEqual(len(found), 1, found)
        self.assertIn("is a NEW member", found[0])
        shrunk = LEDGER.replace("member validation-error-variants-unnamed Untested\n", "") + "validation-error-variants-unnamed 2026-02-01 1 a test names it\n"
        self.assertEqual(TOOL.check_ledger_prefix(LEDGER, shrunk, "base"), [])

    def test_a_row_edited_in_place_fails_the_prefix_check(self) -> None:
        self.assertEqual(TOOL.check_ledger_prefix(LEDGER, LEDGER + "units-without-checked-evidence 2026-03-01 0 backed\n", "base"), [])
        edited = LEDGER.replace("2026-01-01 1 initial", "2026-01-01 2 initial")
        self.assertEqual(len(TOOL.check_ledger_prefix(LEDGER, edited, "base")), 1)
        dropped = LEDGER.replace("validation-error-variants-never-constructed  2026-01-01 1 initial census\n", "")
        self.assertEqual(len(TOOL.count_rows(dropped)) + 1, len(TOOL.count_rows(LEDGER)))
        self.assertEqual(len(TOOL.check_ledger_prefix(LEDGER, dropped, "base")), 1)

    def test_the_landed_ledger_is_read_at_the_merge_base_not_at_the_remote_tip(self) -> None:
        def git(root: Path, *args: str) -> None:
            subprocess.run(["git", "-C", os.fspath(root), "-c", "user.name=t", "-c", "user.email=t@t", *args], check=True, capture_output=True)

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            synthetic(root)
            git(root, "init", "-q")
            git(root, "add", "-A")
            git(root, "commit", "-q", "-m", "land the ledger")
            git(root, "update-ref", "refs/remotes/origin/main", "HEAD")
            landed = (root / TOOL.RATCHET).read_text(encoding="utf-8")

            def found() -> List[str]:
                return [str(f) for f in TOOL.run(root, base_ref="origin/main", governed=ONLY_SPEC).findings]

            self.assertEqual(found(), [])
            # The remote gains a row this clone has not merged: BEHIND is not EDITED.
            ahead = landed.replace("member validation-error-variants-unnamed Untested\n", "")
            (root / TOOL.RATCHET).write_text(ahead + "validation-error-variants-unnamed 2026-02-01 1 a test now names it\n", encoding="utf-8")
            git(root, "commit", "-q", "-am", "origin moves ahead")
            git(root, "update-ref", "refs/remotes/origin/main", "HEAD")
            git(root, "reset", "-q", "--hard", "HEAD~1")
            self.assertEqual(found(), [])
            # A landed row rewritten upward, with an unbacked claim added to match it.
            (root / SPEC_DOC).write_text(section("*Enforcement (prose-only):* nothing."), encoding="utf-8")
            (root / TOOL.RATCHET).write_text(landed.replace("2026-01-01 1 initial", "2026-01-01 2 initial", 1) + SECTION_3, encoding="utf-8")
            rewritten = found()
            self.assertEqual(len(rewritten), 2, rewritten)
            self.assertTrue(any("append-only" in f for f in rewritten), rewritten)
            self.assertTrue(any("is a NEW member" in f and "§3" in f for f in rewritten), rewritten)

    # --- An honest DOWNGRADE is recorded, not refused.  Before this the ratchet
    # --- could not tell "I read the cited test and it does not test the claim"
    # --- from a regression, and so rewarded leaving the overclaim standing.

    DOWNGRADED = GOOD_SPEC.replace("*Enforcement (test):* `config_validates` and the file\n`crates/demo/tests/rules.rs`.", "*Enforcement (prose-only):* the cited test was read: it does not test this rule.")
    SECTION_1 = "member units-without-checked-evidence docs/SPEC_RATIFICATIONS.md §1\n"
    CORRECTION_1 = "correction units-without-checked-evidence 2026-02-01 docs/SPEC_RATIFICATIONS.md §1 :: read on review: the cited test does not test the rule\n"
    THEN = {"docs/SPEC_RATIFICATIONS.md §1": True, "docs/SPEC_RATIFICATIONS.md §2": False}

    def test_an_honest_downgrade_is_refused_bare_and_accepted_as_a_correction(self) -> None:
        self.assertNotEqual(self.DOWNGRADED, GOOD_SPEC)
        bare = findings(self.DOWNGRADED)
        self.assertEqual(len(bare), 1, bare)
        self.assertIn("measured 2, ledger says 1", bare[0])
        self.assertIn("honest downgrade", bare[0])  # the message names the way through
        corrected = LEDGER + self.CORRECTION_1 + self.SECTION_1
        self.assertEqual(findings(self.DOWNGRADED, ledger_text=corrected, base=(LEDGER, self.THEN)), [])
        # The member line alone (the count left behind) is not enough ...
        self.assertTrue(findings(self.DOWNGRADED, ledger_text=LEDGER + self.SECTION_1, base=(LEDGER, self.THEN)))
        # ... and a plain COUNT row still cannot rise.
        raised = LEDGER + "units-without-checked-evidence 2026-02-01 2 we downgraded one\n" + self.SECTION_1
        self.assertTrue(any("rose from 1 to 2" in f for f in findings(self.DOWNGRADED, ledger_text=raised)))

    def test_a_correction_cannot_launder_a_new_unbacked_claim(self) -> None:
        # §3 is NEW: it did not exist at the base, so it is a regression.
        spec = section("*Enforcement (prose-only):* nothing.")
        ledger = LEDGER + self.CORRECTION_1.replace("§1", "§3") + SECTION_3
        found = findings(spec, ledger_text=ledger, base=(LEDGER, self.THEN))
        self.assertEqual(len(found), 1, found)
        self.assertIn("did not exist at", found[0])
        # §2 was ALREADY a debt at the base: there is nothing to correct.
        found = [str(f) for f in TOOL.check_ledger_prefix(LEDGER, LEDGER + self.CORRECTION_1.replace("§1", "§2"), "base", self.THEN)]
        self.assertTrue(any("already had no checked evidence" in f for f in found), found)

    def test_a_correction_is_one_unit_one_row_with_a_reason_and_only_for_units(self) -> None:
        for bad, needle in (
            (self.CORRECTION_1.replace(" :: read on review: the cited test does not test the rule", " ::"), "the reason is required"),
            (self.CORRECTION_1.replace(" :: ", " because "), "the reason is required"),
            (self.CORRECTION_1 + self.CORRECTION_1, "is corrected twice"),
            (self.CORRECTION_1.replace("units-without-checked-evidence", "validation-error-variants-unnamed"), "measured, not judged"),
            (self.CORRECTION_1.replace("2026-02-01", "2025-01-01"), "dated before"),
        ):
            parsed = [str(f) for f in TOOL.parse_ledger(LEDGER + bad).findings]
            self.assertTrue(any(needle in f for f in parsed), (bad, parsed))
        # It counts: the last row of the ledger is now 2, and history keeps it.
        parsed = TOOL.parse_ledger(LEDGER + self.CORRECTION_1)
        self.assertEqual(parsed.rows[TOOL.SECTION_LEDGER][-1][2], 2)
        self.assertIn(" ".join(self.CORRECTION_1.split()), TOOL.count_rows(LEDGER + self.CORRECTION_1))
        removed = TOOL.check_ledger_prefix(LEDGER + self.CORRECTION_1, LEDGER, "base")
        self.assertTrue(any("append-only" in str(f) for f in removed), removed)

    def test_a_comment_cannot_retire_a_debt(self) -> None:
        # The reviewer's route: mark the debt `not-normative`, delete its
        # entries, and write the "gain" down exactly as the gate instructs.
        opted = GOOD_SPEC.replace("Rule two.\n\n*Enforcement (prose-only):* nothing; `Config` is merely mentioned.", "<!-- enforcement-links: not-normative it is a statement of intent -->\n\nRule two.")
        self.assertNotEqual(opted, GOOD_SPEC)
        paid = LEDGER.replace("member units-without-checked-evidence docs/SPEC_RATIFICATIONS.md §2\n", "") + "units-without-checked-evidence 2026-02-01 0 section 2 is not normative\n"
        found = findings(opted, ledger_text=paid, base=(LEDGER, self.THEN))
        self.assertEqual(len(found), 1, found)
        self.assertIn("A marker does not retire a claim", found[0])
        self.assertIn("§2", found[0])
        # A section that never was a normative unit may still opt out.
        appendix = GOOD_SPEC + "\n## Changelog\n\n<!-- enforcement-links: not-normative a dated list, states no rule -->\n\nText.\n"
        self.assertEqual(findings(appendix, base=(LEDGER, self.THEN)), [])

    def test_the_check_output_names_every_opt_out_and_correction(self) -> None:
        appendix = GOOD_SPEC + "\n## Changelog\n\n<!-- enforcement-links: not-normative a dated list, states no rule -->\n\nText.\n"
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            synthetic(root, appendix, {"scripts/gates/enforcement-ratchet.txt": LEDGER, "TRUST.md": "# T\n\n## Trusted base\n\n1. **One.** x\n\n| Item | Enforcement |\n|---|---|\n| 1 | (test) `config_validates` |\n", "CLAUDE.md": "# C\n\n## Serialization\n\nnone\n"})
            result = subprocess.run([sys.executable, "-B", os.fspath(TOOL_PATH), "--root", os.fspath(root), "--base-ref", "", "check"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("note: opted out as not-normative", result.stdout)
        self.assertIn("Changelog", result.stdout)
        self.assertIn("1 opted out as not-normative, 0 correction(s) on record", result.stdout)

    def test_a_malformed_backdated_or_unknown_row_is_refused(self) -> None:
        for bad, needle in (
            ("units-without-checked-evidence 2026-01-01 one why\n", "expected `<ledger>"),
            ("units-without-checked-evidence 2025-01-01 1 earlier\n", "dated before"),
            ("some-other-ledger 2026-01-01 1 why\n", "unknown ledger"),
            ("member some-other-ledger Thing\n", "expected `member <ledger> <name>`"),
            ("member validation-error-variants-unnamed Dead\n", "is listed twice"),
            ("units-without-checked-evidence 2026-13-40 1 why\n", "not an ISO date"),
        ):
            found = findings(ledger_text=LEDGER + bad)
            self.assertTrue(any(needle in f for f in found), (bad, found))

    def test_a_missing_ledger_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            synthetic(root)
            (root / TOOL.RATCHET).unlink()
            report = TOOL.run(root, base_ref=None, governed=ONLY_SPEC)
            self.assertTrue(any("ledger is missing" in str(f) for f in report.findings))


class PRepoRootedPathsInProse(unittest.TestCase):
    def test_a_dead_path_in_prose_is_refused_and_a_declared_one_is_not(self) -> None:
        dead = GOOD_SPEC + "\nSee `crates/elsewhere/src/shim.rs`.\n"
        self.assertTrue(any("[P]" in f and "shim.rs" in f for f in findings(dead)))
        declared = dead + "\n<!-- enforcement-links: external crates/elsewhere/src/shim.rs (another repo) -->\n"
        self.assertEqual(findings(declared), [])

    def test_a_stale_external_declaration_is_refused(self) -> None:
        stale = GOOD_SPEC + "\n<!-- enforcement-links: external crates/demo/src/lib.rs -->\n"
        self.assertTrue(any("declared external but exists" in f for f in findings(stale)))

    def test_a_glob_must_match_and_a_template_is_not_a_path(self) -> None:
        self.assertEqual(findings(GOOD_SPEC + "\nSee `crates/demo/tests/*.rs` and `scripts/gates/<gate>.tests`.\n"), [])
        self.assertTrue(any("matches no file" in f for f in findings(GOOD_SPEC + "\nSee `crates/demo/benches/*.rs`.\n")))


class TestModulesAreFoundTheWayRustcLoadsThem(unittest.TestCase):
    """`cfg_test_module_files`: a `#[cfg(test)]` module is a test context in
    full wherever rustc loads it from, `#[path]` included."""

    ENGINE = """
    pub fn run() {}
    #[cfg(test)]
    #[path = "engine_checks.rs"]
    mod checks;
    #[path = "engine_shared.rs"]
    #[cfg(test)]
    mod shared_tests;
    #[path = r"engine_raw.rs"]
    #[cfg(test)]
    pub(crate) mod raw;
    mod outer {
        #[cfg(test)]
        #[path = "inner_tests.rs"]
        mod inner;
    }
    #[path = "pinned"]
    mod pinned {
        #[cfg(test)]
        #[path = "pinned_tests.rs"]
        mod tests;
    }
    #[cfg(test)]
    mod suite {
        #[path = "../suite_tests.rs"]
        mod cases;
    }
    // #[cfg(test)] #[path = "commented.rs"] mod commented;
    const TEXT: &str = "#[cfg(test)] #[path = \"quoted.rs\"] mod quoted;";
    """

    def files(self, extra: Optional[Dict[str, str]] = None) -> set:
        sources = {
            "crates/demo/src/lib.rs": "pub mod engine;\n#[cfg(test)]\n#[path = \"lib_tests.rs\"]\nmod tests;\n",
            "crates/demo/src/engine.rs": textwrap.dedent(self.ENGINE),
            "crates/demo/src/engine_checks.rs": "mod helpers;\nfn checks() {}\n",
            "crates/demo/src/helpers.rs": "fn help() {}\n",
            "crates/demo/src/engine/checks.rs": "fn decoy() {}\n",
            "crates/demo/src/engine_shared.rs": "fn shared() {}\n",
            "crates/demo/src/engine_raw.rs": "fn raw() {}\n",
            "crates/demo/src/engine/outer/inner_tests.rs": "fn inner() {}\n",
            "crates/demo/src/outer/inner_tests.rs": "fn wrong_directory() {}\n",
            "crates/demo/src/pinned/pinned_tests.rs": "fn pinned() {}\n",
            "crates/demo/src/engine/suite_tests.rs": "fn suite() {}\n",
            "crates/demo/src/suite_tests.rs": "fn not_the_suite() {}\n",
            "crates/demo/src/lib_tests.rs": "fn lib_tests() {}\n",
            "crates/demo/src/commented.rs": "fn commented() {}\n",
            "crates/demo/src/quoted.rs": "fn quoted() {}\n",
        }
        sources.update(extra or {})
        return TOOL.cfg_test_module_files(sources)

    def test_a_path_attribute_is_resolved_relative_to_the_declaring_file(self) -> None:
        found = self.files()
        for test_file in (
            "crates/demo/src/engine_checks.rs",  # beside engine.rs, not in engine/
            "crates/demo/src/engine_shared.rs",  # `#[path]` before `#[cfg(test)]`
            "crates/demo/src/engine_raw.rs",  # a raw-string path
            "crates/demo/src/lib_tests.rs",
        ):
            self.assertIn(test_file, found)
        # `mod checks;` without its `#[path]` would load engine/checks.rs: the
        # attribute replaces that default, so the decoy is live code.
        self.assertNotIn("crates/demo/src/engine/checks.rs", found)
        for ghost in ("crates/demo/src/commented.rs", "crates/demo/src/quoted.rs"):
            self.assertNotIn(ghost, found)

    def test_inside_inline_modules_the_path_follows_rustc(self) -> None:
        found = self.files()
        # engine.rs is not a `mod.rs`: an inline `mod outer` is engine/outer/.
        self.assertIn("crates/demo/src/engine/outer/inner_tests.rs", found)
        self.assertNotIn("crates/demo/src/outer/inner_tests.rs", found)
        # An inline module's own `#[path]` names a directory beside the file.
        self.assertIn("crates/demo/src/pinned/pinned_tests.rs", found)
        # A declaration inside a `#[cfg(test)]` inline module is test-only;
        # its `..` climbs out of engine/suite/, not out of src/.
        self.assertIn("crates/demo/src/engine/suite_tests.rs", found)
        self.assertNotIn("crates/demo/src/suite_tests.rs", found)

    def test_a_test_files_own_modules_are_test_files(self) -> None:
        # engine_checks.rs is loaded by `#[path]`, so it owns its directory:
        # its plain `mod helpers;` is helpers.rs beside it.
        self.assertIn("crates/demo/src/helpers.rs", self.files())

    def test_a_file_a_live_declaration_also_loads_is_live_code(self) -> None:
        found = self.files({"crates/demo/src/main.rs": '#[path = "engine_checks.rs"]\nmod shared;\nfn main() {}\n'})
        self.assertNotIn("crates/demo/src/engine_checks.rs", found)
        self.assertNotIn("crates/demo/src/helpers.rs", found)

    def test_a_path_loaded_test_module_counts_in_the_gate(self) -> None:
        validate = VALIDATE_RS + '#[cfg(test)]\n#[path = "validate_path_tests.rs"]\nmod path_tests;\n'
        extra = {
            "crates/trust-ir-build/src/validate.rs": validate,
            "crates/trust-ir-build/src/validate_path_tests.rs": (
                "use super::*;\n#[test]\nfn builds() { let _ = ValidationError::Dead(1); let _ = ValidationError::Untested; }\n"
            ),
        }
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            synthetic(root, extra=extra)
            report = TOOL.run(root, base_ref=None, governed=ONLY_SPEC)
            # Both are named by a test now, and `Dead` is still built by no
            # live code: before `#[path]` was honoured the file read as live
            # code, which hid `Dead` from the never-constructed census.
            self.assertEqual(report.unnamed_variants, [])
            self.assertEqual(report.dead_variants, ["Dead"])
        # The file witnesses `(test)`.  (Naming two more variants is a ratchet
        # gain the synthetic ledger has not written down: E4, not E3.)
        cited = section("*Enforcement (test):* `crates/trust-ir-build/src/validate_path_tests.rs`.")
        self.assertEqual(besides_the_ratchet(findings(cited, extra=extra)), [])
        self.assertTrue(any("[E3]" in f for f in findings(cited.replace("validate_path_tests", "validate"), extra=extra)))

    def test_a_crate_root_a_test_only_declaration_loads_stays_live(self) -> None:
        # Cargo compiles every target root live, whatever else loads it; a
        # test-only `#[path]` load must not make one a test context.
        sources = {
            "crates/a/src/lib.rs": "pub fn live_impl() {}\n",
            "crates/a/tests/t.rs": '#[path = "../src/lib.rs"]\nmod lib_under_test;\n',
            "crates/c/src/lib.rs": (
                '#[cfg(test)]\n#[path = "bin/tool.rs"]\nmod tool_tests;\n'
                '#[cfg(test)]\n#[path = "helper.rs"]\nmod helper_tests;\n'
            ),
            "crates/c/src/bin/tool.rs": "fn main() {}\n",
            "crates/c/src/helper.rs": "fn helper() {}\n",
            "crates/c/build.rs": "fn main() {}\n",
            "crates/c/examples/demo/main.rs": "fn main() {}\n",
            "crates/c/tests/build_too.rs": '#[path = "../build.rs"]\nmod b;\n#[path = "../examples/demo/main.rs"]\nmod e;\n',
        }
        found = TOOL.cfg_test_module_files(sources)
        for root in (
            "crates/a/src/lib.rs",
            "crates/c/src/bin/tool.rs",
            "crates/c/build.rs",
            "crates/c/examples/demo/main.rs",
        ):
            self.assertNotIn(root, found)
        # The control: a file only a test-only declaration loads is a test.
        self.assertIn("crates/c/src/helper.rs", found)

    def test_manifest_target_paths_are_roots(self) -> None:
        paths = ["crates/m/core.rs", "crates/m/tools/x.rs", "crates/m/gen/build.rs", "crates/m/src/other.rs"]
        manifest = (
            '[package]\nname = "m"\nbuild = "gen/build.rs"\n\n[lib]\npath = "core.rs"\n\n'
            '[[bin]]\nname = "x"\npath = "tools/x.rs"\n\n[[test]]\nname = "t"\npath = "src/other.rs"\n'
        )
        roots = TOOL.cargo_target_roots(paths, {"crates/m/Cargo.toml": manifest})
        self.assertEqual(roots, {"crates/m/core.rs", "crates/m/tools/x.rs", "crates/m/gen/build.rs"})

    def test_a_crate_root_counts_as_live_code_in_the_gate(self) -> None:
        extra = {
            "crates/trust-ir-build/Cargo.toml": '[package]\nname = "trust-ir-build"\n\n[lib]\npath = "src/validate.rs"\n',
            "crates/trust-ir-build/tests/through_path.rs": '#[path = "../src/validate.rs"]\nmod under_test;\n',
        }
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            synthetic(root, extra=extra)
            report = TOOL.run(root, base_ref=None, governed=ONLY_SPEC)
            # As with no such load (VEveryRefusalRuleIsCounted): validate.rs's
            # body is live code, so nothing is hidden and nothing invented.
            self.assertEqual(report.unnamed_variants, ["Dead", "Untested"])
            self.assertEqual(report.dead_variants, ["Dead"])
        cited = section("*Enforcement (test):* `crates/trust-ir-build/src/validate.rs`.")
        self.assertTrue(any("[E3]" in f for f in findings(cited, extra=extra)))

    def test_the_scan_reads_each_character_once(self) -> None:
        # Long attribute runs in front of items, and in front of nothing: the
        # backward read is bounded by the source, and every declaration keeps
        # its attributes.
        item = "#[allow(dead_code)]\n" * 400 + "#[cfg(test)]\n#[path = \"t.rs\"]\npub(crate) mod m;\n"
        source = ("#[inline]\n" * 2000 + "fn f() {}\n" + item) * 20
        work = TOOL.ScanWork()
        decls = TOOL.module_decls(source, work)
        self.assertEqual([(d.name, d.path, d.test) for d in decls], [("m", "t.rs", True)] * 20)
        self.assertLessEqual(work.read, len(source))
        # Deep inline nesting with a declaration at every level: each inline
        # module is resolved to a directory once, not once per declaration
        # inside it.
        depth = 3000
        nested = "".join(f"mod a{i} {{\nmod x{i};\n" for i in range(depth)) + "}\n" * depth
        target = "crates/p/src/" + "/".join(f"a{i}" for i in range(depth)) + f"/x{depth - 1}.rs"
        work = TOOL.ScanWork()
        found = TOOL.cfg_test_module_files({"crates/p/src/lib.rs": nested, target: "fn deep() {}\n"}, work=work)
        self.assertEqual(work.scopes, depth)
        self.assertEqual(found, set())  # loaded by a live declaration
        test_nested = nested.replace("mod a0 {", "#[cfg(test)]\nmod a0 {", 1)
        found = TOOL.cfg_test_module_files({"crates/p/src/lib.rs": test_nested, target: "fn deep() {}\n"})
        self.assertEqual(found, {target})


class VEveryRefusalRuleIsCounted(unittest.TestCase):
    def test_unnamed_and_dead_variants_are_told_apart(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            synthetic(root)
            report = TOOL.run(root, base_ref=None, governed=ONLY_SPEC)
            self.assertEqual(report.variant_total, 3)
            self.assertEqual(report.unnamed_variants, ["Dead", "Untested"])
            # `Dead` appears in a Display arm and an `if let` PATTERN; neither builds it.
            self.assertEqual(report.dead_variants, ["Dead"])

    def test_a_vanished_enum_cannot_make_the_census_vacuous(self) -> None:
        found = findings(extra={"crates/trust-ir-build/src/validate.rs": "pub fn nothing() {}\n"})
        self.assertTrue(any("cannot be vacuous" in f for f in found), found)


TRUST_DOC = """
# Trust

## Trusted base

1. **The kernel.** Trusted.
2. **The validator.** Checked by tests.

| Item | About | Enforcement |
|------|-------|-------------|
| 1 | the kernel | (prose-only) trusted by declaration |
| 2 | refusals | (test) `the_tested_rule_fires` |

## Later

3. **Not in the region.**
"""


REFUSE_MANIFEST = TOOL.REFUSE_MANIFEST
REFUSE_HEADER = "row\tcarrier\tverdicts\ttext_losses\tobligation\twhy\n"


def refuse_manifest(*rows: str) -> str:
    return "# the must-refuse corpus\n" + REFUSE_HEADER + "".join(r + "\n" for r in rows)


def corpus_section(citation: str = "refuse/row_one") -> str:
    return section(f"*Enforcement (corpus):* `{citation}`.")


class RCorpusRowsAreCitedBothWays(unittest.TestCase):
    """KIND 4: a `refuse/<row>` citation resolves against the must-refuse
    manifest and witnesses `(corpus)`; rule R holds every manifest row to a
    document that names it back."""

    ROW_ONE = "row_one\tnone\t-\t-\tdocs/SPEC_RATIFICATIONS.md\ta rule the corpus cannot express"

    def test_a_corpus_citation_resolves_and_witnesses_the_class(self) -> None:
        found = findings(corpus_section(), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE)})
        self.assertEqual(found, [])

    def test_a_citation_of_a_row_the_manifest_lacks_is_refused(self) -> None:
        found = findings(corpus_section("refuse/row_zero"), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE)})
        self.assertTrue(any("[E2]" in f and "no must-refuse corpus row named `refuse/row_zero`" in f for f in found), found)

    def test_the_corpus_class_is_witnessed_only_by_a_row(self) -> None:
        found = findings(section("*Enforcement (corpus):* `config_validates`."), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE)})
        self.assertTrue(any("[E3]" in f and "class `corpus` is not witnessed" in f for f in found), found)
        # and a row does not witness `(test)`: the classes are distinct
        found = findings(section("*Enforcement (test):* `refuse/row_one`."), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE)})
        self.assertTrue(any("[E3]" in f and "class `test` is not witnessed" in f for f in found), found)

    def test_a_row_whose_document_does_not_cite_it_back_is_refused(self) -> None:
        row = "row_two\tnone\t-\t-\tcrates/demo/src/lib.rs\tw"
        found = findings(corpus_section(), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE, row)})
        self.assertTrue(any("[R]" in f and "row `row_two`" in f and "does not name `refuse/row_two` back" in f for f in found), found)
        cited = LIB_RS + "// consumers must refuse this: refuse/row_two\n"
        found = findings(corpus_section(), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE, row), "crates/demo/src/lib.rs": cited})
        self.assertEqual([f for f in found if "[R]" in f], [])

    def test_a_longer_token_sharing_the_prefix_does_not_cite_the_row(self) -> None:
        row = "row_two\tnone\t-\t-\tcrates/demo/src/lib.rs\tw"
        cited = LIB_RS + "// refuse/row_two_renamed\n"
        found = findings(corpus_section(), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE, row), "crates/demo/src/lib.rs": cited})
        self.assertTrue(any("[R]" in f and "does not name `refuse/row_two` back" in f for f in found), found)

    def test_a_row_citing_a_missing_document_is_refused(self) -> None:
        row = "row_two\tnone\t-\t-\tdocs/gone.md\tw"
        found = findings(corpus_section(), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE, row)})
        self.assertTrue(any("[R]" in f and "`docs/gone.md`, which does not exist" in f for f in found), found)

    def test_artifact_presence_matches_the_carrier(self) -> None:
        refuse_dir = REFUSE_MANIFEST.rsplit("/", 1)[0]
        cited = LIB_RS + "// refuse/row_art\n"
        art = "row_art\tmodule\tconsumer=Consumer:some_rule\t-\tcrates/demo/src/lib.rs\tw"
        # an artifact row with no bytes
        found = findings(corpus_section(), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE, art), "crates/demo/src/lib.rs": cited})
        self.assertTrue(any("[R]" in f and "row `row_art` (module) has no" in f for f in found), found)
        # ... and with them
        found = findings(corpus_section(), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE, art), "crates/demo/src/lib.rs": cited, f"{refuse_dir}/row_art.tmbc": "x"})
        self.assertEqual([f for f in found if "[R]" in f], [])
        # a `none` row must not have one
        found = findings(corpus_section(), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE), f"{refuse_dir}/row_one.tmbc": "x"})
        self.assertTrue(any("[R]" in f and "`none` row yet" in f for f in found), found)
        # a `control` row (an artifact a consumer must ACCEPT) is a carrier with bytes
        ctl = "row_ctl\tcontrol\tvalidate_module=accepts;consumer=accepts\t-\tcrates/demo/src/lib.rs\tw"
        cited_ctl = LIB_RS + "// refuse/row_ctl\n"
        found = findings(corpus_section(), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE, ctl), "crates/demo/src/lib.rs": cited_ctl})
        self.assertTrue(any("[R]" in f and "row `row_ctl` (control) has no" in f for f in found), found)
        found = findings(corpus_section(), extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE, ctl), "crates/demo/src/lib.rs": cited_ctl, f"{refuse_dir}/row_ctl.tmbc": "x"})
        self.assertEqual([f for f in found if "[R]" in f], [])

    def test_a_malformed_manifest_is_a_finding_not_silence(self) -> None:
        found = findings(GOOD_SPEC, extra={REFUSE_MANIFEST: "row\tcarrier\n"})
        self.assertTrue(any("[R]" in f and "header" in f for f in found), found)
        found = findings(GOOD_SPEC, extra={REFUSE_MANIFEST: refuse_manifest(self.ROW_ONE, self.ROW_ONE)})
        self.assertTrue(any("[R]" in f and "listed twice" in f for f in found), found)
        found = findings(GOOD_SPEC, extra={REFUSE_MANIFEST: refuse_manifest("Bad Row\tmodule\t-\t-\tdocs/a.md\tw")})
        self.assertTrue(any("[R]" in f and "malformed" in f for f in found), found)

    def test_a_variant_a_manifest_verdict_pins_counts_as_named_by_a_test(self) -> None:
        # The synthetic ledger says two variants are unnamed (Dead, Untested);
        # a manifest row pinning `Validation:Untested` names one of them, and
        # the ratchet then demands the smaller number be written down.
        cited = LIB_RS + "// refuse/row_v\n"
        row = "row_v\tmodule\tvalidate_module=Validation:Untested\t-\tcrates/demo/src/lib.rs\tw"
        refuse_dir = REFUSE_MANIFEST.rsplit("/", 1)[0]
        found = findings(GOOD_SPEC, extra={REFUSE_MANIFEST: refuse_manifest(row), "crates/demo/src/lib.rs": cited, f"{refuse_dir}/row_v.tmbc": "x"})
        self.assertTrue(any("[E4]" in f and "validation-error-variants-unnamed`: measured 1, ledger still says 2" in f for f in found), found)


REFUSE_TEMPLATE_MANIFEST = TOOL.REFUSE_TEMPLATE_MANIFEST
REFUSE_TEMPLATE_HEADER = "row\tcarrier\tverdicts\tobligation\twhy\n"


def refuse_template_manifest(*rows: str) -> str:
    return "# the template corpus\n" + REFUSE_TEMPLATE_HEADER + "".join(r + "\n" for r in rows)


class RTemplateCorpusRowsAreCitedBothWays(unittest.TestCase):
    """Amendment S: the template corpus's own manifest. A
    `refuse_templates/<row>` citation resolves against it and witnesses
    `(corpus)`; rule R holds each row to a document naming it back and to
    its carrier's artifacts."""

    ROW = "tpl_row\tinstance\tinstantiate=Instantiate:ArityMismatch\tcrates/demo/src/lib.rs\tw"
    DIR = TOOL.REFUSE_TEMPLATE_MANIFEST.rsplit("/", 1)[0]

    def tree(self, *rows: str, cite: bool = True, artifacts: tuple = (".json", ".host.json")) -> dict:
        extra = {
            REFUSE_MANIFEST: refuse_manifest(RCorpusRowsAreCitedBothWays.ROW_ONE),
            REFUSE_TEMPLATE_MANIFEST: refuse_template_manifest(*(rows or (self.ROW,))),
            "crates/demo/src/lib.rs": LIB_RS + ("// refuse_templates/tpl_row\n" if cite else ""),
        }
        for suffix in artifacts:
            extra[f"{self.DIR}/tpl_row{suffix}"] = "x"
        return extra

    @staticmethod
    def cites(row: str = "refuse_templates/tpl_row") -> str:
        # The module corpus's synthetic row is named back by the same spec.
        return section(f"*Enforcement (corpus):* `refuse/row_one` and `{row}`.")

    def test_a_template_row_cited_both_ways_is_clean(self) -> None:
        found = findings(self.cites(), extra=self.tree())
        self.assertEqual(found, [])

    def test_a_citation_of_a_template_row_the_manifest_lacks_is_refused(self) -> None:
        found = findings(self.cites("refuse_templates/tpl_none"), extra=self.tree())
        self.assertTrue(any("[E2]" in f and "`refuse_templates/tpl_none`" in f and "refuse_templates/MANIFEST.tsv" in f for f in found), found)

    def test_a_template_row_whose_document_does_not_cite_it_back_is_refused(self) -> None:
        found = findings(self.cites(), extra=self.tree(cite=False))
        self.assertTrue(any("[R]" in f and "does not name `refuse_templates/tpl_row` back" in f for f in found), found)

    def test_an_instance_row_needs_its_template_and_its_host_script(self) -> None:
        found = findings(self.cites(), extra=self.tree(artifacts=(".json",)))
        self.assertTrue(any("[R]" in f and "tpl_row.host.json" in f for f in found), found)

    def test_an_unknown_template_carrier_is_malformed(self) -> None:
        bad = "tpl_row\tmodule\t-\tcrates/demo/src/lib.rs\tw"
        found = findings(corpus_section("refuse/row_one"), extra=self.tree(bad))
        self.assertTrue(any("[R]" in f and "carrier `module` is malformed" in f for f in found), found)


class NumberedItemsAndTheirEvidenceTable(unittest.TestCase):
    ITEMS = (TOOL.Doc("TRUST.md", "items", region="## Trusted base"),)
    # Only TRUST.md is governed here, so the one named debt is its item 1.
    ITEM_LEDGER = LEDGER.replace("docs/SPEC_RATIFICATIONS.md §2", "TRUST.md item 1")

    def test_items_are_covered_by_table_rows(self) -> None:
        found = findings(extra={"TRUST.md": TRUST_DOC}, governed=self.ITEMS, ledger_text=self.ITEM_LEDGER)
        self.assertEqual(found, [])

    def test_an_item_with_no_row_and_a_row_with_no_item_are_refused(self) -> None:
        orphan = TRUST_DOC.replace("| 2 | refusals |", "| 7 | refusals |")
        found = findings(extra={"TRUST.md": orphan}, governed=self.ITEMS)
        self.assertTrue(any("item 2" in f and "no Enforcement entry" in f for f in found), found)
        self.assertTrue(any("names item `7`" in f for f in found), found)

    def test_a_table_cell_without_a_class_is_refused(self) -> None:
        unclassed = TRUST_DOC.replace("(test) `the_tested_rule_fires`", "`the_tested_rule_fires`")
        found = findings(extra={"TRUST.md": unclassed}, governed=self.ITEMS)
        self.assertTrue(any("no evidence class" in f for f in found), found)

    def test_a_pipe_inside_backticks_does_not_split_a_cell(self) -> None:
        self.assertEqual(TOOL.split_row("| a | `x|y` | (test) `t` |"), ["a", "`x|y`", "(test) `t`"])


class ThePublicSnapshot(unittest.TestCase):
    def test_an_unexported_document_is_skipped_only_when_asked(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            synthetic(root)
            (root / SPEC_DOC).unlink()
            closed = TOOL.run(root, base_ref=None, governed=ONLY_SPEC)
            self.assertTrue(any("governed document is missing" in str(f) for f in closed.findings))
            asked = TOOL.run(root, base_ref=None, governed=ONLY_SPEC, snapshot=True)
            self.assertEqual([str(f) for f in asked.findings], [])
            self.assertEqual(asked.skipped, [SPEC_DOC])


    def test_a_snapshot_is_a_tree_missing_everything_a_snapshot_never_ships(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            synthetic(root)
            self.assertFalse(TOOL.is_public_snapshot(root))  # docs/ is there
            (root / SPEC_DOC).unlink()
            # docs/ still exists: a missing governed document is a BROKEN
            # checkout, not a snapshot, and the CLI still fails closed.
            self.assertFalse(TOOL.is_public_snapshot(root))
            broken = subprocess.run([sys.executable, "-B", os.fspath(TOOL_PATH), "--root", os.fspath(root), "--base-ref", "", "check"], capture_output=True, text=True)
            self.assertEqual(broken.returncode, 1, broken.stdout)
            self.assertIn("governed document is missing", broken.stderr)
            (root / "docs").rmdir()
            self.assertTrue(TOOL.is_public_snapshot(root))


# `scripts/` ships whole, so this file runs in the public clone too
# (scripts/ci-self-verify.sh), where docs/ is absent BY DESIGN.
SNAPSHOT = TOOL.is_public_snapshot(ROOT)


class TheLiveRepository(unittest.TestCase):
    """Mutations of the REAL governed documents, in memory."""

    index = None

    @classmethod
    def setUpClass(cls) -> None:
        cls.index = TOOL.build_index(ROOT)
        cls.spec = None if SNAPSHOT else (ROOT / SPEC_DOC).read_text(encoding="utf-8")
        cls.trust = (ROOT / "TRUST.md").read_text(encoding="utf-8")

    def setUp(self) -> None:
        needs_the_ratifications = "ratification" in self._testMethodName or self._testMethodName in self.NEED_THE_LEDGER
        if SNAPSHOT and needs_the_ratifications:
            self.skipTest("public snapshot: docs/ is not exported, so neither the ratifications nor the ratchet over them can be mutated here")

    # Tests that read the ratifications or the ledger over them.
    NEED_THE_LEDGER = (
        "test_relabelling_any_code_entry_as_a_test_is_caught",
        "test_raising_the_checked_in_count_is_refused",
        "test_an_honest_downgrade_of_a_live_unit_is_recorded_not_refused",
        "test_a_live_debt_cannot_be_retired_by_a_comment",
        "test_naming_a_gate_does_not_back_a_live_debt",
    )

    def run_with(self, overrides: Dict[str, str], ledger_text: Optional[str] = None, base=None) -> List[str]:
        report = TOOL.run(ROOT, base_ref=None, index=self.index, overrides=overrides, ledger_text=ledger_text, snapshot=SNAPSHOT, base=base)
        return [str(f) for f in report.findings]

    def units_today(self) -> Dict[str, bool]:
        then: Dict[str, bool] = {}
        for doc, text in ((TOOL.GOVERNED[0], self.spec), (TOOL.GOVERNED[1], self.trust)):
            for unit in TOOL.parse_document(doc, text)[0]:
                then[f"{doc.path} {unit.ident}"] = unit.backed_in_tree()
        return then

    def test_the_unmutated_documents_are_green(self) -> None:
        self.assertEqual(self.run_with({}), [])

    # --- The reviewer's three executed routes, against the LIVE documents.
    # --- Every name below is DERIVED from the live tree, never spelled.

    def test_an_honest_downgrade_of_a_live_unit_is_recorded_not_refused(self) -> None:
        # A unit resting on exactly ONE checked entry, in line form: relabel
        # that entry `(prose-only)` and the unit has no checked evidence left.
        doc = TOOL.GOVERNED[0]
        unit = next(
            (u for u in TOOL.parse_document(doc, self.spec)[0] if [e.form for e in u.entries if e.cls in TOOL.IN_TREE] == ["line"]),
            None,
        )
        if unit is None:
            self.skipTest("no live unit rests on a single line-form checked entry; the synthetic test pins the rule")
        entry = next(e for e in unit.entries if e.cls in TOOL.IN_TREE)
        lines = self.spec.split("\n")
        lines[entry.line - 1] = lines[entry.line - 1].replace(f"*Enforcement ({entry.cls}):*", "*Enforcement (prose-only):*", 1)
        downgraded = "\n".join(lines)
        self.assertNotEqual(downgraded, self.spec)
        member = f"{SPEC_DOC} {unit.ident}"
        ledger = (ROOT / TOOL.RATCHET).read_text(encoding="utf-8")
        bare = self.run_with({SPEC_DOC: downgraded})
        self.assertEqual(len(bare), 1, bare)
        self.assertIn("honest downgrade", bare[0])
        recorded = ledger + f"correction {TOOL.SECTION_LEDGER} 2099-01-01 {member} :: read on review: the cited evidence does not back the claim\nmember {TOOL.SECTION_LEDGER} {member}\n"
        self.assertEqual(self.run_with({SPEC_DOC: downgraded}, ledger_text=recorded, base=(ledger, self.units_today())), [])

    def test_a_live_debt_cannot_be_retired_by_a_comment(self) -> None:
        ledger = (ROOT / TOOL.RATCHET).read_text(encoding="utf-8")
        parsed = TOOL.parse_ledger(ledger)
        debts = [m for m in parsed.members.get(TOOL.SECTION_LEDGER, {}) if m.startswith(SPEC_DOC + " ")]
        if not debts:
            self.skipTest("every ratification has checked evidence; the synthetic test pins the rule")
        member = debts[0]
        doc = TOOL.GOVERNED[0]
        unit = next(u for u in TOOL.parse_document(doc, self.spec)[0] if f"{SPEC_DOC} {u.ident}" == member)
        lines = self.spec.split("\n")
        for entry in sorted(unit.entries, key=lambda e: -e.line):  # drop each entry paragraph
            end = entry.line - 1
            while end < len(lines) and lines[end].strip():
                end += 1
            del lines[entry.line - 1 : end]
        lines.insert(unit.line, "\n<!-- enforcement-links: not-normative it is a statement of intent -->")
        opted = "\n".join(lines)
        count = parsed.rows[TOOL.SECTION_LEDGER][-1][2]
        paid = ledger.replace(f"member {TOOL.SECTION_LEDGER} {member}\n", "") + f"{TOOL.SECTION_LEDGER} 2099-01-01 {count - 1} not normative after all\n"
        # With no base to compare against, this is exactly what used to pass ...
        self.assertEqual(self.run_with({SPEC_DOC: opted}, ledger_text=paid), [])
        # ... and against the merge-base it is refused, by name.
        found = self.run_with({SPEC_DOC: opted}, ledger_text=paid, base=(ledger, self.units_today()))
        self.assertEqual(len(found), 1, found)
        self.assertIn("A marker does not retire a claim", found[0])
        self.assertIn(member, found[0])

    def test_naming_a_gate_does_not_back_a_live_debt(self) -> None:
        # The WHOLE entry is replaced, so the gate name is the only citation:
        # a prose-only paragraph may itself name real tests (to say they do NOT
        # cover the claim), and relabelling THAT is the disclosed limit — a
        # cited test exists, never that it tests the claim — not this one.
        gate = next(name for name, defs in sorted(self.index.defs.items()) if any(d.kind == "gate" for d in defs))
        doc = TOOL.GOVERNED[0]
        debts = [u for u in TOOL.parse_document(doc, self.spec)[0] if u.entries and not u.backed_in_tree()]
        if not debts:
            self.skipTest("every ratification has checked evidence; the synthetic test pins the rule")
        for unit in debts:
            lines = self.spec.split("\n")
            for entry in sorted(unit.entries, key=lambda e: -e.line):
                end = entry.line - 1
                while end < len(lines) and lines[end].strip():
                    end += 1
                del lines[entry.line - 1 : end]
            lines.insert(unit.line, f"\n*Enforcement (test):* the `{gate}` gate.")
            found = self.run_with({SPEC_DOC: "\n".join(lines)})
            self.assertTrue(any(f"[E3] {unit.ident}:" in f and "is not witnessed" in f for f in found), (unit.ident, found))

    def cited(self, doc_path: str, text: str, cls: str, kind: str):
        """(unit, entry, token): the first citation of `kind` in an entry of class
        `cls`.  DERIVED from the live document, so a rename elsewhere in the
        repository cannot break the tests below; only the gate's rules can."""
        doc = next(d for d in TOOL.GOVERNED if d.path == doc_path)
        units, _, _ = TOOL.parse_document(doc, text)
        for unit in units:
            for entry in unit.entries:
                if entry.cls != cls:
                    continue
                for token in TOOL.TOKEN.findall(entry.text):
                    _, kinds, _ = TOOL.resolve(self.index, ROOT, token)
                    if kinds and kind in kinds:
                        return unit, entry, token
        self.fail(f"{doc_path} has no `{cls}` entry citing a {kind}")

    def test_a_renamed_test_function_in_the_ratifications_is_caught(self) -> None:
        unit, _, token = self.cited(SPEC_DOC, self.spec, "test", "test-fn")
        name = token.split("::")[-1]
        found = self.run_with({SPEC_DOC: self.spec.replace(name, name + "_renamed")})
        self.assertTrue(found, token)
        self.assertTrue(all("[E2]" in f or "[E3]" in f for f in found), found)
        self.assertTrue(any(f"[E2] {unit.ident}:" in f and name + "_renamed" in f for f in found), found)

    def test_a_moved_test_file_in_the_ratifications_is_caught(self) -> None:
        unit, _, token = self.cited(SPEC_DOC, self.spec, "test", "test-file")
        moved = token.replace(".rs", "_moved.rs")
        found = self.run_with({SPEC_DOC: self.spec.replace(token, moved)})
        self.assertTrue(any(f"[E2] {unit.ident}:" in f and moved in f for f in found), found)

    def test_a_rotted_theorem_in_the_trust_table_takes_its_class_with_it(self) -> None:
        unit, entry, token = self.cited("TRUST.md", self.trust, "lean-theorem", "lean-theorem")
        found = self.run_with({"TRUST.md": self.trust.replace(f"`{token}`", f"`{token}_gone`")})
        self.assertTrue(any(f"[E2] {unit.ident}:" in f for f in found), found)
        others = [t for t in TOOL.TOKEN.findall(entry.text) if t != token]
        still_witnessed = any("lean-theorem" in (TOOL.resolve(self.index, ROOT, t)[1] or set()) for t in others)
        if not still_witnessed:
            # No theorem is left cited, so the CLASS is refused too, not just the name.
            self.assertTrue(any(f"[E3] {unit.ident}:" in f and "lean-theorem" in f for f in found), found)

    def test_relabelling_any_code_entry_as_a_test_is_caught(self) -> None:
        # DERIVED, never spelled: this test once named section 1.1 as "the" code
        # entry, and broke the day that debt was paid.  Every `(code)` entry the
        # live document has today is relabelled `(test)`, one at a time; the
        # witness rule must refuse each, because no words were changed.
        label = "*Enforcement (code):*"
        positions = [i for i in range(len(self.spec)) if self.spec.startswith(label, i)]
        # When the last such debt is paid there is nothing to relabel, and that
        # must not turn this red: the synthetic `test_rewording_cannot_raise_a_class`
        # pins the rule for good.  Paying a debt never breaks a test.
        for position in positions:
            relabelled = self.spec[:position] + "*Enforcement (test):*" + self.spec[position + len(label):]
            found = self.run_with({SPEC_DOC: relabelled})
            self.assertTrue(any("[E3]" in f and "is not witnessed" in f for f in found), (position, found))

    # --- `(proved-contract)` against the LIVE documents: every name derived.

    def live_docs(self):
        """(path, text) of each governed document this tree carries."""
        return [(path, text) for path, text in ((SPEC_DOC, self.spec), ("TRUST.md", self.trust)) if text is not None]

    def proved_contract_entries(self):
        """(doc path, unit, entry) of every live `(proved-contract)` entry."""
        found = []
        for path, text in self.live_docs():
            doc = next(d for d in TOOL.GOVERNED if d.path == path)
            for unit in TOOL.parse_document(doc, text)[0]:
                found += [(path, unit, e) for e in unit.entries if e.cls == "proved-contract"]
        return found

    @staticmethod
    def replace_in_entry(text: str, entry, old: str, new: str) -> str:
        """`text` with the first `old` at or after `entry`'s first line replaced."""
        start = sum(len(line) + 1 for line in text.split("\n")[: entry.line - 1])
        at = text.index(old, start)
        return text[:at] + new + text[at + len(old) :]

    def test_the_trusted_base_cites_a_proved_contract(self) -> None:
        # TRUST.md ships in the public snapshot too, so this holds in both.
        self.cited("TRUST.md", self.trust, "proved-contract", "law")

    def test_the_fresh_id_ratification_cites_every_fresh_id_table_before_its_laws(self) -> None:
        # Round 11's one fresh-id rule decides by monomorphic `u32` tables
        # resident in trust-ir (every gate-13 table named `fresh_*`, derived
        # here from what gate 13 holds). The ratification unit that states
        # the rule carries ONE `(proved-contract)` entry that reads a law of
        # EVERY such table under a citation of that table, so no table of
        # the rule is left uncited and no law of it is read under another.
        held = self.index.gate13
        self.assertIsNotNone(held)
        fresh = sorted({t for t in held.tables.values() if t and t.startswith("fresh_")})
        self.assertTrue(fresh, "gate 13 holds no law of a fresh-id table")
        citing = []
        for path, unit, entry in self.proved_contract_entries():
            under = {current for _, current, _, _ in self.law_citations_under_tables(entry)}
            if under & set(fresh):
                citing.append((path, unit.ident, sorted(under)))
        self.assertEqual(len(citing), 1, citing)
        path, ident, under = citing[0]
        self.assertEqual(path, SPEC_DOC, citing)
        self.assertEqual(under, fresh, ident)

    def test_a_live_proved_contract_repointed_at_a_law_of_another_table_is_caught(self) -> None:
        held = self.index.gate13
        self.assertIsNotNone(held)
        for path, text in self.live_docs():
            unit, entry, token = self.cited(path, text, "proved-contract", "law")
            tables = {held.tables[law] for law in TOOL.law_names(self.index, token)}
            other = next(law for law in held.held if held.tables[law] not in tables | {None} and held.tables[law] not in entry.text)
            found = self.run_with({path: self.replace_in_entry(text, entry, f"`{token}`", f"`laws::{other}`")})
            self.assertTrue(
                any(f"[E3] {unit.ident}:" in f and f"`{held.tables[other]}`" in f for f in found), (path, token, other, found)
            )

    def law_citations_under_tables(self, entry):
        """`(token, table it is read under, laws, tables cited before it)` for
        each law citation of a live entry, walked as the gate walks it."""
        held = self.index.gate13
        definitions = TOOL.table_definitions(self.index, held)
        current, seen, out = None, [], []
        for token in TOOL.TOKEN.findall(entry.text):
            laws = TOOL.law_names(self.index, token)
            if laws:
                out.append((token, current, laws, list(seen)))
                continue
            table = TOOL.cited_table(self.index, token, definitions)
            if table:
                current = table
                seen += [table] if table not in seen else []
        return out

    def test_a_live_law_moved_under_another_table_of_its_ratification_entry_is_caught(self) -> None:
        # The review's M1 (a11, a12) on every live multi-table entry: a law
        # of a table the entry cites EARLIER put where a law of a later table
        # stands. Its table is still cited in the entry, and it is refused.
        held = self.index.gate13
        tried = []
        for path, unit, entry in self.proved_contract_entries():
            text = self.spec if path == SPEC_DOC else self.trust
            for token, current, laws, seen in self.law_citations_under_tables(entry):
                earlier = [t for t in seen if t != current]
                if not earlier or "*" in token:
                    continue
                other = next(law for law in held.held if held.tables[law] == earlier[0])
                found = self.run_with({path: self.replace_in_entry(text, entry, f"`{token}`", f"`laws::{other}`")})
                self.assertTrue(
                    any(f"[E3] {unit.ident}:" in f and f"the table citation it follows is `{current}`" in f for f in found),
                    (path, token, other, found),
                )
                tried.append((path, entry.line))
                break
        self.assertTrue(tried, "no live entry cites a law after a second table")

    def test_a_live_table_citation_respelled_ambiguously_is_caught(self) -> None:
        # The review's L4 (a9) on the live documents: each live table citation
        # respelled by its bare last segment — which either also names another
        # item (`proof_ref_kind_is_ambiguous`, the validator's private
        # wrapper) or does not say whose method it is — cites no table, so
        # the laws after it are refused.
        definitions = TOOL.table_definitions(self.index, self.index.gate13)
        tried = 0
        for path, unit, entry in self.proved_contract_entries():
            text = self.spec if path == SPEC_DOC else self.trust
            for token in dict.fromkeys(TOOL.TOKEN.findall(entry.text)):
                table = TOOL.cited_table(self.index, token, definitions)
                bare = (table or "").split("::")[-1]
                if not table or bare == token or TOOL.cited_table(self.index, bare, definitions) is not None:
                    continue
                found = self.run_with({path: self.replace_in_entry(text, entry, f"`{token}`", f"`{bare}`")})
                self.assertTrue(any(f"[E3] {unit.ident}:" in f and f"is a law of `{table}`" in f for f in found), (path, token, found))
                tried += 1
        self.assertTrue(tried)

    def assert_every_live_proved_contract_falls(self, refusing) -> None:
        """Every live `(proved-contract)` entry is refused when gate 13 holds
        what `refusing` holds (nothing)."""
        self.assertEqual(refusing.held, ())
        entries = self.proved_contract_entries()
        self.assertTrue(entries)
        saved = self.index.gate13
        try:
            self.index.gate13 = refusing
            found = self.run_with({})
        finally:
            self.index.gate13 = saved
        for path, unit, entry in entries:
            self.assertTrue(
                any(f.startswith(f"{path}:{entry.line}: [E3] {unit.ident}:") and "gate 13 holds no law" in f for f in found),
                (path, unit.ident, entry.line, found),
            )

    def test_every_live_proved_contract_falls_when_gate_13_would_refuse_to_run(self) -> None:
        # Drop the one mutant that alone refutes some law: gate 13 then refuses
        # to run, holds nothing, and every `(proved-contract)` entry is refused.
        gate13 = TOOL.gate13
        laws = gate13.law_functions(ROOT)
        flips = {m.name: set(gate13.expand_flips(m, laws)) for m in gate13.MUTANTS}
        sole = next(m for m in gate13.MUTANTS if any(sum(law in flips[n.name] for n in gate13.MUTANTS) == 1 for law in flips[m.name]))
        with mock.patch.object(gate13, "MUTANTS", tuple(m for m in gate13.MUTANTS if m is not sole)):
            refusing = gate13.holding(ROOT)
        self.assert_every_live_proved_contract_falls(refusing)

    def test_every_live_proved_contract_falls_when_a_table_gains_a_variant_without_a_law(self) -> None:
        # The review's M2 forward scenario: an enum a cell table ranges over
        # gains a variant and no law states its cell. Gate 13 refuses to run,
        # so a glob citation (`laws::ambiguous_*`) can no longer stand for a
        # family that misses a cell.
        gate13 = TOOL.gate13
        real = gate13.enum_definitions

        def planted(root, names):
            found, errors = real(root, names)
            name = sorted(n for n in found if found[n])[0]
            found[name] = [gate13.EnumDefinition(d.path, d.variants + ("Planted",)) for d in found[name]]
            return found, errors

        with mock.patch.object(gate13, "enum_definitions", planted):
            refusing = gate13.holding(ROOT)
        self.assertTrue(any("::Planted)" in e for e in refusing.errors), refusing.errors)
        self.assert_every_live_proved_contract_falls(refusing)

    def test_relabelling_every_live_test_entry_as_a_proved_contract_is_caught(self) -> None:
        # No words change, so no `(test)` entry can become a proved contract.
        for path, text in self.live_docs():
            doc = next(d for d in TOOL.GOVERNED if d.path == path)
            lines = {e.line for u in TOOL.parse_document(doc, text)[0] for e in u.entries if e.cls == "test"}
            self.assertTrue(lines, path)
            relabelled = text.replace("*Enforcement (test):*", "*Enforcement (proved-contract):*").replace("| (test) ", "| (proved-contract) ")
            found = self.run_with({path: relabelled})
            for line in sorted(lines):
                self.assertTrue(any(f.startswith(f"{path}:{line}: [E3]") for f in found), (path, line))

    def test_a_new_prose_only_ratification_raises_the_count_and_is_refused(self) -> None:
        added = self.spec + "\n## 9. A rule nobody checks\n\nText.\n\n*Enforcement (prose-only):* nothing.\n"
        found = self.run_with({SPEC_DOC: added})
        self.assertEqual(len(found), 1, found)
        self.assertIn("[E4]", found[0])
        self.assertIn("§9", found[0])

    def test_raising_the_checked_in_count_is_refused(self) -> None:
        ledger = (ROOT / TOOL.RATCHET).read_text(encoding="utf-8")
        current = TOOL.parse_ledger(ledger).rows[TOOL.SECTION_LEDGER][-1][2]
        raised = ledger + f"{TOOL.SECTION_LEDGER} 2099-01-01 {current + 1} one more unbacked claim\n"
        found = self.run_with({}, ledger_text=raised)
        self.assertTrue(any(f"rose from {current} to {current + 1}" in f for f in found), found)

    def test_every_ledger_is_tight(self) -> None:
        ledger = (ROOT / TOOL.RATCHET).read_text(encoding="utf-8")
        parsed = TOOL.parse_ledger(ledger)
        self.assertEqual(parsed.findings, [])
        self.assertEqual(sorted(parsed.rows), sorted(TOOL.LEDGERS))
        for name in TOOL.LEDGERS:
            # Derived, never spelled: the count IS the number of named debts.
            self.assertEqual(parsed.rows[name][-1][2], len(parsed.members.get(name, {})), name)


    # --- Rule E5 against the LIVE documents: every name and phrase derived.
    # The FIRST trial of each test is derived by a plain pattern over the live
    # text (no E5 code) and goes through the full gate (`run_with`), so the
    # gate before E5 fails it by assertion, not by a missing attribute; the
    # rest are derived from the entry's clauses and call `check_says` on the
    # mutated entry alone.

    SAID = ("proved-contract", "lean-theorem")
    NUMBERS = "zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen seventeen eighteen nineteen twenty".split()

    def said_entries(self):
        """(doc path, text, unit, entry) of every live entry rule E5 reads."""
        found = []
        for path, text in self.live_docs():
            doc = next(d for d in TOOL.GOVERNED if d.path == path)
            for unit in TOOL.parse_document(doc, text)[0]:
                found += [(path, text, unit, e) for e in unit.entries if e.cls in self.SAID]
        return found

    def first_trial(self, cls: str, pattern: str, new, needle: str = "[E5]") -> None:
        """Through the full gate: the first live entry of class `cls` where
        `pattern` matches, that match replaced by `new` (text, or a function
        of the match), must be refused with a finding carrying `needle`."""
        for path, text, unit, entry in self.said_entries():
            match = re.search(pattern, entry.text) if entry.cls == cls else None
            if match is None:
                continue
            replacement = new(match) if callable(new) else new
            doc = next(d for d in TOOL.GOVERNED if d.path == path)
            mutated = self.doc_with(text, entry, match.start(), match.end(), replacement)
            expected = " ".join((entry.text[: match.start()] + replacement + entry.text[match.end() :]).split())
            self.assertIn(expected, [" ".join(e.text.split()) for u in TOOL.parse_document(doc, mutated)[0] for e in u.entries])
            found = self.run_with({path: mutated})
            self.assertTrue(
                any(f.startswith(f"{path}:{entry.line}: [E5]") and needle in f for f in found), (path, entry.line, match.group(0), replacement, found)
            )
            return
        self.fail(f"no live `{cls}` entry matches {pattern!r}")

    def bound(self, entry, token: str) -> bool:
        if entry.cls == "proved-contract":
            return bool(TOOL.law_names(self.index, token))
        return any(d.kind in TOOL.THEOREM_KINDS for d in TOOL.qualified_definitions(self.index, token))

    def events(self, entry):
        """Per clause, the verdict phrases `(start, end, kind, verdict,
        governed)` — `governed` the bound citations `(start, end, token)` it
        governs — and the clause's bound citations."""
        masked = TOOL.masked_text(entry.text)
        out = []
        for a, b in TOOL.clauses(entry.text):
            items = []
            for m in TOOL.PHRASE.finditer(masked, a, b):
                i = next(i for i in range(len(TOOL._PHRASES)) if m.group(f"p{i}") is not None)
                _, kind, verdict = TOOL._PHRASES[i]
                items.append((m.start(), m.end(), "phrase", (kind, verdict)))
            cites = [(t.start(), t.end(), t.group(1)) for t in TOOL.TOKEN.finditer(entry.text, a, b) if self.bound(entry, t.group(1))]
            items += [(x, y, "cite", tok) for x, y, tok in cites]
            items.sort()
            phrases, lead, pending = [], None, []
            for x, y, what, data in items:
                if what == "phrase":
                    kind, verdict = data
                    record = [x, y, kind, verdict, []]
                    if kind == "leading":
                        lead, pending = record, []
                    else:
                        record[4].extend(pending)
                        pending = []
                    phrases.append(record)
                elif lead is not None:
                    lead[4].append((x, y, data))
                else:
                    pending.append((x, y, data))
            out.append((phrases, cites))
        return out

    def doc_with(self, text: str, entry, start: int, end: int, new: str) -> str:
        """The live document `text` with `entry.text[start:end]` replaced."""
        lines = text.split("\n")
        offsets = [0]
        for line in lines:
            offsets.append(offsets[-1] + len(line) + 1)
        if entry.form == "table":
            base = offsets[entry.line - 1] + lines[entry.line - 1].index(entry.text)
            segments = [(0, base, len(entry.text))]
        else:
            head = TOOL.ENTRY_LINE.match(lines[entry.line - 1])
            segments = [(0, offsets[entry.line - 1] + head.start(2), len(head.group(2)))]
            at, j = len(head.group(2)) + 1, entry.line
            while at < len(entry.text):
                raw = lines[j]
                segments.append((at, offsets[j] + len(raw) - len(raw.lstrip()), len(raw.strip())))
                at, j = at + len(raw.strip()) + 1, j + 1

        def to_doc(pos: int) -> int:
            return next(doc + pos - at for at, doc, n in segments if at <= pos <= at + n)

        return text[: to_doc(start)] + new + text[to_doc(end) :]

    def caught(self, path, unit, entry, start, end, new, needle="[E5]") -> bool:
        """Is `entry` with `entry.text[start:end]` replaced by `new` refused
        by rule E5 with a finding carrying `needle`?"""
        mutated = entry.text[:start] + new + entry.text[end:]
        doc = next(d for d in TOOL.GOVERNED if d.path == path)
        report = TOOL.Report()
        TOOL.check_says(self.index, ROOT, doc, unit, TOOL.Entry(entry.line, entry.cls, mutated, entry.form), report)
        return any("[E5]" in str(f) and needle in str(f) for f in report.findings)

    def trials(self, mutations, needle="[E5]"):
        """Run `(path, text, unit, entry, start, end, new)` mutations; return
        the ones NOT caught."""
        missed = []
        for path, text, unit, entry, start, end, new in mutations:
            if not self.caught(path, unit, entry, start, end, new, needle):
                missed.append((path, entry.line, entry.text[max(0, start - 40) : end + 40], new))
        return missed

    FLIP = {"true": "false", "false": "true"}

    def test_e5_every_live_law_verdict_phrase_flipped_is_caught(self) -> None:
        self.first_trial("proved-contract", r"\btrue at\b", "false at")
        mutations, relations = [], []
        for path, text, unit, entry in self.said_entries():
            if entry.cls != "proved-contract":
                continue
            for phrases, _ in self.events(entry):
                for start, end, kind, verdict, governed in phrases:
                    if not governed:
                        continue
                    said = entry.text[start:end]
                    if verdict in self.FLIP:
                        mutations.append((path, text, unit, entry, start, end, said.replace(verdict, self.FLIP[verdict])))
                    elif verdict == "relation":
                        rel = re.search(r"when (.+?) (<=|>=|<|>) (.+?) at\Z", said)
                        self.assertIsNotNone(rel, said)
                        swapped = said[: rel.start(1)] + f"{rel.group(3)} {rel.group(2)} {rel.group(1)}" + said[rel.end(3) :]
                        relations.append((path, text, unit, entry, start, end, swapped))
        self.assertTrue(mutations)
        if not SNAPSHOT:
            self.assertTrue(relations)
        self.assertEqual(self.trials(mutations + relations), [])

    def test_e5_every_live_law_swapped_for_an_opposite_verdict_law_of_its_table_is_caught(self) -> None:
        # First: the first law said true and the next said false, swapped.
        self.first_trial(
            "proved-contract",
            r"\btrue at `laws::(\w+)`(?P<rest>.*?)\bfalse at `laws::(\w+)`",
            lambda m: f"true at `laws::{m.group(3)}`{m.group('rest')}false at `laws::{m.group(1)}`",
        )
        held = self.index.gate13
        mutations = []
        for path, text, unit, entry in self.said_entries():
            if entry.cls != "proved-contract":
                continue
            for _, cites in self.events(entry):
                for start, end, token in cites:
                    laws = TOOL.law_names(self.index, token)
                    if len(laws) != 1 or "*" in token:
                        continue
                    law = laws[0]
                    other = next(
                        (o for o in held.held if held.tables.get(o) == held.tables[law] and held.verdicts[o] != held.verdicts[law]), None
                    )
                    if other is not None:
                        mutations.append((path, text, unit, entry, start, end, f"`laws::{other}`"))
        self.assertTrue(mutations)
        self.assertEqual(self.trials(mutations), [])

    def test_e5_every_live_verdict_phrase_deleted_is_caught(self) -> None:
        self.first_trial("proved-contract", r"\btrue at ", "", "no verdict phrase governs it")
        mutations = []
        for path, text, unit, entry in self.said_entries():
            for phrases, _ in self.events(entry):
                leads = [p for p in phrases if p[2] == "leading"]
                for start, end, kind, verdict, governed in phrases:
                    if not governed:
                        continue
                    # An earlier leading phrase of the same verdict in the
                    # clause would govern what this one governed: the
                    # English would still say the statement's verdict.
                    if any(p[0] < start and p[3] == verdict for p in leads):
                        continue
                    mutations.append((path, text, unit, entry, start, end, ""))
        self.assertTrue(mutations)
        self.assertEqual(self.trials(mutations), [])

    def test_e5_live_count_words_and_exactly_lists_that_drift_are_caught(self) -> None:
        self.first_trial(
            "proved-contract",
            r"\bthe (\w+) other laws of",
            lambda m: m.group(0).replace(m.group(1), self.NUMBERS[self.NUMBERS.index(m.group(1)) + 1]),
            "other laws of",
        )
        mutations = []
        for path, text, unit, entry in self.said_entries():
            if entry.cls != "proved-contract":
                continue
            masked = TOOL.masked_text(entry.text)
            for m in re.finditer(r"\bthe (\w+) other laws of", masked):
                count = TOOL.number_word(m.group(1))
                self.assertIsNotNone(count, m.group(0))
                mutations.append((path, text, unit, entry, m.start(1), m.end(1), str(count + 1)))
            for phrases, _ in self.events(entry):
                for start, end, kind, verdict, governed in phrases:
                    if "exactly at" in entry.text[start:end] and len(governed) > 1:
                        x, y, _ = governed[-1]
                        mutations.append((path, text, unit, entry, x, y, ""))
        self.assertTrue(any("other laws" in m[3].text for m in mutations))
        self.assertTrue(any("exactly at" in m[3].text for m in mutations))
        self.assertEqual(self.trials(mutations), [])

    LEAN_FLIP = {"ub": "runs", "runs": "is UB", "noop": "is UB", "true": "false at", "false": "true at"}

    def test_e5_every_live_lean_verdict_flipped_is_caught(self) -> None:
        self.first_trial("lean-theorem", r"\bis UB\b", "runs", "says `runs`")
        mutations = []
        for path, text, unit, entry in self.said_entries():
            if entry.cls != "lean-theorem":
                continue
            for phrases, _ in self.events(entry):
                for start, end, kind, verdict, governed in phrases:
                    if governed and kind == "leading":
                        mutations.append((path, text, unit, entry, start, end, self.LEAN_FLIP[verdict]))
        self.assertTrue(mutations)
        self.assertEqual(self.trials(mutations), [])

    def cited_theorems(self):
        """(path, text, unit, entry, start, end, token, reader verdict) of
        every live theorem citation."""
        out = []
        for path, text, unit, entry in self.said_entries():
            if entry.cls != "lean-theorem":
                continue
            for _, cites in self.events(entry):
                for start, end, token in cites:
                    defs = [d for d in TOOL.qualified_definitions(self.index, token) if d.kind in TOOL.THEOREM_KINDS]
                    statement = TOOL.lean_statement(self.index, ROOT, defs[0])
                    self.assertIsNotNone(statement, token)
                    out.append((path, text, unit, entry, start, end, token, TOOL.lean_conclusion_verdict(statement.conclusion)))
        return out

    def test_e5_every_live_theorem_swapped_for_one_of_another_class_is_caught(self) -> None:
        # First: a UB example and a run example of one entry, swapped.
        self.first_trial(
            "lean-theorem",
            r"`(\w+_is_ub_example)`(?P<rest>.*?)`(\w+_ok_example)`",
            lambda m: f"`{m.group(3)}`{m.group('rest')}`{m.group(1)}`",
        )
        cited = self.cited_theorems()
        mutations = []
        for path, text, unit, entry, start, end, token, verdict in cited:
            if verdict is None:
                continue
            other = next((c[6] for c in sorted(cited, key=lambda c: c[6]) if c[7] is not None and c[7] not in TOOL.SUBSUMES.get(verdict, {verdict}) and verdict not in TOOL.SUBSUMES.get(c[7], {c[7]})), None)
            self.assertIsNotNone(other, token)
            mutations.append((path, text, unit, entry, start, end, f"`{other}`"))
        self.assertTrue(mutations)
        self.assertEqual(self.trials(mutations), [])

    # A theorem's name is an oracle independent of the reader: a verdict
    # suffix names the class its conclusion must read as, when readable.
    NAME_CLASSES = (("_is_ub_example", "ub"), ("_is_ub_stable", "ub"), ("_is_ub", "ub"), ("_ok_example", "runs"), ("_is_noop", "noop"))

    def test_e5_the_reader_agrees_with_every_cited_theorems_verdict_suffix(self) -> None:
        # First: a UB example said to run is refused.
        self.first_trial("lean-theorem", r"\bis UB\b(?=[^;]*`\w+_is_ub_example`)", "runs", "says `runs`")
        checked = 0
        for *_, token, verdict in self.cited_theorems():
            name = token.split(".")[-1]
            expected = next((cls for suffix, cls in self.NAME_CLASSES if name.endswith(suffix)), None)
            if expected is None or verdict is None:
                continue
            self.assertEqual(verdict, expected, token)
            checked += 1
        self.assertGreater(checked, 0)

    def test_e5_a_live_negation_removed_or_added_before_a_named_identifier_is_caught(self) -> None:
        self.first_trial("lean-theorem", r"\bother than (?=`)", "", "only after a `≠` or `¬`")
        removed, added = [], []
        for path, text, unit, entry in self.said_entries():
            if entry.cls != "lean-theorem":
                continue
            masked = TOOL.masked_text(entry.text)
            for a, b in TOOL.clauses(entry.text):
                cites = [t for t in TOOL.TOKEN.finditer(entry.text, a, b) if self.bound(entry, t.group(1))]
                if not cites:
                    continue
                statements = []
                for t in cites:
                    d = next(d for d in TOOL.qualified_definitions(self.index, t.group(1)) if d.kind in TOOL.THEOREM_KINDS)
                    statements.append(TOOL.lean_statement(self.index, ROOT, d).text)
                for t in TOOL.TOKEN.finditer(entry.text, a, cites[-1].start()):
                    kinds = TOOL.resolve(self.index, ROOT, t.group(1))[1] or set()
                    if self.bound(entry, t.group(1)) or not kinds & TOOL.LEAN_NAME_KINDS:
                        continue
                    window_start = max(a, t.start() - TOOL.NEGATOR_REACH)
                    negator = TOOL.NEGATOR_ANYWHERE.search(masked, window_start, t.start())
                    if negator:
                        removed.append((path, text, unit, entry, negator.start(), t.start(), ""))
                    elif not any(c in st for st in statements for c in "≠¬"):
                        added.append((path, text, unit, entry, t.start(), t.start(), "not "))
        self.assertTrue(removed)
        self.assertTrue(added)
        self.assertEqual(self.trials(removed), [])
        self.assertEqual(self.trials(added), [])

    def test_e5_f1_f2_f3_refuse_every_live_negation_family(self) -> None:
        self.first_trial("proved-contract", r"\btrue at\b", "not true at", "F1")
        # `not` before each leading phrase's verdict word: F1 where the rest
        # is still a phrase (`is not true at`, `not runs`); where it is not
        # (`is not UB`, `is not a no-op`), the citation has lost its own
        # verdict and is refused by E5 as ungoverned, or as governed by an
        # earlier phrase of the clause that does not say what it says.
        f1, unphrased, f1_never, f2, f3 = [], [], [], [], []
        for path, text, unit, entry in self.said_entries():
            for phrases, cites in self.events(entry):
                for start, end, kind, verdict, governed in phrases:
                    said = entry.text[start:end]
                    if kind != "leading":
                        continue
                    if said.startswith(("is ", "are ")):
                        at = start + said.index(" ") + 1
                        family = f1 if verdict in ("true", "false", "relation") else unphrased
                        if family is f1 or governed:
                            family.append((path, text, unit, entry, at, at, "not "))
                    else:
                        f1.append((path, text, unit, entry, start, start, "not "))
                    if verdict == "runs":
                        f1_never.append((path, text, unit, entry, start, start, "never "))
                    if entry.cls == "proved-contract" and verdict in self.FLIP:
                        for x, y, token in governed:
                            f2.append((path, text, unit, entry, y, y, f" ({self.FLIP[verdict]})"))
                for x, y, token in cites:
                    f3.append((path, text, unit, entry, x, x, "but not "))
        for family, needle in ((f1, "F1"), (unphrased, "[E5]"), (f1_never, "F1"), (f2, "F2"), (f3, "F3")):
            self.assertTrue(family, needle)
            self.assertEqual(self.trials(family, needle), [], needle)

    def test_e5_binds_live_laws_and_theorems_and_the_census_counts_them(self) -> None:
        passed = self.pass_line()
        self.assertIn("proved statements' verdicts stated as they say", passed)
        report = TOOL.run(ROOT, base_ref=None, index=self.index, snapshot=SNAPSHOT)
        self.assertEqual(report.findings, [])
        said = report.says
        self.assertGreater(said["laws"], 0)
        self.assertGreater(said["theorems"], 0)
        self.assertGreater(said["names_only"], 0)
        self.assertGreater(said["identifiers"], said["theorems"] + said["names_only"] - 1)
        self.assertEqual(TOOL.census(report)["statements_said"], said)
        self.assertIn(TOOL.said_line(report), passed)

    def pass_line(self) -> str:
        done = subprocess.run(
            [sys.executable, "-B", os.fspath(TOOL_PATH), "--root", os.fspath(ROOT), "--base-ref", "", "check"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        self.assertEqual(done.returncode, 0, done.stdout[-2000:])
        return done.stdout

if __name__ == "__main__":
    unittest.main()
