"""Guards for the registry-backed gates of scripts/ci_gates.sh (scripts/gates/*.tests).

A registry line that names no test target would make its gate fail at run time; a missing
`merge=union` declaration would bring back the merge conflicts the registries exist to remove;
and an inline `--test` list reappearing in ci_gates.sh for a registry-backed gate would silently
split one gate's population across two places.
"""

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GATES = ROOT / "scripts" / "gates"
REGISTRY = re.compile(r"^(?P<gate>[a-z0-9-]+)\.(?P<crate>[a-z0-9-]+)\.tests$")


def declared_test_targets(crate_dir: Path) -> dict[str, Path]:
    """The crate's explicit `[[test]]` targets (name -> source path).

    A target declared with its own `path` (the two-language ratchets live
    under tests/two_language/) is as real as an auto-discovered
    tests/<name>.rs; the source file it names must exist.
    """
    manifest = crate_dir / "Cargo.toml"
    if not manifest.is_file():
        return {}
    # A minimal reader of `[[test]]` tables (`name = "..."`, `path = "..."`):
    # the interpreter this runs under may predate tomllib.
    out: dict[str, Path] = {}
    current = None
    for raw in manifest.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if line.startswith("["):
            if current and current.get("name"):
                out[current["name"]] = crate_dir / current.get(
                    "path", f"tests/{current['name']}.rs"
                )
            current = {} if line == "[[test]]" else None
            continue
        m = re.match(r'^(name|path)\s*=\s*"([^"]*)"$', line)
        if current is not None and m:
            current[m.group(1)] = m.group(2)
    if current and current.get("name"):
        out[current["name"]] = crate_dir / current.get("path", f"tests/{current['name']}.rs")
    return out


def excluded_packages(root: Path = ROOT) -> list[str]:
    """The root manifest's workspace `exclude` list: packages no `--workspace`
    gate compiles, which a registry names by directory (`frontend`)."""
    text = (root / "Cargo.toml").read_text(encoding="utf-8")
    block = re.search(r"(?m)^exclude\s*=\s*\[(.*?)\]", text, re.S)
    return re.findall(r'"([^"]+)"', block.group(1)) if block else []


def registry_package(crate: str) -> tuple[Path, bool]:
    """The package directory a registry's `<crate>` part names, and whether it
    is workspace-EXCLUDED: `crates/<crate>` for a member, else `<crate>/` when
    the root manifest excludes it (its gate runs it by `--manifest-path`)."""
    member = ROOT / "crates" / crate
    if member.is_dir():
        return member, False
    if crate in excluded_packages():
        return ROOT / crate, True
    return member, False


def entries(path: Path) -> list[str]:
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        name = line.split("#", 1)[0].strip()
        if name:
            out.append(name)
    return out


class GateRegistryTests(unittest.TestCase):
    def registries(self) -> list[Path]:
        found = sorted(GATES.glob("*.tests"))
        self.assertTrue(found, "no gate registries under scripts/gates")
        return found

    def test_every_registry_names_existing_test_targets(self) -> None:
        for path in self.registries():
            m = REGISTRY.match(path.name)
            self.assertIsNotNone(m, f"{path.name}: expected <gate>.<crate>.tests")
            crate_dir, _ = registry_package(m["crate"])
            crate_tests = crate_dir / "tests"
            declared = declared_test_targets(crate_dir)
            names = entries(path)
            self.assertTrue(names, f"{path.name} lists no tests")
            self.assertEqual(len(names), len(set(names)), f"{path.name} lists a test twice")
            for name in names:
                self.assertRegex(name, r"^[A-Za-z0-9_]+$", f"{path.name}: bad target {name!r}")
                target = crate_tests / f"{name}.rs"
                target_dir = crate_tests / name / "main.rs"
                explicit = declared.get(name)
                self.assertTrue(
                    target.is_file()
                    or target_dir.is_file()
                    or (explicit is not None and explicit.is_file()),
                    f"{path.name}: no test target {name} in {crate_tests.relative_to(ROOT)}",
                )

    def test_registry_gates_are_wired_and_not_duplicated_inline(self) -> None:
        gates = (ROOT / "scripts" / "ci_gates.sh").read_text(encoding="utf-8")
        for path in self.registries():
            m = REGISTRY.match(path.name)
            gate = m["gate"]
            _, excluded = registry_package(m["crate"])
            if excluded:
                # A workspace-excluded package is run by its manifest path,
                # one gate call per (gate, package).
                self.assertIn(
                    f"gate {gate} run_excluded_registry {gate} {m['crate']}\n",
                    gates,
                    f"{gate} registry of the excluded package {m['crate']} is not run",
                )
            else:
                self.assertIn(f"run_registry {gate}", gates, f"{gate} registry is not run")
            for name in entries(path):
                self.assertNotIn(
                    f"--test {name} ",
                    gates.replace("\\\n", " "),
                    f"{name} is listed inline in ci_gates.sh as well as in {path.name}",
                )

    def test_declared_targets_are_read_with_their_paths(self) -> None:
        import tempfile

        with tempfile.TemporaryDirectory() as tmp:
            crate = Path(tmp)
            (crate / "Cargo.toml").write_text(
                '[package]\nname = "x"\n\n[[test]]\nname = "a"\npath = "tests/sub/a.rs"\n\n'
                '[dependencies]\nname = "not-a-test"\n\n[[test]]\nname = "b"\n',
                encoding="utf-8",
            )
            declared = declared_test_targets(crate)
            self.assertEqual(
                declared,
                {"a": crate / "tests/sub/a.rs", "b": crate / "tests/b.rs"},
            )
            # The live registries: every explicitly declared target a registry
            # names must point at a real source file (a declared-but-missing
            # path is not a target).
            self.assertFalse(declared["a"].is_file())

    def test_an_excluded_package_registry_names_its_own_directory(self) -> None:
        # `frontend/` is excluded from the workspace (no `--workspace` gate
        # compiles it), so its registry resolves to `frontend/`, never to a
        # `crates/frontend` that does not exist, and is run by manifest path.
        self.assertIn("frontend", excluded_packages())
        self.assertEqual(registry_package("frontend"), (ROOT / "frontend", True))
        self.assertEqual(
            registry_package("trust-ir-build"), (ROOT / "crates" / "trust-ir-build", False)
        )
        gates = (ROOT / "scripts" / "ci_gates.sh").read_text(encoding="utf-8")
        self.assertIn('--manifest-path "$ROOT/$package/Cargo.toml"', gates)

    def test_registries_and_changelog_merge_by_union(self) -> None:
        attrs = (ROOT / ".gitattributes").read_text(encoding="utf-8").split()
        text = " ".join(attrs)
        self.assertIn("scripts/gates/*.tests merge=union", text)
        self.assertIn("CHANGELOG.md merge=union", text)


if __name__ == "__main__":
    unittest.main()
