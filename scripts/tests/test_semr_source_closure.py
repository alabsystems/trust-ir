"""Source projection regressions; no compiler, publication service or credentials."""
import hashlib
import builtins
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

from scripts import check_semr_source_closure as closure


class ClosureTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for package in closure.PACKAGES:
            self.put(package + "/lean-toolchain", "leanprover/lean4:v4.30.0-rc2\n")
            self.put(package + "/lake-manifest.json", '{"packages": []}')
            self.put(package + "/lakefile.lean", "import Lake\n")
        self.put("lean/semr/lakefile.lean", "import Lake\nlean_lib SemR where\nlean_exe oracle where\n  root := `Main\n")
        self.put("lean/semr/SemR.lean", "import Init\n")
        self.put("lean/semr/Main.lean", "import SemR\n")
        self.put("lean/semr/FRAGMENT.tsv", "fixture\n")
        self.put("lean/semr/QUOTED_MODEL.tsv", "fixture\n")
        self.put("lean/semr/fixtures/input.bin", "bytes")
        self.put("lean/semr-memory/SemRFrameMemory.lean", "import SemR\n")
        self.put("lean/semr-memory/SemRFrameChecks.lean", "import SemRFrameMemory\n")
        self.put("lean/semr-memory/FrameAudit.lean", "import Lean\nimport SemRFrameChecks\n")
        self.put("lean/semr-memory/frame-audit-refusals.json", "{}")
        self.put("crates/probe/src/lib.rs", 'const B: &[u8] = include_bytes!("../../../lean/semr/fixtures/input.bin");\n')
        self.put("THIRD_PARTY.md", "fixture notices")
        self.put("NOTICE", "fixture notices")
        revision = "1" * 40
        self.put("lean/semr/MiniRust.lean", "-- from MiniRust " + revision + "\n")
        licenses = {}
        for name in ("MIT", "APACHE"):
            path = "LICENSES/MiniRust-" + name + ".txt"
            self.put(path, name)
            data = (self.root / path).read_bytes()
            licenses[path] = {"sha256": hashlib.sha256(data).hexdigest(),
                "git_blob_sha1": hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()}
        self.put("LICENSES/MiniRust.json", json.dumps({"schema": 1, "revision": revision,
            "translation": "lean/semr/MiniRust.lean", "translation_sha256": hashlib.sha256(
                (self.root / "lean/semr/MiniRust.lean").read_bytes()).hexdigest(), "license_files": licenses}))

    def put(self, path, text):
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(text)

    def problems(self, excluded=()):
        return closure.check(self.root, closure.files(self.root) - set(excluded))["problems"]

    def materialized_result(self, selected):
        with tempfile.TemporaryDirectory() as directory:
            projected = Path(directory).resolve()
            for path in sorted(selected):
                source, target = self.root / path, projected / path
                self.assertTrue(target.parent.resolve().is_relative_to(projected))
                target.parent.mkdir(parents=True, exist_ok=True)
                if source.is_symlink():
                    target.symlink_to(os.readlink(source), target_is_directory=source.is_dir())
                else:
                    target.write_bytes(source.read_bytes())
            return closure.check(projected, selected)

    def test_complete_input_tree(self):
        self.assertEqual(self.problems(), [])

    def test_missing_compile_time_fixture_is_reported(self):
        self.assertIn("missing source input: lean/semr/fixtures/input.bin",
                      self.problems(["lean/semr/fixtures/input.bin"]))

    def test_raw_literal_include_is_checked(self):
        self.put("crates/probe/src/lib.rs", 'const B: &[u8] = include_bytes!(r#"../../../lean/semr/fixtures/missing.bin"#);')
        self.assertIn("missing source input: lean/semr/fixtures/missing.bin", self.problems())

    def test_all_literal_include_delimiters_bind_selected_fixture(self):
        for macro in ("include", "include_str", "include_bytes"):
            for opening, closing in (("(", ")"), ("[", "]"), ("{", "}")):
                for literal in ('"../../../lean/semr/fixtures/input.bin"',
                                'r#"../../../lean/semr/fixtures/input.bin"#',
                                r'"../../../lean/\x73emr/fixtures/input.bin"'):
                    for comma in ("", ","):
                        with self.subTest(macro=macro, opening=opening,
                                          literal=literal, comma=comma):
                            self.put("crates/probe/src/lib.rs",
                                     macro + "! /* boundary */ " + opening +
                                     " /* argument */ " + literal + comma +
                                     " /* end */ " + closing + ";")
                            self.assertEqual(self.problems(), [])
                            self.assertIn("missing source input: lean/semr/fixtures/input.bin",
                                          self.problems(["lean/semr/fixtures/input.bin"]))

    def test_mismatched_include_delimiters_do_not_create_source_edges(self):
        pairs = {"(": ")", "[": "]", "{": "}"}
        for opening, expected in pairs.items():
            for closing in pairs.values():
                if closing == expected:
                    continue
                with self.subTest(opening=opening, closing=closing):
                    self.put("crates/probe/src/lib.rs", "include_bytes!" + opening +
                             '"../../../lean/semr/fixtures/missing.bin"' + closing + ";")
                    self.assertEqual(self.problems(), [])

    def test_cooked_literal_paths_are_decoded_before_semr_selection(self):
        literals = [r'"../../../lean/\x73emr/fixtures/input.bin"',
                    r'"../../../lean/se\u{6d}r/fixtures/input.bin"',
                    '"../../../lean/se\\\n  mr/fixtures/input.bin"']
        for literal in literals:
            with self.subTest(literal=literal):
                self.put("crates/probe/src/lib.rs", 'const B: &[u8] = include_bytes!(' + literal + ');')
                self.assertEqual(self.problems(), [])
                self.assertIn("missing source input: lean/semr/fixtures/input.bin",
                              self.problems(["lean/semr/fixtures/input.bin"]))

    def test_raw_or_escaped_backslash_paths_keep_literal_backslashes(self):
        for literal in (r'r"../../../lean/\x73emr/fixtures/missing.bin"',
                        r'"../../../lean/\\x73emr/fixtures/missing.bin"'):
            with self.subTest(literal=literal):
                self.put("crates/probe/src/lib.rs", 'const B: &[u8] = include_bytes!(' + literal + ');')
                self.assertEqual(self.problems(), [])

    def test_invalid_cooked_include_reports_its_source_path(self):
        self.put("crates/probe/src/lib.rs", r'const B: &[u8] = include_bytes!("../../../lean/\xGGemr/missing.bin");')
        problems = self.problems()
        self.assertTrue(any(p.startswith("invalid Rust literal include: crates/probe/src/lib.rs:")
                            for p in problems), problems)

    def test_vendored_toml_parser_supports_package_and_cli_imports(self):
        (self.root / 'lean/semr-memory/lakefile.lean').unlink()
        self.put('lean/semr-memory/lakefile.toml',
                 'name = "proofs"\n[[lean_lib]]\nname = "SemRFrameChecks"\n')
        original_import = builtins.__import__
        def no_stdlib(name, *args, **kwargs):
            if name == 'tomllib':
                raise ModuleNotFoundError('forced Python3.9 parser path', name=name)
            return original_import(name, *args, **kwargs)
        script_dir = str(Path(closure.__file__).parent)
        for name, backend in (('scripts.semr_fallback_control', 'scripts._vendor.tomli'),
                              ('semr_fallback_cli_control', '_vendor.tomli')):
            with self.subTest(module=name):
                spec = importlib.util.spec_from_file_location(name, closure.__file__)
                module = importlib.util.module_from_spec(spec)
                search_path = ([p for p in sys.path if p != script_dir]
                               if name.startswith('scripts.') else [script_dir, *sys.path])
                with mock.patch.object(sys, 'path', search_path), \
                        mock.patch.object(builtins, '__import__', side_effect=no_stdlib):
                    spec.loader.exec_module(module)
                self.assertEqual(module.tomllib.__name__, backend)
                self.assertEqual(module.check(self.root, module.files(self.root))['problems'], [])

    def test_examples_in_comments_and_strings_are_not_includes(self):
        self.put("crates/probe/src/lib.rs", '// include_bytes!("../../../lean/semr/missing.bin")\n'
                 '/* include!["../../../lean/semr/missing.rs"] */\n'
                 'const S: &str = r#"include_str!{"../../../lean/semr/missing.lean"}"#;')
        self.assertEqual(self.problems(), [])

    def test_missing_import_is_reported(self):
        self.assertTrue(any("missing Lean import:" in p for p in
                            self.problems(["lean/semr-memory/SemRFrameMemory.lean"])))

    def test_unimported_declared_library_root_is_required(self):
        self.put("lean/semr/lakefile.lean", "import Lake\nlean_lib Optional where\n")
        self.assertIn("missing source input: lean/semr/Optional.lean", self.problems())

    def test_bare_library_and_executable_roots_are_required(self):
        self.put("lean/semr/Optional.lean", "import Init\n")
        for kind in ("lean_lib", "lean_exe"):
            with self.subTest(kind=kind):
                self.put("lean/semr/lakefile.lean", "import Lake\n" + kind + " Optional\n")
                self.assertEqual(self.problems(), [])
                self.assertIn("missing source input: lean/semr/Optional.lean",
                              self.problems(["lean/semr/Optional.lean"]))

    def test_crlf_bare_targets_keep_their_default_roots(self):
        self.put("lean/semr/Optional.lean", "import Init\r\n")
        for kind in ("lean_lib", "lean_exe"):
            with self.subTest(kind=kind):
                self.put("lean/semr/lakefile.lean", "import Lake\r\n" + kind + " Optional\r\n")
                self.assertEqual(self.problems(), [])
                self.assertIn("missing source input: lean/semr/Optional.lean",
                              self.problems(["lean/semr/Optional.lean"]))

    def test_bare_target_does_not_borrow_later_root_or_directory_fields(self):
        self.put("lean/semr/Optional.lean", "import Init\n")
        self.put("lean/semr/lakefile.lean", "import Lake\nlean_lib Optional\n"
                 "def root := `Main\ndef srcDir := \"absent\"\n"
                 "lean_exe oracle where\n  root := `Main\n")
        self.assertEqual(self.problems(), [])
        self.assertIn("missing source input: lean/semr/Optional.lean",
                      self.problems(["lean/semr/Optional.lean"]))

    def test_bare_target_separates_configured_target_bodies(self):
        self.put("lean/semr/Optional.lean", "import Init\n")
        self.put("lean/semr/lakefile.lean", "import Lake\n"
                 "lean_lib First where\n  roots := #[`SemR]\n"
                 "lean_lib Optional -- uses its default root\n"
                 "lean_exe oracle where\n  root := `Main\n")
        self.assertEqual(self.problems(), [])
        self.assertIn("missing source input: lean/semr/Optional.lean",
                      self.problems(["lean/semr/Optional.lean"]))

    def test_commented_bare_targets_do_not_require_roots(self):
        self.put("lean/semr/lakefile.lean", "import Lake\n-- lean_lib Absent\n"
                 "/- outer\n/- nested -/\nlean_exe Absent\n-/\n")
        self.assertEqual(self.problems(), [])

    def test_literal_and_escaped_name_examples_do_not_declare_targets(self):
        for example in ('"example\nlean_lib Absent where\n"',
                        'r#"example\nlean_exe Absent where\n"#',
                        '«example\nlean_lib Absent where\n»'):
            with self.subTest(example=example):
                self.put("lean/semr/lakefile.lean", "import Lake\ndef example := " + example + "\n")
                self.assertEqual(self.problems(), [])

    def test_literal_field_examples_cannot_replace_default_root(self):
        self.put("lean/semr/Optional.lean", "import Init\n")
        self.put("lean/semr/lakefile.lean", "import Lake\nlean_lib Optional where\n"
                 '  moreLeanArgs := #["root := `Absent", "srcDir := \\"absent\\""]\n')
        self.assertEqual(self.problems(), [])
        self.assertIn("missing source input: lean/semr/Optional.lean",
                      self.problems(["lean/semr/Optional.lean"]))

    def test_literal_source_directories_preserve_comment_markers(self):
        for directory in ("source--tree", "source/-tree"):
            with self.subTest(directory=directory):
                path = "lean/semr/" + directory + "/Optional.lean"
                self.put(path, "import Init\n")
                self.put("lean/semr/lakefile.lean", "import Lake\nlean_lib Optional where\n"
                         '  srcDir := "' + directory + '"\n')
                self.assertEqual(self.problems(), [])
                self.assertIn("missing source input: " + path, self.problems([path]))

    def test_adjacent_next_line_where_keeps_the_explicit_root(self):
        self.put("lean/semr/lakefile.lean", "import Lake\nlean_exe oracle\n"
                 "/- configuration comment -/\nwhere\n  root := `Main\n")
        self.assertEqual(self.problems(), [])

    def test_multiline_target_names_keep_bare_and_where_forms(self):
        self.put("lean/semr/Optional.lean", "import Init\n")
        for kind, field in (("lean_lib", "roots := #[`Optional]"),
                            ("lean_exe", "root := `Optional")):
            for gap in ("\n  ", " /- across\n lines -/ "):
                for config in ("\n", " where\n  " + field + "\n"):
                    with self.subTest(kind=kind, gap=gap, config=config):
                        self.put("lean/semr/lakefile.lean", "import Lake\n" +
                                 kind + gap + "Optional" + config)
                        self.assertEqual(self.problems(), [])
                        self.assertIn("missing source input: lean/semr/Optional.lean",
                                      self.problems(["lean/semr/Optional.lean"]))

    def test_unsupported_target_configs_cannot_silently_skip_roots(self):
        for declaration in ('lean_lib Optional { roots := #[`Absent] }',
                            'lean_lib "Optional"',
                            'lean_lib Optional where\n  srcDir := anotherDirectory',
                            r'lean_lib Optional where' + '\n  srcDir := "source\\x2dname"'):
            with self.subTest(declaration=declaration):
                self.put("lean/semr/lakefile.lean", "import Lake\n" + declaration + "\n")
                self.assertTrue(any(p.startswith("unsupported Lean ") for p in self.problems()))

    def test_toml_target_root_is_required(self):
        (self.root / "lean/semr-memory/lakefile.lean").unlink()
        self.put("lean/semr-memory/lakefile.toml", 'name = "proofs"\n[[lean_lib]]\nname = "Absent"\n')
        self.assertIn("missing source input: lean/semr-memory/Absent.lean", self.problems())

    def test_local_dependency_cannot_escape_projection(self):
        self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
            "type": "path", "dir": "../../../outside", "configFile": "lakefile.lean"}]}))
        self.assertTrue(any("escaping Lean dependency:" in p for p in self.problems()))

    def test_absolute_dependency_directory_cannot_bind_a_relative_decoy(self):
        self.put("lean/semr-memory/outside/lakefile.lean", "import Lake\n")
        for directory in ("/outside", "//outside", "/"):
            with self.subTest(directory=directory):
                self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
                    "type": "path", "dir": directory, "configFile": "lakefile.lean"}]}))
                self.assertTrue(any(p.startswith("escaping Lean dependency:") for p in self.problems()))

    def test_dependency_configuration_cannot_reset_or_escape_its_base(self):
        for config in ("/lakefile.lean", "../../../outside/lakefile.lean"):
            with self.subTest(config=config):
                self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
                    "type": "path", "dir": "../semr", "configFile": config}]}))
                self.assertTrue(any(p.startswith("escaping Lean dependency") for p in self.problems()))

    def test_dependency_stages_reject_exact_parent_roots(self):
        for directory, config in (("../../..", "lakefile.lean"), ("../semr", "../../..")):
            with self.subTest(directory=directory, config=config):
                self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
                    "type": "path", "dir": directory, "configFile": config}]}))
                self.assertTrue(any(p.startswith("escaping Lean dependency") for p in self.problems()))

    def test_dependency_normalization_preserves_physical_path_identity(self):
        with tempfile.TemporaryDirectory() as outside:
            for target in (self.root / "different-package", Path(outside)):
                (target / "child").mkdir(parents=True)
                (target / "lakefile.lean").write_text("import Lake\n")
                link = self.root / "lean/semr/link"
                link.symlink_to(target / "child", target_is_directory=True)
                try:
                    for directory, config in (("../semr/link/..", "lakefile.lean"),
                                              ("../semr", "link/../lakefile.lean")):
                        with self.subTest(target=target, directory=directory, config=config):
                            self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
                                "type": "path", "dir": directory, "configFile": config}]}))
                            self.assertTrue(any((p.startswith("escaping source input:") or
                                                 p.startswith("source path normalization changes resolution:"))
                                                and "link/.." in p for p in self.problems()))
                finally:
                    link.unlink()

    def test_relative_dependency_configuration_uses_canonical_selected_paths(self):
        self.put("lean/semr/sub/unused.txt", "directory exists")
        path = "lean/semr-memory/lake-manifest.json"
        for directory, config in (("../semr", "./lakefile.lean"),
                                  ("../semr/.", "sub/../lakefile.lean"),
                                  ("../semr/sub/..", "././lakefile.lean")):
            with self.subTest(directory=directory, config=config):
                self.put(path, json.dumps({"packages": [{"type": "path", "dir": directory,
                                                        "configFile": config}]}))
                result = closure.check(self.root, closure.files(self.root))
                self.assertEqual(result["problems"], [])
                self.assertIn([path, "lean/semr/lakefile.lean"], result["edges"])
                self.assertIn("missing source input: lean/semr/lakefile.lean",
                              self.problems(["lean/semr/lakefile.lean"]))

    def test_normalization_does_not_hide_missing_intermediate_directories(self):
        self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
            "type": "path", "dir": "../semr", "configFile": "absent/../lakefile.lean"}]}))
        self.assertTrue(any(p.startswith("missing source input:") and
                            "absent/../lakefile.lean" in p for p in self.problems()))
        self.put("lean/semr-memory/lake-manifest.json", '{"packages": []}')
        self.fixture_manifest("absent/../input.bin")
        self.assertTrue(any(p.startswith("missing source input:") and
                            "absent/../input.bin" in p for p in self.problems()))

    def test_internal_file_symlinks_preserve_source_spelling_identity(self):
        (self.root / "lean/semr/same-config.lean").symlink_to("lakefile.lean")
        self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
            "type": "path", "dir": "../semr", "configFile": "./same-config.lean"}]}))
        (self.root / "lean/semr/fixtures/alias.bin").symlink_to("input.bin")
        self.fixture_manifest("./alias.bin")
        result = closure.check(self.root, closure.files(self.root))
        self.assertEqual(result["problems"], [])
        self.assertIn(["lean/semr-memory/lake-manifest.json", "lean/semr/same-config.lean"], result["edges"])
        self.assertIn(["lean/semr/fixtures/model/MANIFEST.json", "lean/semr/fixtures/alias.bin"], result["edges"])

    def test_intermediate_directories_must_survive_selected_materialization(self):
        for family in ("dependency", "fixture"):
            with self.subTest(family=family):
                self.put("lean/semr-memory/lake-manifest.json", '{"packages": []}')
                if family == "dependency":
                    marker = "lean/semr/sub/unused.txt"
                    self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
                        "type": "path", "dir": "../semr", "configFile": "sub/../lakefile.lean"}]}))
                else:
                    marker = "lean/semr/fixtures/sub/unused.txt"
                    self.fixture_manifest("sub/../input.bin")
                self.put(marker, "creates the directory")
                selected = closure.files(self.root)
                self.assertEqual(closure.check(self.root, selected)["problems"], [])
                self.assertEqual(self.materialized_result(selected)["problems"], [])
                selected.remove(marker)
                self.assertTrue(self.materialized_result(selected)["problems"])
                self.assertTrue(closure.check(self.root, selected)["problems"])

    def test_file_symlink_targets_and_hops_must_survive_selection(self):
        self.put("lean/semr/actual-target.lean", "import Lake\n")
        (self.root / "lean/semr/hop.lean").symlink_to("actual-target.lean")
        (self.root / "lean/semr/alias.lean").symlink_to("hop.lean")
        self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
            "type": "path", "dir": "../semr", "configFile": "alias.lean"}]}))
        full = closure.files(self.root)
        self.assertEqual(closure.check(self.root, full)["problems"], [])
        self.assertEqual(self.materialized_result(full)["problems"], [])
        for excluded in ("lean/semr/hop.lean", "lean/semr/actual-target.lean"):
            with self.subTest(excluded=excluded):
                selected = full - {excluded}
                self.assertTrue(self.materialized_result(selected)["problems"])
                self.assertTrue(closure.check(self.root, selected)["problems"])

    def test_symlink_target_directory_spellings_must_survive_selection(self):
        self.put("lean/semr/missing/marker.txt", "directory exists")
        self.put("lean/semr/actual-target.lean", "import Lake\n")
        (self.root / "lean/semr/alias.lean").symlink_to("missing/../actual-target.lean")
        self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
            "type": "path", "dir": "../semr", "configFile": "alias.lean"}]}))
        full = closure.files(self.root)
        self.assertEqual(self.materialized_result(full)["problems"], [])
        selected = full - {"lean/semr/missing/marker.txt"}
        self.assertTrue(self.materialized_result(selected)["problems"])
        self.assertTrue(closure.check(self.root, selected)["problems"])

    def test_absolute_internal_file_links_cannot_survive_relocation(self):
        self.put("lean/semr/actual-target.lean", "import Lake\n")
        (self.root / "lean/semr/alias.lean").symlink_to(self.root / "lean/semr/actual-target.lean")
        selected = closure.files(self.root)
        self.assertTrue(self.materialized_result(selected)["problems"])
        self.assertTrue(closure.check(self.root, selected)["problems"])

    def test_regular_files_cannot_be_traversed_as_directories(self):
        for family, name in (("dependency", "lakefile.lean"), ("fixture", "input.bin")):
            for suffix in ("/.", "/"):
                with self.subTest(family=family, suffix=suffix):
                    self.put("lean/semr-memory/lake-manifest.json", '{"packages": []}')
                    if family == "dependency":
                        raw = "lean/semr/" + name + suffix
                        self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
                            "type": "path", "dir": "../semr", "configFile": name + suffix}]}))
                    else:
                        raw = "lean/semr/fixtures/" + name + suffix
                        self.fixture_manifest(name + suffix)
                    self.assertFalse(os.path.isfile(os.fspath(self.root) + "/" + raw))
                    self.assertTrue(self.problems())

    def test_repeated_acyclic_directory_links_keep_their_prerequisites(self):
        self.put("lean/semr/sub/marker.txt", "directory exists")
        (self.root / "lean/semr/alias").symlink_to("sub", target_is_directory=True)
        self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
            "type": "path", "dir": "../semr", "configFile": "alias/../alias/../lakefile.lean"}]}))
        full = closure.files(self.root)
        self.assertIn("lean/semr/alias", full)
        self.assertEqual(closure.check(self.root, full)["problems"], [])
        self.assertEqual(self.materialized_result(full)["problems"], [])
        for excluded in ("lean/semr/alias", "lean/semr/sub/marker.txt"):
            with self.subTest(excluded=excluded):
                selected = full - {excluded}
                self.assertTrue(self.materialized_result(selected)["problems"])
                self.assertTrue(closure.check(self.root, selected)["problems"])

    def test_cyclic_file_links_refuse_without_looping(self):
        (self.root / "lean/semr/first.lean").symlink_to("second.lean")
        (self.root / "lean/semr/second.lean").symlink_to("first.lean")
        self.assertTrue(self.problems())

    def test_absolute_dependency_inputs_cannot_resolve_to_local_files(self):
        self.put("lean/semr-memory/outside/lakefile.lean", "import Lake\n")
        for directory, config_file, escaped in (("/outside", "lakefile.lean", "/outside"),
                                                (".", "/outside/lakefile.lean", "/outside/lakefile.lean")):
            with self.subTest(directory=directory, config_file=config_file):
                self.put("lean/semr-memory/lake-manifest.json", json.dumps({"packages": [{
                    "type": "path", "dir": directory, "configFile": config_file}]}))
                self.assertIn("escaping Lean dependency: " + escaped, self.problems())

    def test_json_inputs_require_objects_and_report_their_paths(self):
        self.fixture_manifest()
        inputs = [(package + "/lake-manifest.json", "Lean dependency manifest")
                  for package in closure.PACKAGES]
        inputs += [("lean/semr/fixtures/model/MANIFEST.json", "SemR fixture manifest"),
                   ("LICENSES/MiniRust.json", "MiniRust provenance")]
        for path, label in inputs:
            file = self.root / path
            original = file.read_bytes()
            try:
                for payload in (b"", b"not JSON", b"\xff", b"[]", b"null", b"false", b'"text"'):
                    with self.subTest(path=path, payload=payload):
                        file.write_bytes(payload)
                        self.assertTrue(any(p.startswith("invalid " + label + " JSON:")
                                            and path in p for p in self.problems()))
            finally:
                file.write_bytes(original)

    def test_present_dependency_packages_must_be_an_array(self):
        path = "lean/semr-memory/lake-manifest.json"
        for packages in ({}, "", None, False, 0):
            with self.subTest(packages=packages):
                self.put(path, json.dumps({"packages": packages}))
                self.assertTrue(any(path in p for p in self.problems()))
        for record in ({}, {"packages": []}):
            with self.subTest(valid_record=record):
                self.put(path, json.dumps(record))
                self.assertEqual(self.problems(), [])

    def test_dependency_rows_require_path_strings(self):
        path = "lean/semr-memory/lake-manifest.json"
        rows = [None, "dependency", False, 1,
                {"type": "path", "configFile": "lakefile.lean"},
                {"type": "path", "dir": [], "configFile": "lakefile.lean"},
                {"type": "path", "dir": "../semr", "configFile": False}]
        for row in rows:
            with self.subTest(row=row):
                self.put(path, json.dumps({"packages": [row]}))
                self.assertTrue(any(path in p for p in self.problems()))
        self.put(path, json.dumps({"packages": [{"type": "path", "dir": "../semr",
                                                "configFile": "lakefile.lean"}]}))
        result = closure.check(self.root, closure.files(self.root))
        self.assertEqual(result["problems"], [])
        self.assertIn([path, "lean/semr/lakefile.lean"], result["edges"])

    def test_invalid_manifest_does_not_hide_other_missing_inputs(self):
        self.put("lean/semr-memory/lake-manifest.json", "")
        self.assertIn("missing source input: lean/semr/fixtures/input.bin",
                      self.problems(["lean/semr/fixtures/input.bin"]))

    def test_cli_retains_a_structured_report_for_invalid_json(self):
        path = "lean/semr-memory/lake-manifest.json"
        self.put(path, "")
        self.fixture_manifest()
        self.put("lean/semr/fixtures/model/MANIFEST.json", "not JSON")
        report = self.root / "closure-result.json"
        result = subprocess.run([sys.executable, "-B", str(Path(closure.__file__).resolve()),
                                 "--tree", str(self.root), "--output", str(report)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 1, result.stderr)
        problems = json.loads(report.read_text())["problems"]
        self.assertTrue(any(path in p for p in problems))
        self.assertTrue(any("fixtures/model/MANIFEST.json" in p for p in problems))

    def test_changed_license_and_translation_are_reported(self):
        self.put("LICENSES/MiniRust-MIT.txt", "changed")
        self.put("lean/semr/MiniRust.lean", "changed")
        problems = self.problems()
        self.assertIn("upstream license bytes changed: LICENSES/MiniRust-MIT.txt", problems)
        self.assertIn("MiniRust translation identity changed", problems)
        self.assertIn("MiniRust revision marker disagrees with provenance", problems)

    def test_empty_translation_cannot_skip_identity_or_revision_checks(self):
        self.put("lean/semr/MiniRust.lean", "")
        problems = self.problems()
        self.assertIn("MiniRust translation identity changed", problems)
        self.assertIn("MiniRust revision marker disagrees with provenance", problems)
        provenance = self.root / "LICENSES/MiniRust.json"
        record = json.loads(provenance.read_text())
        record["translation_sha256"] = hashlib.sha256(b"").hexdigest()
        provenance.write_text(json.dumps(record))
        self.assertIn("MiniRust revision marker disagrees with provenance", self.problems())

    def test_invalid_provenance_json_is_reported(self):
        for payload in (b"", b"not JSON", b"\xff"):
            with self.subTest(payload=payload):
                (self.root / "LICENSES/MiniRust.json").write_bytes(payload)
                self.assertTrue(any(p.startswith("invalid MiniRust provenance JSON:")
                                    for p in self.problems()))

    def test_provenance_field_types_are_checked_before_use(self):
        file = self.root / "LICENSES/MiniRust.json"
        original = json.loads(file.read_text())
        changes = [{"schema": True}, {"translation": []}, {"translation_sha256": None},
                   {"revision": 1}, {"license_files": []},
                   {"license_files": {"LICENSES/MiniRust-MIT.txt": None}},
                   {"license_files": {"LICENSES/MiniRust-MIT.txt": {"sha256": False}}}]
        for change in changes:
            with self.subTest(change=change):
                file.write_text(json.dumps({**original, **change}))
                self.assertTrue(any("LICENSES/MiniRust.json" in p for p in self.problems()))

    def test_escaping_fixture_symlink_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            outside = Path(directory) / "outside.bin"
            outside.write_bytes(b"outside")
            file = self.root / "lean/semr/fixtures/input.bin"
            file.unlink()
            file.symlink_to(outside)
            self.assertIn("escaping source input: lean/semr/fixtures/input.bin", self.problems())

    def fixture_manifest(self, file="input.bin"):
        self.put("lean/semr/fixtures/model/MANIFEST.json", json.dumps({
            "schema": "trust.generic-scalar-model-fixtures.v1", "fixtures": [{
                "file": file, "bytes": 5, "sha256": hashlib.sha256(b"bytes").hexdigest()}]}))

    def test_fixture_manifest_binds_actual_bytes(self):
        self.fixture_manifest()
        self.assertEqual(self.problems(), [])
        self.put("lean/semr/fixtures/input.bin", "other")
        self.assertIn("SemR fixture bytes changed: lean/semr/fixtures/input.bin", self.problems())

    def test_fixture_collections_and_rows_are_typed(self):
        self.fixture_manifest()
        path = "lean/semr/fixtures/model/MANIFEST.json"
        file = self.root / path
        table = json.loads(file.read_text())
        for fixtures in ({"file": "input.bin"}, "fixture", [None], ["fixture"], [False], [{}]):
            with self.subTest(fixtures=fixtures):
                file.write_text(json.dumps({**table, "fixtures": fixtures}))
                self.assertTrue(any(path in p for p in self.problems()))

    def test_fixture_byte_counts_do_not_coerce_boolean_or_float(self):
        for count, payload in ((True, b"x"), (5.0, b"bytes")):
            with self.subTest(count=count):
                self.fixture_manifest()
                (self.root / "lean/semr/fixtures/input.bin").write_bytes(payload)
                file = self.root / "lean/semr/fixtures/model/MANIFEST.json"
                table = json.loads(file.read_text())
                table["fixtures"][0].update(bytes=count, sha256=hashlib.sha256(payload).hexdigest())
                file.write_text(json.dumps(table))
                self.assertTrue(self.problems())

    def test_empty_fixture_with_integer_count_and_digest_is_valid(self):
        self.fixture_manifest()
        (self.root / "lean/semr/fixtures/input.bin").write_bytes(b"")
        file = self.root / "lean/semr/fixtures/model/MANIFEST.json"
        table = json.loads(file.read_text())
        table["fixtures"][0].update(bytes=0, sha256=hashlib.sha256(b"").hexdigest())
        file.write_text(json.dumps(table))
        self.assertEqual(self.problems(), [])

    def test_fixture_manifest_cannot_escape_its_source_area(self):
        self.fixture_manifest("../../../NOTICE")
        self.assertTrue(any("escaping SemR fixture:" in p for p in self.problems()))

    def test_absolute_fixture_paths_cannot_bind_relative_decoys(self):
        for path in ("/input.bin", "//input.bin"):
            with self.subTest(path=path):
                self.fixture_manifest(path)
                self.assertTrue(any(p.startswith("escaping SemR fixture:") for p in self.problems()))

    def test_relative_fixture_aliases_keep_canonical_identity(self):
        self.put("lean/semr/fixtures/sub/unused.txt", "directory exists")
        for path in ("./input.bin", "sub/../input.bin", "../fixtures/input.bin"):
            with self.subTest(path=path):
                self.fixture_manifest(path)
                result = closure.check(self.root, closure.files(self.root))
                self.assertEqual(result["problems"], [])
                self.assertIn(["lean/semr/fixtures/model/MANIFEST.json",
                               "lean/semr/fixtures/input.bin"], result["edges"])
                self.assertIn("missing source input: lean/semr/fixtures/input.bin",
                              self.problems(["lean/semr/fixtures/input.bin"]))

    def test_fixture_normalization_preserves_physical_path_identity(self):
        with tempfile.TemporaryDirectory() as outside:
            for target in (self.root / "different-fixtures", Path(outside)):
                with self.subTest(target=target):
                    (target / "child").mkdir(parents=True)
                    (target / "input.bin").write_bytes(b"bytes")
                    link = self.root / "lean/semr/fixtures/link"
                    link.symlink_to(target / "child", target_is_directory=True)
                    try:
                        self.fixture_manifest("link/../input.bin")
                        self.assertTrue(any((p.startswith("escaping source input:") or
                                             p.startswith("source path normalization changes resolution:"))
                                            and "link/.." in p for p in self.problems()))
                    finally:
                        link.unlink()

    def test_exclude_only_manifest_is_refused(self):
        manifest = self.root / "manifest.txt"
        manifest.write_text("!private/\n")
        with self.assertRaises(ValueError):
            closure.manifest_selection(self.root, manifest)

    def test_old_allowlist_omission_and_fixed_directory_selection(self):
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        manifest = self.root / "manifest.txt"
        manifest.write_text("crates/\nlean/trust_ir-semantics/\nLICENSES/\nNOTICE\nTHIRD_PARTY.md\n")
        self.assertTrue(closure.check(self.root, closure.manifest_selection(self.root, manifest))["problems"])
        manifest.write_text(manifest.read_text() + "lean/semr/\nlean/semr-memory/\n")
        self.assertEqual(closure.check(self.root, closure.manifest_selection(self.root, manifest))["problems"], [])


class RepositoryRegression(unittest.TestCase):
    def test_snapshot_or_source_policy_contains_semr_inputs(self):
        root = Path(__file__).resolve().parents[2]
        manifest = root / "publish/manifest.txt"
        selected = closure.manifest_selection(root, manifest) if manifest.exists() else closure.files(root)
        self.assertEqual(closure.check(root, selected)["problems"], [])


if __name__ == "__main__":
    unittest.main()
