#!/usr/bin/env python3
"""Hostile source custody controls for the logical/runtime boundary inventory."""
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[2]
GUARD = REPO / "scripts/check_lean_runtime_boundary.py"
spec = importlib.util.spec_from_file_location("runtime_boundary", GUARD)
boundary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(boundary)


class RuntimeBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="runtime-boundary-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.producer = self.root / boundary.PRODUCER
        shutil.copytree(REPO / boundary.PRODUCER, self.producer,
                        ignore=shutil.ignore_patterns(".lake", "__pycache__"))
        (self.root / "scripts").mkdir()
        shutil.copy2(GUARD, self.root / "scripts/check_lean_runtime_boundary.py")
        for relative in boundary.CALLER_INPUTS:
            destination = self.root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(REPO / relative, destination)

    def ledger(self, change):
        path = self.root / boundary.LEDGER
        data = json.loads(path.read_text())
        change(data)
        path.write_text(json.dumps(data))

    def refused(self, text):
        with self.assertRaisesRegex(boundary.BoundaryError, text):
            boundary.inspect(self.root)

    def test_untraced_native_header_refuses(self):
        path = self.producer / "lakefile.lean"
        path.write_text(path.read_text().replace('nativeFacets := trustIrNativeObjects', 'nativeFacets := fun _ => #[]', 1))
        self.refused("native objects require their header dependency")

    def test_native_header_trace_cannot_be_discarded(self):
        path = self.producer / "lakefile.lean"
        original = path.read_text()
        self.assertIn("source.zipWith (fun path _ => path) header", original)
        path.write_text(original.replace("source.zipWith (fun path _ => path) header", "source.add header"))
        self.refused("native object job expansion changed")

    def test_native_foundation_inventory_cannot_omit_a_dependency(self):
        self.ledger(lambda d: d["native_foundation_modules_lean430"].pop())
        self.refused("native foundations differ from the provider import closure")

    def test_native_foundation_roster_cannot_omit_new_import(self):
        path = self.producer / "lakefile.lean"
        original = path.read_text()
        self.assertIn("`TrustIr.StringCompat", original)
        path.write_text(original.replace(",\n    `TrustIr.StringCompat", "", 1))
        self.refused("native foundation ownership differs from the provider import closure")

    def test_native_foundation_roster_cannot_duplicate_module(self):
        path = self.producer / "lakefile.lean"
        original = path.read_text()
        path.write_text(original.replace("`TrustIr.StringCompat]",
            "`TrustIr.StringCompat, `TrustIr.StringCompat]", 1))
        self.refused("native foundation ownership differs from the provider import closure")

    def test_native_foundation_ownership_cannot_be_dropped(self):
        path = self.producer / "lakefile.lean"
        path.write_text(path.read_text().replace("  roots := trustIrProviderRoots\n", ""))
        self.refused("native provider requires its reviewed foundation ownership")

    def test_native_export_prototype_tampering_refuses(self):
        path = self.producer / "native/runtime_ffi.h"
        path.write_text(path.read_text().replace("LEAN_EXPORT lean_object*", "LEAN_EXPORT void*", 1))
        self.refused("native provider header differs")

    def test_actual_boundary_keeps_baseline_and_binds_runtime_source(self):
        actual = boundary.inspect(self.root)
        self.assertEqual((actual["baseline_total"], actual["baseline_logical_safe"],
                          actual["runtime_open"], actual["interfaces_open"]), (7125, 7084, 41, 15))
        for module in actual["runtime_modules"]:
            self.assertIn((boundary.PRODUCER / (module.replace(".", "/") + ".lean")).as_posix(),
                          actual["source_inputs"])
        self.assertTrue(all(not name.startswith("TrustIrRuntime")
                            for name in actual["logical_import_modules"]))

    def test_changed_compatibility_macro_is_refused(self):
        path = self.producer / "TrustIr/CompilerCompat.lean"
        path.write_text(path.read_text().replace('let backend := Lean.mkIdent `c',
                                                'let backend := Lean.mkIdent `cpp', 1))
        self.refused("extern compatibility macro expansion changed")

    def test_changed_lake_facet_macro_is_refused(self):
        path = self.producer / "lakefile.lean"
        path.write_text(path.read_text().replace('Lake.Module.facetKind ++ $name', '$name', 1))
        self.refused("native Lake compatibility macro expansion changed")

    def test_attachment_cannot_omit_provider_facet(self):
        path = self.producer / "lakefile.lean"
        path.write_text(path.read_text().replace(
            'trustIrNativeFacet trustirRuntimeInit, trustIrNativeFacet trustirRuntimeProvider',
            'trustIrNativeFacet trustirRuntimeInit', 1))
        self.refused("native attachment requires its exported initializer and provider facets")

    def test_old_schema_cannot_omit_additional_support(self):
        self.ledger(lambda d: d.__setitem__("schema", 1))
        self.refused("unsupported runtime boundary schema")

    def test_native_support_cannot_be_certified_by_metadata(self):
        self.ledger(lambda d: d["support_obligations"][0].__setitem__("certified", True))
        self.refused("support metadata cannot promote")

    def test_native_support_cannot_disappear(self):
        self.ledger(lambda d: d["support_obligations"].pop())
        self.refused("support obligation census changed")

    def test_support_ids_cannot_collapse(self):
        self.ledger(lambda d: d["support_obligations"].__setitem__(1, d["support_obligations"][0]))
        self.refused("duplicate support obligation")

    def test_native_attachment_cannot_hide_logical_declarations(self):
        path = self.producer / "TrustIrNativeLink.lean"
        path.write_text(path.read_text() + "\ndef hidden : Nat := 0\n")
        self.refused("native attachment must have only")

    def test_provider_cannot_depend_on_its_native_attachment(self):
        path = self.producer / "TrustIrRuntime/ArrayEncoding.lean"
        path.write_text("import TrustIrNativeLink\n" + path.read_text())
        self.refused("runtime provider depends on its native attachment")

    def test_hidden_initializer_is_not_an_attachment(self):
        path = self.producer / "lakefile.lean"
        path.write_text(path.read_text().replace('"-DLEAN_EXPORTING", ', ''))
        self.refused("native initializer ABI expansion changed")

    def test_semantic_evaluation_must_activate_the_native_attachment(self):
        path = self.producer / "TrustIr/Semantics/Eval.lean"
        path.write_text(path.read_text().replace("import TrustIrNativeLink\n", ""))
        self.refused("semantic evaluation lacks its native attachment")

    def test_runtime_import_cannot_enter_logical_closure(self):
        p = self.producer / "TrustIr.lean"
        p.write_text("import TrustIrRuntime\n" + p.read_text())
        self.refused("runtime library leaked")

    def test_unknown_unsafe_declaration_is_not_hidden(self):
        p = self.producer / "TrustIrRuntime/ImageMap.lean"
        p.write_text(p.read_text().replace("end TrustIr.ByteImage.ImageMapRuntime",
                     "unsafe def unregistered : Nat := 0\nend TrustIr.ByteImage.ImageMapRuntime"))
        self.refused("runtime declaration identity mismatch")

    def test_duplicate_original_full_identity_cannot_collapse_rows(self):
        self.ledger(lambda d: d["runtime_obligations"].__setitem__(1, d["runtime_obligations"][0]))
        self.refused("duplicate original obligation identity")

    def test_baseline_denominator_cannot_shrink(self):
        self.ledger(lambda d: d["baseline"].__setitem__("total_obligations", 7084))
        self.refused("baseline obligations were changed")

    def test_historical_root_subject_cannot_be_relabelled(self):
        self.ledger(lambda d: d["baseline"].__setitem__("root_subject", "f" * 40))
        self.refused("historical baseline identity changed")

    def test_historical_ir_source_cannot_be_relabelled(self):
        self.ledger(lambda d: d["baseline"].__setitem__("ir_source", "f" * 40))
        self.refused("historical baseline identity changed")

    def test_full_inventory_digest_cannot_be_relabelled(self):
        self.ledger(lambda d: d["baseline"].__setitem__("complete_inventory_sha256", "f" * 64))
        self.refused("historical baseline identity changed")

    def test_metadata_scope_cannot_be_promoted(self):
        self.ledger(lambda d: d["baseline"].__setitem__("scope", "full_lean_metadata"))
        self.refused("historical baseline identity changed")

    def test_repair_predecessor_identity_cannot_be_relabelled(self):
        self.ledger(lambda d: d.__setitem__("repair_base", "f" * 40))
        self.refused("historical repair predecessor changed")

    def test_substituted_roster_and_matching_digest_cannot_self_authorize(self):
        import hashlib
        path = self.producer / "runtime-boundary-baseline.json"
        roster = json.loads(path.read_text())
        victim = roster["unsafe_declarations"][0]
        original = (victim["module"], victim["name"])
        victim["name"] = "TrustIr.FORGED.originalObligation"
        data = (json.dumps(roster, indent=2) + "\n").encode()
        path.write_bytes(data)
        def replace(d):
            d["baseline"]["roster_sha256"] = hashlib.sha256(data).hexdigest()
            for row in d["runtime_obligations"]:
                if (row["original_module"], row["original_full_name"]) == original:
                    row["original_full_name"] = victim["name"]
        self.ledger(replace)
        self.refused("historical baseline identity changed")

    def test_metadata_cannot_promote_runtime_to_certified(self):
        self.ledger(lambda d: d["runtime_obligations"][0].__setitem__("certified", True))
        self.refused("cannot promote")

    def test_forged_interface_full_name_refuses(self):
        self.ledger(lambda d: d["interfaces"][0].__setitem__(
            "runtime_full_name", "TrustIr.FORGED.unprovedProvider"))
        self.refused("ABI full-name identity does not match")

    def test_forged_public_logical_full_name_refuses(self):
        self.ledger(lambda d: d["interfaces"][0].__setitem__(
            "logical_full_name", "TrustIr.FORGED.Leaf.checkStored"))
        self.refused("logical interface attachment mismatch")

    def test_forged_private_logical_full_name_refuses(self):
        self.ledger(lambda d: d["interfaces"][-1].__setitem__(
            "logical_full_name", "_private.TrustIr.FORGED.99.TrustIr.AggregateMemory.encodeArrayImage"))
        self.refused("logical interface attachment mismatch")

    def test_logical_namespace_drift_refuses(self):
        path = self.producer / "TrustIr/State/ValueMap.lean"
        path.write_text(path.read_text().replace("namespace TrustIr\n", "namespace Forged\n", 1)
                        .replace("end TrustIr\n", "end Forged\n"))
        self.refused("logical interface attachment mismatch")

    def test_private_logical_visibility_drift_refuses(self):
        path = self.producer / "TrustIr/Semantics/AggregateImages.lean"
        self.assertEqual(path.read_text().count("private def encodeArrayImage"), 1)
        path.write_text(path.read_text().replace("private def encodeArrayImage", "def encodeArrayImage"))
        self.refused("logical interface attachment mismatch")

    def test_missing_abi_export_refuses(self):
        p = self.producer / "TrustIrRuntime/ImageMap.lean"
        p.write_text(p.read_text().replace("l_TrustIr_ByteImage_map", "wrong_runtime_map"))
        self.refused("export/provider mismatch")

    def test_inline_adapter_cannot_repeat_or_omit_an_argument(self):
        p = self.producer / "TrustIr/State/CompactArray.lean"
        p.write_text(p.read_text().replace("#1, #2, #3, #4, #5)", "#1, #2, #3, #4, #4)", 1))
        self.refused("logical interface attachment mismatch")

    def test_partial_provider_preloading_is_refused(self):
        p = self.producer / "lakefile.lean"
        needle = "  precompileModules := false"
        self.assertIn(needle, p.read_text())
        p.write_text(p.read_text().replace(needle, "  precompileModules := true"))
        self.refused("must load through the complete native attachment")

    def test_missing_executable_attachment_refuses(self):
        p = self.producer / "TrustIrEval/Main.lean"
        p.write_text(p.read_text().replace("import TrustIrRuntime\n", ""))
        self.refused("lacks one explicit complete attachment")

    def test_unregistered_transitive_runtime_dependency_refuses(self):
        p = self.producer / "TrustIrRuntime/ImageMap.lean"
        p.write_text("import TrustIrEval.Run\n" + p.read_text())
        self.refused("unregistered runtime dependency")

    def test_runtime_byte_change_invalidates_source_equality_receipt(self):
        prior = self.root / "bound.json"
        prior.write_text(json.dumps(boundary.inspect(self.root)))
        p = self.producer / "TrustIrRuntime/ImageMap.lean"
        p.write_text(p.read_text() + "\n-- Changed runtime input remains visible.\n")
        result = subprocess.run([sys.executable, str(GUARD), "--root", str(self.root),
                                 "--against", str(prior)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("source inputs differ", result.stderr)

    def test_inventory_cannot_write_into_its_source_input_tree(self):
        output = self.producer / "self-inventory.json"
        result = subprocess.run([sys.executable, str(GUARD), "--root", str(self.root),
                                 "--output", str(output)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("must not become its own producer input", result.stderr)
        self.assertFalse(output.exists())


class LogicalExternNamesTests(unittest.TestCase):
    HOOK = '@[nospecialize, extern 1 c inline "l_entry(#1)"]\n'

    def names(self, text):
        return [row[3] for row in boundary.logical_extern_declarations("TrustIr.Test", text)]

    def test_compatibility_macro_retains_arity_pattern_and_private_identity(self):
        text = ('namespace TrustIr\n@[nospecialize, trustIrExtern 2 "l_entry(#1, #2)"]\n'
                'private def entry : Nat := 0\nend TrustIr\n')
        self.assertEqual(boundary.logical_extern_declarations("TrustIr.Test", text),
                         [("TrustIr.Test", 2, "l_entry(#1, #2)",
                           "_private.TrustIr.Test.0.TrustIr.entry")])

    def test_namespace_section_and_mutual_scopes_preserve_full_names(self):
        text = ("namespace TrustIr\nsection Values\nnamespace CompactArray\nmutual\n"
                + self.HOOK + "def Leaf.entry : Nat := 0\nend\nend CompactArray\n"
                "end Values\nend TrustIr\n")
        self.assertEqual(self.names(text), ["TrustIr.CompactArray.Leaf.entry"])

    def test_private_module_and_numeric_prefix_are_retained(self):
        text = "namespace TrustIr.Test\n" + self.HOOK + "private def entry : Nat := 0\nend TrustIr.Test\n"
        self.assertEqual(self.names(text), ["_private.TrustIr.Test.0.TrustIr.Test.entry"])

    def test_strings_and_nested_comments_cannot_change_scope(self):
        text = ('namespace TrustIr\ndef text := "\nnamespace Forged\nend\n"\n'
                '/- namespace Ignored /- end -/ end -/\n'
                + self.HOOK + "def entry : Nat := 0\nend TrustIr\n")
        self.assertEqual(self.names(text), ["TrustIr.entry"])

    def test_mismatched_scope_end_refuses(self):
        text = "namespace TrustIr\n" + self.HOOK + "def entry : Nat := 0\nend Forged\n"
        with self.assertRaisesRegex(boundary.BoundaryError, "mismatched logical scope end"):
            self.names(text)

    def test_absolute_declaration_refuses(self):
        text = ("namespace TrustIr\n" + self.HOOK
                + "def _root_.TrustIr.entry : Nat := 0\nend TrustIr\n")
        with self.assertRaisesRegex(boundary.BoundaryError, "unsupported absolute logical declaration"):
            self.names(text)

    def test_unclassified_or_absolute_scope_refuses(self):
        for scope in ("namespace TrustIr def hidden : Nat := 0", "namespace _root_.TrustIr"):
            with self.subTest(scope=scope), self.assertRaises(boundary.BoundaryError):
                self.names(scope + "\n" + self.HOOK + "def entry : Nat := 0\nend\n")

    def test_character_literal_cannot_pair_with_a_later_string(self):
        # A string-only scan pairs the `"` of `'"'` with the next string, hiding the
        # `end` / `namespace` commands between them.
        text = ("namespace TrustIr\ndef q := '\"'\nend TrustIr\nnamespace TrustIr.Inner\n"
                'def s := "x"\n' + self.HOOK + "def entry : Nat := 0\nend TrustIr.Inner\n")
        self.assertEqual(self.names(text), ["TrustIr.Inner.entry"])

    def test_raw_string_cannot_change_scope(self):
        text = ('namespace TrustIr\ndef j := r#"\n"\nend\n"#\n'
                + self.HOOK + "def entry : Nat := 0\nend TrustIr\n")
        self.assertEqual(self.names(text), ["TrustIr.entry"])


class LeanLexerTests(unittest.TestCase):
    """The guard's one Lean lexer: comments go, literal and identifier extents stay."""

    def lexed(self, text):
        cleaned = boundary.comments_removed(text)
        self.assertEqual(len(cleaned), len(text))
        self.assertEqual([i for i, ch in enumerate(cleaned) if ch == "\n"],
                         [i for i, ch in enumerate(text) if ch == "\n"])
        return cleaned

    def test_island_end_preserves_offsets_and_stops_before_following_rust(self):
        prefix = 'not Lean "'
        bodies = ['-- } "\n', '/- } /- nested -/ -/', 'def s := "}"',
                  'def s := r##"}"##', "def c := '}'", 'def «}» := { x := 1 }']
        for body in bodies:
            with self.subTest(body=body):
                source = prefix + body + '} fn f<\'a>() { "unterminated'
                self.assertEqual(boundary.island_end(source, len(prefix)),
                                 len(prefix) + len(body) + 1)

    def test_character_literals_and_escapes_keep_one_extent(self):
        for literal in ("'\"'", r"'\''", r"'\\'", r"'\"'", r"'\n'", r"'\r'",
                        r"'\t'", r"'\x41'", r"'\u03B1'", r"'\u{1F600}'", "'-'", "'/'",
                        "'\u00ab'", "' '"):
            with self.subTest(literal=literal):
                comment = f'-- {literal} " /-'
                text = f'def c := {literal} {comment}\ndef s := "-- kept" /- gone -/\n'
                self.assertEqual(self.lexed(text),
                                 f'def c := {literal} {" " * len(comment)}\n'
                                 f'def s := "-- kept" {" " * 10}\n')
                self.assertEqual(boundary.code_only(f"x {literal} y"),
                                 f"x {' ' * len(literal)} y")

    def test_primed_identifiers_are_not_character_literals(self):
        text = ("theorem foo' (x' : Nat) (h'' : x' = 0) : x' = 0 := h''\n"
                "def \u03b1' := 1 -- c'\n"
                "def x\u2081' := \u03b1' /- 'a -/\n"
                "def get!' := f x\u2081'\"s -- kept\" a'b' \u00abx'\u00bb\n")
        expected = (text.replace(" -- c'\n", "      \n", 1)
                    .replace(" /- 'a -/\n", " " * 9 + "\n", 1))
        self.assertEqual(self.lexed(text), expected)
        self.assertEqual(boundary.code_only("a'b' x' h''"), "a'b' x' h''")

    def test_core_primed_tokens_are_not_character_literals(self):
        text = ("def a := xs[i]'(by omega) -- c\n"
                "abbrev P := (_ : Nat) \u00d7' Nat\n"
                "abbrev Q := \u03a3' n : Nat, n = 0\n"
                "def i := f '' s\n")
        expected = text.replace(" -- c\n", "     \n", 1)
        self.assertEqual(self.lexed(text), expected)
        self.assertEqual(boundary.code_only(expected), expected)

    def test_raw_strings_end_at_their_own_hash_count(self):
        text = (r'def a := r"\" -- c' "\n"
                r'def b := r#"x"-- kept"# -- gone' "\n"
                r'''def c := r##"{"k":"'"}"#"## /- gone -/''' "\n")
        expected = (text.replace(" -- c\n", "     \n", 1)
                    .replace(" -- gone\n", " " * 8 + "\n", 1)
                    .replace(" /- gone -/\n", " " * 11 + "\n", 1))
        self.assertEqual(self.lexed(text), expected)
        self.assertEqual(boundary.code_only('x r#"a"b"# y'), "x " + " " * len('r#"a"b"#') + " y")

    def test_identifier_escapes_are_names(self):
        text = 'def \u00aba"b\u00bb := 1 -- c\ndef \u00abx -- y\u00bb := \u00aba\'b\u00bb\n'
        self.assertEqual(self.lexed(text), text.replace(" -- c\n", "     \n", 1))

    def test_unterminated_or_malformed_tokens_refuse(self):
        cases = [
            ('def s := "abc', "unterminated Lean comment or string"),
            ('def s := "abc\\', "unterminated Lean comment or string"),
            ("/- a /- b -/", "unterminated Lean comment or string"),
            ('def s := r#"abc"', "unterminated Lean comment or string"),
            ("def c := 'ab'", "unterminated Lean character literal"),
            ("def c := 'a", "unterminated Lean character literal"),
            ("def c := (f x)' y", "unterminated Lean character literal"),
            ("def c := '", "malformed Lean character literal"),
            (r"def c := '\q'", "malformed Lean character literal"),
            (r"def c := '\x4'", "malformed Lean character literal"),
            (r"def c := '\u12'", "malformed Lean character literal"),
            (r"def c := '\u{}'", "malformed Lean character literal"),
            ("def \u00ababc := 1", "unterminated Lean identifier escape"),
        ]
        for text, message in cases:
            for lex in (boundary.comments_removed, boundary.code_only):
                with self.subTest(text=text, lex=lex.__name__), \
                        self.assertRaisesRegex(boundary.BoundaryError, message):
                    lex(text)


if __name__ == "__main__":
    unittest.main()
