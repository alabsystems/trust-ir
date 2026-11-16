"""Exact immutable per-package authority, including independent workspaces."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import derive_ay_package_contract as CONTRACT

REV = "a" * 40
HOME = Path("/cargo")
SOURCE = f"git+{CONTRACT.AY_REMOTE}?rev={REV}#{REV}"


class Authority:
    def __init__(self, files):
        self.files = {p: value.encode() for p, value in files.items()}

    def read(self, path):
        data = self.files[path]
        return data, hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

    def optional(self, path):
        return self.read(path) if path in self.files else None


def package(name, version, path):
    return {"name": name, "version": version, "source": SOURCE,
            "manifest_path": str(HOME / "git/checkouts/ay-0123456789abcdef" / REV[:7] / path)}


class PackageContractTests(unittest.TestCase):
    def setUp(self):
        self.files = {
            "Cargo.toml": '[workspace.package]\nversion = "0.28.0"\n',
            "crates/ay-core/Cargo.toml": '[package]\nname = "ay-core"\nversion.workspace = true\n',
            "vendor/policy/Cargo.toml": '[package]\nname = "policy"\nversion = "0.13.0"\n',
        }
        self.metadata = {"packages": [package("ay-core", "0.28.0", "crates/ay-core/Cargo.toml"),
                                      package("policy", "0.13.0", "vendor/policy/Cargo.toml")]}

    def derive(self, metadata=None, files=None):
        return CONTRACT.derive(metadata if metadata is not None else self.metadata,
                               REV, "0.28.0", HOME,
                               Authority(files if files is not None else self.files))

    def test_heterogeneous_versions_come_from_exact_manifests(self):
        result = self.derive()
        self.assertEqual([(p["name"], p["version"]) for p in result["packages"]],
                         [("ay-core", "0.28.0"), ("policy", "0.13.0")])
        self.assertEqual(result["packages"][0]["version_source"]["path"], "Cargo.toml")
        self.assertEqual(result["packages"][1]["version_source"]["path"], "vendor/policy/Cargo.toml")
        self.assertNotIn(str(HOME), json.dumps(result))

    def test_nested_workspace_version_is_not_the_ay_workspace_version(self):
        self.files["vendor/policy/Cargo.toml"] = '[workspace.package]\nversion = "0.13.0"\n'
        self.files["vendor/policy/crates/leaf/Cargo.toml"] = (
            '[package]\nname = "policy"\nversion.workspace = true\n')
        self.metadata["packages"][1] = package("policy", "0.13.0", "vendor/policy/crates/leaf/Cargo.toml")
        for explicit in (False, True):
            with self.subTest(explicit=explicit):
                files = dict(self.files)
                if explicit:
                    files["vendor/policy/crates/leaf/Cargo.toml"] += 'workspace = "../.."\n'
                result = self.derive(files=files)
                self.assertEqual(result["packages"][1]["version_source"]["path"],
                                 "vendor/policy/Cargo.toml")

    def test_forged_version_name_revision_and_duplicate_identity_refuse(self):
        for mutation in ("version", "name", "revision", "duplicate", "empty"):
            with self.subTest(mutation=mutation):
                metadata = copy.deepcopy(self.metadata)
                if mutation == "version": metadata["packages"][1]["version"] = "0.12.0"
                if mutation == "name": metadata["packages"][1]["name"] = "not-policy"
                if mutation == "revision": metadata["packages"][1]["source"] = SOURCE.replace(REV, "b" * 40)
                if mutation == "duplicate": metadata["packages"].append(dict(metadata["packages"][0]))
                if mutation == "empty": metadata["packages"] = []
                with self.assertRaises(ValueError): self.derive(metadata=metadata)

    def test_unsafe_or_ambiguous_checkout_locators_refuse_without_local_reads(self):
        for locator in ("/private/Cargo.toml", "relative/Cargo.toml",
                        "/cargo/git/checkouts/other-01234567/aaaaaaa/Cargo.toml",
                        "/cargo/git/checkouts/ay-01234567/bbbbbbb/Cargo.toml",
                        "/cargo/git/checkouts/ay-01234567/aaaaaaa/../Cargo.toml"):
            with self.subTest(locator=locator):
                with self.assertRaises(ValueError): CONTRACT.repository_path(locator, REV, HOME)

    def test_toml_string_contents_cannot_become_package_declarations(self):
        self.files["vendor/policy/Cargo.toml"] = '''[package]
description = """
[package]
name = "forged"
version = "0.99.0"
"""
name = "policy"
version = "0.13.0"
'''
        self.assertEqual(self.derive()["packages"][1]["version"], "0.13.0")

    def test_non_boolean_inheritance_and_workspace_escape_refuse(self):
        for declaration in ('version.workspace = 1',
                            'version.workspace = true\nworkspace = "../../.."'):
            with self.subTest(declaration=declaration):
                files = dict(self.files)
                files["vendor/policy/Cargo.toml"] = '[package]\nname = "policy"\n' + declaration + '\n'
                with self.assertRaises(ValueError): self.derive(files=files)

    def test_missing_or_forged_root_workspace_version_refuses(self):
        for root in ('[workspace.package]\nversion = "0.27.0"\n',
                     '[workspace]\n', 'workspace = false\n'):
            with self.subTest(root=root):
                files = dict(self.files); files["Cargo.toml"] = root
                with self.assertRaises(ValueError): self.derive(files=files)


if __name__ == "__main__":
    unittest.main()
