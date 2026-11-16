"""Immutable native authority bytes and no direct transport fallback."""
import base64
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import unittest
import tempfile
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("dependency_authority", ROOT / "scripts/dependency_authority.py")
AUTH = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUTH)
BUMP_SOURCE = (ROOT / "scripts/bump-dep-pin.sh").read_text()


class AuthorityTests(unittest.TestCase):
    def fixture(self, data=b"[workspace]\r\n# unicode: \xc3\xa9\n"):
        revision = "a" * 40
        tree = "b" * 40
        oid = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        replies = {
            f"git/commits/{revision}": {"sha": revision, "tree": {"sha": tree}},
            f"git/trees/{tree}": {"sha": tree, "truncated": False, "tree": [
                {"path": "Cargo.toml", "type": "blob", "mode": "100644", "sha": oid}]},
            f"git/blobs/{oid}": {"sha": oid, "size": len(data), "encoding": "base64",
                                   "content": base64.encodebytes(data).decode()},
        }
        return revision, tree, oid, replies, data

    def test_online_owner_has_no_direct_git_fetch_or_init(self):
        self.assertNotIn('git -C "$PROBE" fetch', BUMP_SOURCE)
        self.assertNotIn('git -C "$authority" fetch', BUMP_SOURCE)
        self.assertNotIn('git init', BUMP_SOURCE)
        self.assertIn('"$AUTHORITY" manifest clean "$clean_rev"', BUMP_SOURCE)
        self.assertIn('"$AUTHORITY" remote "$REMOTE_REPO" "$REV"', BUMP_SOURCE)

    def read_fixture(self, replies, revision):
        return AUTH.manifest("clean", revision)

    def test_exact_git_blob_bytes_preserve_unicode_crlf(self):
        rev, _, _, replies, data = self.fixture()
        with patch.object(AUTH, "remote"), patch.object(AUTH, "api", side_effect=lambda repo, p: replies[p]):
            self.assertEqual(self.read_fixture(replies, rev), data)

    def test_forged_bytes_metadata_mode_and_tree_refuse(self):
        for mutation in ("bytes", "size", "encoding", "mode", "tree", "commit"):
            with self.subTest(mutation=mutation):
                rev, tree, oid, replies, _ = self.fixture()
                if mutation == "bytes": replies[f"git/blobs/{oid}"]["content"] = base64.b64encode(b"!" * replies[f"git/blobs/{oid}"]["size"]).decode()
                if mutation == "size": replies[f"git/blobs/{oid}"]["size"] += 1
                if mutation == "encoding": replies[f"git/blobs/{oid}"]["encoding"] = "utf-8"
                if mutation == "mode": replies[f"git/trees/{tree}"]["tree"][0]["mode"] = "120000"
                if mutation == "tree": replies[f"git/trees/{tree}"]["truncated"] = True
                if mutation == "commit": replies[f"git/commits/{rev}"]["sha"] = "c" * 40
                with patch.object(AUTH, "remote"), patch.object(AUTH, "api", side_effect=lambda repo, p: replies[p]):
                    with self.assertRaises(ValueError): self.read_fixture(replies, rev)

    def test_native_error_has_no_git_or_anonymous_fallback(self):
        with patch.object(AUTH, "invoke", side_effect=subprocess.CalledProcessError(6, ["agh"])), patch.object(AUTH, "offline_manifest") as offline:
            with self.assertRaises(subprocess.CalledProcessError): AUTH.manifest("clean", "a" * 40)
            offline.assert_not_called()
        with patch.object(AUTH.shutil, "which", return_value="/owned/agh"), patch.object(AUTH.subprocess, "check_output", return_value=b"ok") as run:
            AUTH.invoke(["api", "repos/alabsystems/clean"])
            self.assertEqual(run.call_args.args[0][:2], ["/owned/agh", "--no-anonymous-api"])

    def test_environment_disables_ambient_and_cached_indirection(self):
        with patch.dict(os.environ, {"GIT_DIR": "/other", "GIT_CONFIG_GLOBAL": "/poison", "GIT_GRAFT_FILE": "/graft", "GIT_NAMESPACE": "other", "GIT_TEMPLATE_DIR": "/template", "GIT_SHALLOW_FILE": "/shallow"}):
            env = AUTH.git_environment()
        for key in ("GIT_DIR", "GIT_NAMESPACE", "GIT_TEMPLATE_DIR", "GIT_SHALLOW_FILE"):
            self.assertNotIn(key, env)
        self.assertEqual(env["GIT_CONFIG_GLOBAL"], os.devnull)
        self.assertEqual(env["GIT_GRAFT_FILE"], os.devnull)
        self.assertEqual(env["GIT_CONFIG_NOSYSTEM"], "1")
        self.assertEqual(env["GIT_NO_REPLACE_OBJECTS"], "1")
        self.assertEqual(env["GIT_NO_LAZY_FETCH"], "1")

    def test_real_cached_replacement_changes_legacy_bytes_but_not_offline_reader(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            env = AUTH.git_environment()
            def git(*args, raw=False, environment=env):
                data = subprocess.check_output(["git", "-C", str(root), *args], env=environment)
                return data if raw else data.decode().strip()
            git("init", "--quiet", "--template=", "--object-format=sha1")
            git("config", "user.name", "Authority fixture")
            git("config", "user.email", "authority@example.invalid")
            first = b"[workspace]\n# original exact commit bytes\n"
            second = b"[workspace]\n# replacement must not become authority\n"
            (root / "Cargo.toml").write_bytes(first)
            git("add", "Cargo.toml"); git("commit", "--quiet", "-m", "original")
            original = git("rev-parse", "HEAD")
            (root / "Cargo.toml").write_bytes(second)
            git("add", "Cargo.toml"); git("commit", "--quiet", "-m", "replacement")
            replacement = git("rev-parse", "HEAD")
            git("replace", original, replacement)
            legacy = dict(env); legacy.pop("GIT_NO_REPLACE_OBJECTS")
            self.assertEqual(git("show", original + ":Cargo.toml", raw=True, environment=legacy), second)
            self.assertEqual(AUTH.offline_manifest(root, original), first)

    def test_wrong_remote_identity_and_unowned_repository_refuse(self):
        with patch.object(AUTH, "invoke", return_value=b"b" * 40):
            with self.assertRaises(ValueError): AUTH.remote("clean", "a" * 40)
        with self.assertRaises(ValueError): AUTH.remote("../clean", "a" * 40)
        with self.assertRaises(ValueError): AUTH.remote("clean", "a" * 39)

    def nested_fixture(self):
        rev, root, _, replies, original = self.fixture()
        parent, child = "d" * 40, "e" * 40
        data = b'[package]\nname = "policy"\nversion = "0.13.0"\n'
        oid = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        replies[f"git/trees/{root}"]["tree"].append(
            {"path": "vendor", "type": "tree", "mode": "040000", "sha": parent})
        replies[f"git/trees/{parent}"] = {
            "sha": parent, "truncated": False, "tree": [
                {"path": "policy", "type": "tree", "mode": "040000", "sha": child}]}
        replies[f"git/trees/{child}"] = {
            "sha": child, "truncated": False, "tree": [
                {"path": "Cargo.toml", "type": "blob", "mode": "100644", "sha": oid}]}
        replies[f"git/blobs/{oid}"] = {
            "sha": oid, "size": len(data), "encoding": "base64",
            "content": base64.encodebytes(data).decode()}
        return rev, root, parent, child, replies, original, data

    def test_nested_manifest_uses_the_same_commit_and_reuses_only_its_trees(self):
        rev, root, parent, child, replies, original, data = self.nested_fixture()
        with patch.object(AUTH, "remote") as remote, patch.object(
                AUTH, "api", side_effect=lambda repo, p: replies[p]) as api:
            source = AUTH.ManifestAuthority("ay", rev)
            self.assertEqual(source.read("vendor/policy/Cargo.toml")[0], data)
            self.assertEqual(source.read("Cargo.toml")[0], original)
            self.assertEqual(source.read("vendor/policy/Cargo.toml")[0], data)
            remote.assert_called_once_with("ay", rev)
            for oid in (root, parent, child):
                self.assertEqual(sum(call.args[1] == f"git/trees/{oid}"
                                     for call in api.call_args_list), 1)

    def test_manifest_path_traversal_and_non_manifest_paths_refuse(self):
        rev, _, _, replies, _ = self.fixture()
        with patch.object(AUTH, "remote"), patch.object(AUTH, "api", side_effect=lambda repo, p: replies[p]):
            source = AUTH.ManifestAuthority("ay", rev)
            for path in ("../Cargo.toml", "/Cargo.toml", "vendor//Cargo.toml",
                         "vendor/./Cargo.toml", "vendor/../Cargo.toml",
                         "vendor\\Cargo.toml", "vendor/README.md", "\x00/Cargo.toml"):
                with self.subTest(path=path), self.assertRaises(ValueError):
                    source.read(path)

    def test_nested_symlink_duplicate_and_incomplete_ancestors_refuse(self):
        for mutation in ("symlink", "duplicate", "truncated", "wrong_identity", "leaf_mode"):
            with self.subTest(mutation=mutation):
                rev, _, parent, child, replies, _, _ = self.nested_fixture()
                entries = replies[f"git/trees/{parent}"]["tree"]
                if mutation == "symlink": entries[0]["mode"] = "120000"
                if mutation == "duplicate": entries.append(dict(entries[0]))
                if mutation == "truncated": replies[f"git/trees/{parent}"]["truncated"] = True
                if mutation == "wrong_identity": replies[f"git/trees/{parent}"]["sha"] = "f" * 40
                if mutation == "leaf_mode": replies[f"git/trees/{child}"]["tree"][0]["mode"] = "120000"
                with patch.object(AUTH, "remote"), patch.object(AUTH, "api", side_effect=lambda repo, p: replies[p]):
                    with self.assertRaises(ValueError):
                        AUTH.ManifestAuthority("ay", rev).read("vendor/policy/Cargo.toml")


if __name__ == "__main__": unittest.main()
