# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Pure source/lock controls; no native policy is installed or observed."""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import ay_exec_policy_owner as owner

REV = "1" * 40
SOURCE = f"git+{owner.AY_URL}?rev={REV}#{REV}"


def packages():
    return [
        {"name": "ay-sys", "version": owner.OWNER_AY_VERSION, "source": SOURCE,
         "dependencies": [owner.NAME]},
        {"name": owner.NAME, "version": owner.VERSION, "source": SOURCE,
         "dependencies": ["libc"]},
        {"name": "libc", "version": "0.2.177", "source": owner.REGISTRY,
         "checksum": "a" * 64},
    ]


class ExecPolicyOwnerTests(unittest.TestCase):
    def test_exact_source_qualified_required_owner_and_libc_route(self):
        rows = packages()
        self.assertEqual(owner.locked_identity(rows, REV, owner.OWNER_AY_VERSION),
                         (owner.NAME, owner.VERSION, SOURCE))
        rows[0]["dependencies"] = [f"{owner.NAME} {owner.VERSION} ({SOURCE.split('#')[0]})"]
        rows.append({"name": owner.NAME, "version": owner.VERSION, "source": owner.REGISTRY})
        self.assertEqual(owner.locked_identity(rows, REV, owner.OWNER_AY_VERSION),
                         (owner.NAME, owner.VERSION, SOURCE))

    def test_missing_foreign_stale_duplicate_or_aliased_owner_rows_refuse(self):
        mutations = [
            lambda d: d[0].update(version="0.27.0"),
            lambda d: d[1].update(version="0.14.0"),
            lambda d: d[1].update(source=SOURCE.replace(REV, "2" * 40)),
            lambda d: d.append(copy.deepcopy(d[1])),
            lambda d: d[0].update(dependencies=[]),
            lambda d: d.pop(0),
            lambda d: d.append({"name": "other", "version": "1", "dependencies": [owner.NAME]}),
            lambda d: d[0].update(dependencies=[owner.NAME, owner.NAME]),
            lambda d: d[1].update(checksum="b" * 64),
        ]
        for index, mutate in enumerate(mutations):
            rows = packages()
            mutate(rows)
            with self.subTest(mutation=index), self.assertRaises(owner.OwnerError):
                owner.locked_identity(rows, REV, owner.OWNER_AY_VERSION)
        with self.assertRaises(owner.OwnerError):
            owner.locked_identity(packages(), REV, "0.27.0")

    def test_sole_existing_registry_libc_edge_and_full_identity_are_required(self):
        mutations = [
            lambda d: d[1].update(dependencies=[]),
            lambda d: d[1].update(dependencies=["libc", "libc"]),
            lambda d: d[2].update(source=SOURCE),
            lambda d: d[2].update(version="0.3.0"),
            lambda d: d.append(copy.deepcopy(d[2])),
            lambda d: d[1].update(dependencies="libc"),
        ]
        for index, mutate in enumerate(mutations):
            rows = packages()
            mutate(rows)
            with self.subTest(mutation=index), self.assertRaises(owner.OwnerError):
                owner.locked_identity(rows, REV, owner.OWNER_AY_VERSION)

    def test_required_policy_edge_accepts_rust_whitespace(self):
        base = SOURCE.split("#")[0]
        for edge in (" " + owner.NAME, owner.NAME + " ", "\t" + owner.NAME,
                     f"  {owner.NAME}  {owner.VERSION}  ({base})  ",
                     "\u00a0" + owner.NAME + "\u2003"):
            rows = packages()
            rows[0]["dependencies"] = [edge]
            with self.subTest(edge=edge):
                self.assertEqual(owner.locked_identity(rows, REV, owner.OWNER_AY_VERSION),
                                 (owner.NAME, owner.VERSION, SOURCE))

    def test_other_or_duplicate_incoming_policy_edge_cannot_hide_in_whitespace(self):
        for edge in (" " + owner.NAME, "  " + owner.NAME,
                     "\t" + owner.NAME, "\n" + owner.NAME,
                     "\u00a0" + owner.NAME, "\u2003" + owner.NAME):
            for duplicate in (False, True):
                rows = packages()
                if duplicate:
                    rows[0]["dependencies"].append(edge)
                else:
                    rows.append({"name": "other", "version": "1", "dependencies": [edge]})
                with self.subTest(edge=edge, duplicate=duplicate), self.assertRaises(owner.OwnerError):
                    owner.locked_identity(rows, REV, owner.OWNER_AY_VERSION)

    def test_python_only_control_separators_do_not_split_rust_dependency_tokens(self):
        # Python str.split also treats these as whitespace; Rust does not.
        for separator in ("\x1c", "\x1d", "\x1e", "\x1f"):
            with self.subTest(separator=separator), self.assertRaises(owner.OwnerError):
                owner.resolve(owner.NAME + separator + owner.VERSION, packages())

    def test_absent_package_is_not_minted_for_older_epochs(self):
        rows = [{"name": "ay-sys", "version": "0.27.0", "source": SOURCE}]
        self.assertIsNone(owner.locked_identity(rows, REV, "0.27.0"))
        self.assertIsNone(owner.locked_identity([], REV, owner.OWNER_AY_VERSION))
        with self.assertRaises(owner.OwnerError):
            owner.locked_identity([None], REV, owner.OWNER_AY_VERSION)


if __name__ == "__main__":
    unittest.main(verbosity=2)
