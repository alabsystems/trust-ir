#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""The history removed by the 2026-11-15 rewrite must not return through a merge."""

from __future__ import annotations

from pathlib import Path
import subprocess
import unittest


ROOT = Path(__file__).resolve().parents[2]
# First commit of the removed line. A HEAD that descends from it carries the
# 17 GB of archive payloads, and an ordinary push of it uploads them again.
OLD_LINE = "6b4f55ce8624bc00659c512ab01a8650dd87eb48"


class HistoryRewriteGuard(unittest.TestCase):
    def test_head_does_not_descend_from_the_removed_history(self):
        if not (ROOT / ".git").exists():
            self.skipTest("not a Git checkout")
        present = subprocess.run(["git", "-C", str(ROOT), "cat-file", "-e", OLD_LINE + "^{commit}"],
                                 capture_output=True).returncode == 0
        if not present:
            return  # A clone of the repaired history has no such object.
        descends = subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor", OLD_LINE, "HEAD"],
                                  capture_output=True).returncode == 0
        self.assertFalse(descends, "HEAD contains the history removed on 2026-11-15; do not push. "
                                   "Reset to origin/main and cherry-pick your own commits "
                                   "(HISTORY-REWRITE-2026-11-15.md).")


if __name__ == "__main__":
    unittest.main()
