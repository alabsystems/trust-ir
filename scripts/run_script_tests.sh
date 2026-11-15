#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Keep each test file in its own process; report actual unittest outcomes.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
exec python3 -B "$SCRIPT_DIR/run_script_tests.py" "$@"
