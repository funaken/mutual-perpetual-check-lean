#!/usr/bin/env bash
# Independent chess checks; no shogi proof is imported by these Lean roots.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/source_audit.py
lake build MPC.Chess MPC.Chess.Verification
echo 'PASS: chess foundation, regressions, import isolation and axiom dependencies'
