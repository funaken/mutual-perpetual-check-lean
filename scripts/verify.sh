#!/usr/bin/env bash
# Reproduce the proof checks without changing Lean/Mathlib versions.
set -euo pipefail
cd "$(dirname "$0")/.."
work=$(mktemp -d "${TMPDIR:-/tmp}/mpc-verify.XXXXXX")
trap 'rm -rf "$work"' EXIT
python3 scripts/source_audit.py
python3 scripts/manuscript_refs.py
lake build
lake build MPC.Verification MPC.Axioms MPC.PaperVerification
MPC_API_OUTPUT="$work/api.jsonl" lake env lean scripts/api_snapshot.lean
python3 scripts/check_api.py "$work/api.jsonl"
./scripts/verify_chess.sh
python3 scripts/external_check.py
if [ -e .git ]; then git diff --check; fi
echo 'PASS: source, builds, exact shogi main statement, chess checks, isolation, types, axiom dependencies and external type check'
