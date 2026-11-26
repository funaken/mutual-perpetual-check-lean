#!/usr/bin/env bash
# Historical command name retained for reproducibility of existing instructions.
set -euo pipefail
case "${1:-}" in
  ''|--phase6-complete) ;;
  *) echo 'Usage: verify_phase6.sh [--phase6-complete]' >&2; exit 2 ;;
esac
exec "$(dirname "$0")/verify.sh"
