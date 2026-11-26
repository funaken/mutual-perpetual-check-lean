#!/usr/bin/env bash
# The manuscript builds with Tectonic 0.17.0 or XeLaTeX plus CJK fonts.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/paper_metrics.py
mkdir -p output/pdf
if [ -n "${TECTONIC:-}" ] || command -v tectonic >/dev/null 2>&1; then
  export TECTONIC_CACHE_DIR="${TECTONIC_CACHE_DIR:-$PWD/.cache/tectonic}"
  build() { "${TECTONIC:-tectonic}" --keep-logs --outdir output/pdf "paper/$1.tex"; }
elif command -v xelatex >/dev/null 2>&1; then
  # Relative \input files are resolved from paper/ by both engines.
  build() {
    (cd paper && xelatex -halt-on-error -interaction=nonstopmode -output-directory=../output/pdf "$1.tex")
    (cd paper && xelatex -halt-on-error -interaction=nonstopmode -output-directory=../output/pdf "$1.tex")
  }
else
  echo 'Install Tectonic 0.17.0 (or XeLaTeX), and Noto CJK fonts; see paper/README.md.' >&2
  exit 1
fi
for name in main main_en; do
  build "$name"
  if grep -E 'Overfull \\[hv]box|Missing character:|Undefined control sequence|undefined references' "output/pdf/$name.log"; then
    echo "Fix the layout or references of $name before release." >&2
    exit 1
  fi
done
