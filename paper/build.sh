#!/usr/bin/env bash
# Build the paper PDF.  Run from anywhere:  bash paper/build.sh
# Needs pdflatex with pgfplots; override the binary with PDFLATEX=...
#
# The numbers of the q = 12 Lean proof and of the main theorem's window live in
# q12data.tex, and those of the best window at each length in lengthdata.tex. Both
# are kept by hand; each file's header says how each number was computed.
set -euo pipefail
cd "$(dirname "$0")"
PDFLATEX=${PDFLATEX:-$(command -v pdflatex || echo /Library/TeX/texbin/pdflatex)}
[ -x "$PDFLATEX" ] || { echo "pdflatex not found; install TeX Live or set PDFLATEX=..." >&2; exit 1; }
for i in 1 2 3; do
  "$PDFLATEX" -interaction=nonstopmode -halt-on-error simple-zeros-lower-bound.tex > /dev/null
done
grep -m1 "Output written" simple-zeros-lower-bound.log
rm -f simple-zeros-lower-bound.{aux,out,log}
