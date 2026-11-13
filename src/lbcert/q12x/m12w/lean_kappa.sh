#!/bin/bash
# lean_kappa.sh REFIT.json MODEL.pkl OUTDIR   (the repository's .venv)
# regen_window.py for the refit's window (pvCheck cells chosen by the script, --replay: every window check),
# then the exact kappa = (H_W floor - B) / (1 - c) as q12lean/gen12.py computes it: hw from the regenerated
# window base (gen9.hw_from), B = sum(M.BS), c = M.cN / SA.  Writes OUTDIR/win.lean, win_report.json,
# regen.log, kappa.txt.
set -e
LB=$(cd "$(dirname "$0")/../.." && pwd)
PY=${PY:-$LB/../../.venv/bin/python}
REFIT=$(cd "$(dirname "$1")" && pwd)/$(basename "$1"); MODEL=$(cd "$(dirname "$2")" && pwd)/$(basename "$2")
mkdir -p "$3"; OUT=$(cd "$3" && pwd)
cd $LB
$PY w16/regen_window.py q9lean/work/w16_v3.lean -o $OUT/win.lean --window $REFIT --report $OUT/win_report.json --replay > $OUT/regen.log 2>&1
grep -E "ALL CHECKS|FAIL|false" $OUT/regen.log || true
cd $LB/q9lean
$PY - "$OUT/win.lean" "$MODEL" <<'EOF' | tee $OUT/kappa.txt
import pickle, sys
from fractions import Fraction
sys.path[:0] = ['.', '../q9', '../gen', '..']
import gen9
hw = gen9.hw_from(open(sys.argv[1]).read())
M = pickle.load(open(sys.argv[2], 'rb'))
SA = gen9.SA
B, cN = sum(M.BS), M.cN
k = (Fraction(hw, 10 ** 40) - Fraction(B, SA)) / (1 - Fraction(cN, SA))
print('hw', hw)
print('B', B, 'cN', cN, 'SA', SA)
print('kappa', k.numerator, '/', k.denominator)
print('kappa_float %.13f' % float(k))
EOF
