#!/bin/bash
# run_m12.sh REFIT.json OUT [NAME]   (at most 8 processes at nice 10)
#
# The whole q = 12 model build and its validation for one window, driven by the refit JSON (best_q9_j16
# format: xfree, x, eps, H, B; e.g. q12win/work/refit96_q12_pm_g18i16.json).  Steps and outputs, all in OUT:
#   1. build9 (KB 2^22, c = eps - 6e-7, zero pairs = the refit's zero-weight pairs) -> base/ (model.pkl,
#      pts.pkl, spec.json, build9.log: root cover); xio.setup -> base/{model.pkl.eng, exact.txt, root_*.box};
#      extend_model to 2^20 (PLV 21, NREG 32), no fine blocks -> x/
#   2. table minimum of F - c with far pairs to 2^20 (fmin12 table: all {1.04, 1.975}^12 patterns + 1,600
#      patterns with 2.92 gaps + 400 random) -> tmin.json, tmin.log
#   3. fine blocks: wdiag at the 40 best minima on x/, cell-lb loss of span <= 2 terms, blocks with a loss
#      > 1e-7 padded by 3, united with the fixed set 30-36, 61-66, 91-104 -> fine_final.txt
#   4. extend_model with --fine -> NAME/ (the production model: model.pkl, pts.pkl, model.pkl.eng, exact.txt,
#      root_*.box, spec.json); wd_f.out (wdiag margins at the minima on NAME/)
#   5. true minimum in mpmath (34 digits, no far rule) from the 24 best table minima -> tmp.json, tmp.log
#   6. root 4: cpp_race/xgen tree + check, pycheck -> runs/r4/
#   7. near-lattice boxes (+-64 and +-512 units around the 40 minima) and, if FAILBOXES is set, 50 boxes from
#      $FAILBOXES/r0 and $FAILBOXES/r2 (boxes that failed under a previous model), with --maxdepth 400
#      -> runs/v2d/
#   8. if EST is set: size estimate, the subtree boxes of $EST/samp.list (a leaf-uniform sample of a previous
#      model's trees, estsum.py format) rebuilt on NAME/ -> runs/samp/, est.txt (estsum.py)
set -e
REFIT=$(readlink -f $1); OUT=$(readlink -f $2); NAME=${3:-m12w}
# PY: a Python with the repo's requirements; T holds this directory's tools, with wdiag built from wdiag.cpp.
LB=$(cd "$(dirname "$0")/../.." && pwd); PY=${PY:-$LB/../../.venv/bin/python}; T=${T:-$LB/q12x/m12w}
mkdir -p $OUT && cd $OUT
log() { echo "$(date '+%F %T') $*" | tee -a $OUT/run.log; }
ZP=$($PY -c "
import json,sys
x=json.load(open(sys.argv[1]))['x']; Q=12
P=[(i,j) for i in range(Q+1) for j in range(i+1,Q+1)]
z=[p for k,p in enumerate(P) if abs(x[Q+k])<1e-12 and p<=(Q-p[1],Q-p[0])]
print(','.join('%d-%d'%p for p in z))" $REFIT)
log "start $REFIT -> $OUT/$NAME, zero pairs $ZP"

if [ ! -f x/model.pkl.eng ]; then
  (cd $LB/q9win && nice -n 10 $PY build9.py $REFIT $OUT/base --kb 4194304 --zero-pairs $ZP --workers 8 > $OUT/build9.log 2>&1)
  (cd $LB/q12x && nice -n 10 $PY -c "import sys, xio; print('roots', xio.setup(sys.argv[1] + '/model.pkl', sys.argv[1] + '/pts.pkl', sys.argv[1])[5])" $OUT/base > $OUT/setup.log 2>&1)
  (cd $LB/q12x && nice -n 10 $PY extend_model.py $OUT/base $OUT/x --workers 8 --plv 21 --nreg 32 > $OUT/extend.log 2>&1)
  rm -f base/mc.pkl x/mc.pkl
fi
log "1 model: $(grep -E '^(Q |bad seg|cN )' build9.log | tr '\n' ' ')"

[ -s tmin.json ] || nice -n 10 $PY $T/fmin12.py table base/spec.json tmin.json --starts 1600 --workers 8 > tmin.log 2>&1
log "2 table min: $(sed -n 2p tmin.log)"

$PY $T/nlboxes.py tmin.json nl --top 40 --widths 64,512 --gfile g_top40.txt
nice $T/wdiag x/model.pkl.eng g_top40.txt 0 1 2 4 16 64 > wd_x.out 2>/dev/null
$PY $T/cellloss.py base/spec.json wd_x.out --maxspan 2 --quiet --thr 1e-7 --pad 3 --fine-out fine.txt > cellloss_x.txt
FINE=$($PY -c "
s=set()
for spec in open('fine.txt').read().strip().split(',')+'30-36:2,61-66:2,91-104:2'.split(','):
    if spec:
        a,b=map(int,spec.split(':')[0].split('-')); s.update(range(a,b+1))
r=[]
for j in sorted(s):
    if r and j==r[-1][1]+1: r[-1][1]=j
    else: r.append([j,j])
print(','.join('%d-%d:2'%tuple(t) for t in r))")
echo $FINE > fine_final.txt
log "3 fine blocks: $FINE"

if [ ! -f $NAME/model.pkl.eng ]; then
  (cd $LB/q12x && nice -n 10 $PY extend_model.py $OUT/base $OUT/$NAME --workers 8 --plv 21 --nreg 32 --fine $FINE > $OUT/extend_fine.log 2>&1)
  rm -f $NAME/mc.pkl
fi
nice $T/wdiag $NAME/model.pkl.eng g_top40.txt 0 1 2 4 16 64 > wd_f.out 2>/dev/null
$PY $T/cellloss.py base/spec.json wd_f.out --maxspan 2 --quiet --thr 1e-7 > cellloss_f.txt
log "4 margins at the minima (x / $NAME): $($PY -c "
import sys
for f in sys.argv[1:]:
    v={}
    for ln in open(f):
        if ln.startswith('row'):
            t=ln.split()[3:]
            for k,x in zip(t[::2],t[1::2]): v[k]=min(v.get(k,9),float(x))
    print(' '.join('%s %.3e'%kv for kv in v.items()), end=' | ')" wd_x.out wd_f.out)"

[ -s tmp.json ] || nice -n 10 $PY $T/fmin12.py true base/spec.json $REFIT tmin.json tmp.json --top 24 > tmp.log 2>&1
log "5 true min: $(grep -E 'min F' tmp.log | tr '\n' ' ')"

echo $OUT/$NAME/root_4.box > r4.list
[ -f runs/r4/res.txt ] || $T/runboxes.sh $OUT/$NAME r4.list $OUT/runs/r4 1
nice -n 10 $PY $LB/q12x/pycheck.py $NAME/model.pkl $NAME/pts.pkl runs/r4/root_4.box runs/r4/root_4.nodes > runs/r4/pycheck.txt 2>&1
log "6 root 4: $(head -1 runs/r4/res.txt) | pycheck $(tail -1 runs/r4/pycheck.txt | cut -c1-120)"

ls $OUT/nl/*.box > v2d.list
# FAILBOXES: a directory of boxes that failed under the previous model; optional.
[ -n "${FAILBOXES:-}" ] && ls $FAILBOXES/r0/*.job $FAILBOXES/r2/*.job | shuf --random-source=<(yes) -n 50 >> v2d.list
[ -f runs/v2d/res.txt ] || $T/runboxes.sh $OUT/$NAME v2d.list $OUT/runs/v2d 8
log "7 near-lattice + old-failure boxes: $(grep -vc done runs/v2d/res.txt) boxes, rc: $(awk '$2=="rc"{print $3}' runs/v2d/res.txt | sort | uniq -c | tr '\n' ' ') checks: $(awk '$2=="rc"{print $NF}' runs/v2d/res.txt | sort | uniq -c | tr '\n' ' ')"

# EST: the size-estimate sample of the previous trees; step 8 is skipped without it.
if [ -n "${EST:-}" ]; then
  [ -f runs/samp/res.txt ] || $T/runboxes.sh $OUT/$NAME $EST/samp.list $OUT/runs/samp 8
  $PY $T/estsum.py $EST runs/samp/res.txt > est.txt
  log "8 size estimate: $(grep -E '^total|^sampled' est.txt | tr '\n' ' ')"
fi
(cd $NAME && md5sum model.pkl pts.pkl model.pkl.eng exact.txt root_*.box spec.json > MD5SUMS)
log "done; md5s in $OUT/$NAME/MD5SUMS"
