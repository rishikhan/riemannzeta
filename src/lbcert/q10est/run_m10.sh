#!/bin/bash
# run_m10.sh REFIT.json OUT [NAME]: q12x/m12w/run_m12.sh steps 1-5 with Q read from the refit (FQ for the
# Q-parametrized copies of fmin12.py / nlboxes.py in this directory). Same model recipe: build9 KB 2^22,
# c = eps - 6e-7, zero pairs = refit zero-weight pairs; setup; extend (PLV 21, NREG 32); table min; fine blocks
# (union with the fixed set); extend --fine; wdiag; mpmath true min.  No root tree and no size sample.
set -e
REFIT=$(readlink -f $1); OUT=$(readlink -f $2); NAME=${3:-m10w}
# PY: a Python with the repo's requirements; T12 holds q12x/m12w's tools, with wdiag built from wdiag.cpp.
LB=$(cd "$(dirname "$0")/.." && pwd); PY=${PY:-$LB/../../.venv/bin/python}; T=${T:-$LB/q10est/qtools}; T12=${T12:-$LB/q12x/m12w}
mkdir -p $OUT && cd $OUT
log() { echo "$(date "+%F %T") $*" | tee -a $OUT/run.log; }
export FQ=$($PY -c "
import json,sys
x=json.load(open(sys.argv[1]))[\"x\"]; print(next(q for q in range(2,20) if q+q*(q+1)//2==len(x)))" $REFIT)
ZP=$($PY -c "
import json,sys
x=json.load(open(sys.argv[1]))[\"x\"]; Q=int(sys.argv[2])
P=[(i,j) for i in range(Q+1) for j in range(i+1,Q+1)]
z=[p for k,p in enumerate(P) if abs(x[Q+k])<1e-12 and p<=(Q-p[1],Q-p[0])]
print(\",\".join(\"%d-%d\"%p for p in z))" $REFIT $FQ)
log "start $REFIT -> $OUT/$NAME, Q $FQ, zero pairs $ZP"
if [ ! -f x/model.pkl.eng ]; then
  (cd $LB/q9win && nice -n 10 $PY build9.py $REFIT $OUT/base --kb 4194304 --zero-pairs $ZP --workers 8 > $OUT/build9.log 2>&1)
  (cd $LB/q12x && nice -n 10 $PY -c "import sys, xio; print(\"roots\", xio.setup(sys.argv[1] + \"/model.pkl\", sys.argv[1] + \"/pts.pkl\", sys.argv[1])[5])" $OUT/base > $OUT/setup.log 2>&1)
  (cd $LB/q12x && nice -n 10 $PY extend_model.py $OUT/base $OUT/x --workers 8 --plv 21 --nreg 32 > $OUT/extend.log 2>&1)
  rm -f base/mc.pkl x/mc.pkl
fi
log "1 model: $(grep -E "^(Q |bad seg|cN )" build9.log | tr "\n" " ")"
[ -s tmin.json ] || nice -n 10 $PY $T/fmin12.py table base/spec.json tmin.json --starts 1600 --workers 8 > tmin.log 2>&1
log "2 table min: $(sed -n 2p tmin.log)"
$PY $T/nlboxes.py tmin.json nl --top 40 --widths 64,512 --gfile g_top40.txt
nice $T12/wdiag x/model.pkl.eng g_top40.txt 0 1 2 4 16 64 > wd_x.out 2>/dev/null
(cd $T && $PY cellloss.py $OUT/base/spec.json $OUT/wd_x.out --maxspan 2 --quiet --thr 1e-7 --pad 3 --fine-out $OUT/fine.txt > $OUT/cellloss_x.txt)
FINE=$($PY -c "
s=set()
for spec in open(\"fine.txt\").read().strip().split(\",\")+\"30-36:2,61-66:2,91-104:2\".split(\",\"):
    if spec:
        a,b=map(int,spec.split(\":\")[0].split(\"-\")); s.update(range(a,b+1))
r=[]
for j in sorted(s):
    if r and j==r[-1][1]+1: r[-1][1]=j
    else: r.append([j,j])
print(\",\".join(\"%d-%d:2\"%tuple(t) for t in r))")
echo $FINE > fine_final.txt
log "3 fine blocks: $FINE"
if [ ! -f $NAME/model.pkl.eng ]; then
  (cd $LB/q12x && nice -n 10 $PY extend_model.py $OUT/base $OUT/$NAME --workers 8 --plv 21 --nreg 32 --fine $FINE > $OUT/extend_fine.log 2>&1)
  rm -f $NAME/mc.pkl
fi
nice $T12/wdiag $NAME/model.pkl.eng g_top40.txt 0 1 2 4 16 64 > wd_f.out 2>/dev/null
log "4 margins at the minima (x / $NAME): $($PY -c "
import sys
for f in sys.argv[1:]:
    v={}
    for ln in open(f):
        if ln.startswith(\"row\"):
            t=ln.split()[3:]
            for k,x in zip(t[::2],t[1::2]): v[k]=min(v.get(k,9),float(x))
    print(\" \".join(\"%s %.3e\"%kv for kv in v.items()), end=\" | \")" wd_x.out wd_f.out)"
[ -s tmp.json ] || nice -n 10 $PY $T/fmin12.py true base/spec.json $REFIT tmin.json tmp.json --top 24 > tmp.log 2>&1
log "5 true min: $(grep -E "min F" tmp.log | tr "\n" " ")"
(cd $NAME && md5sum model.pkl pts.pkl model.pkl.eng exact.txt root_*.box spec.json > MD5SUMS)
log "done; md5s in $OUT/$NAME/MD5SUMS"
