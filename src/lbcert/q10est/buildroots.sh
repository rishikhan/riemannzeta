#!/bin/bash
# buildroots.sh MODEL_DIR OUTDIR P ROOTS...: xgen tree (production options) on whole roots, P processes at nice 10,
# then xgen check. OUTDIR/res.txt: "root rc <rc line fields> user_s wall_s check".
W=$1; OUT=$2; P=$3; shift 3
X=${XGEN:-$(cd "$(dirname "$0")/../q12x/cpp_race" && pwd)/xgen}
export XG_FAILSCAN=1 XG_WIDE=4 XG_WIDE_NARROW=0.01 XG_WIDTHFIX=1 XG_CACHE=16000
mkdir -p $OUT
one() {
  r=$1
  /usr/bin/time -f "%U %e" -o $OUT/r$r.time nice -n 10 $X tree $W/model.pkl.eng $W/exact.txt $W/root_$r.box $OUT/r$r.nodes --maxdepth 400 --race-stall 0 --race-cap 300 > $OUT/r$r.out 2>&1
  rc=$?
  ck=$(nice -n 10 $X check $W/model.pkl.eng $W/exact.txt $W/root_$r.box $OUT/r$r.nodes 2>/dev/null | grep "^# check" | head -1)
  echo "$r rc $rc $(grep "^# rc" $OUT/r$r.nodes | head -1) | $(cat $OUT/r$r.time) | $ck"
}
export -f one; export W OUT X
printf "%s\n" "$@" | xargs -P $P -I{} bash -c "one {}" > $OUT/res.txt
echo done >> $OUT/res.txt
