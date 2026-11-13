#!/bin/bash
# runboxes.sh MODEL_DIR LIST OUTDIR [P]: xgen tree --maxdepth 400 on every box file in LIST (one path per
# line; a box trailer " M ..." is stripped), P processes at nice 10; then xgen check on each tree.
# XGEN: the binary (default ../cpp_race/xgen).
# OUTDIR/<name>.nodes, OUTDIR/res.txt: "name rc leaves refl fails maxdepth user_s check".
W=$1; LIST=$2; OUT=$3; P=${4:-8}
X=${XGEN:-$(cd "$(dirname "$0")/../cpp_race" && pwd)/xgen}
mkdir -p $OUT
one() {
  b=$1; n=$(basename $b .box); n=${n%.job}
  sed "s/ M .*//" $b > $OUT/$n.box
  /usr/bin/time -f "%U" -o $OUT/$n.time nice -n 10 $X tree $W/model.pkl.eng $W/exact.txt $OUT/$n.box $OUT/$n.nodes --maxdepth 400 > $OUT/$n.out 2>&1
  rc=$?
  st=$(grep "^# rc" $OUT/$n.nodes 2>/dev/null | head -1)
  ck=$(nice -n 10 $X check $W/model.pkl.eng $W/exact.txt $OUT/$n.box $OUT/$n.nodes 2>/dev/null | grep "^# check" | awk "{print \$3\"/bad\"\$14}")
  echo "$n rc $rc $(echo $st | awk "{print \$5, \$7, \$11, \$13}") $(cat $OUT/$n.time | tail -1) $ck"
}
export -f one; export W OUT X
xargs -P $P -I{} bash -c "one {}" < $LIST > $OUT/res.txt
echo done >> $OUT/res.txt
