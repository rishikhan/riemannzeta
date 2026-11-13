#!/bin/bash
# q12x subtree jobs on Perlmutter CPU nodes, one 30-minute debug job at a time (resumable).
#
#   ROOTS=0,2 sbatch -N 8 nersc/q12x.sbatch            # one job
#   ROOTS=0,2 CHAIN=1 sbatch -N 8 nersc/q12x.sbatch    # the job queues its own successor at start
#   ROOTS=0 FRONTIER_ONLY=1 sbatch -N 1 nersc/q12x.sbatch  # only the top frontier (then exit)
#   XGEN=.../xgen_race XOPTS="--race-stall 0 --race-cap 300" XG_CACHE=16000 ...  # per-box policy racing
#
# Steps: (1) the top frontier of every root in ROOTS that lacks one (run_root.py --frontier-only,
# --fthreads = all hardware threads, roots in parallel on different nodes); (2) one qrun.py per node
# (shared dynamic queue over ROOTS through claim files), stopped DEADLINE_MARGIN seconds before the job's
# end so that xgen is terminated by qrun, not by Slurm.  STEAL=1 (default): running
# jobs donate pending boxes whenever slots are idle, and at the deadline every xgen hands its unstarted
# boxes back to the queue and exits cleanly, so nothing is lost (no budget, no presplit).  STEAL=0: the
# old budget / resplit scheme, where the jobs in progress at the deadline are lost.
# Afterwards: run_root.py WORK k --check [--pycheck] assembles and checks a finished root.
# CHAIN=1: at start the job submits a copy of itself that depends on this one (afterany); it stops
# chaining when every root has top.nodes and no pending job, or when WORK/STOP exists.
#SBATCH -q debug
#SBATCH -C cpu
#SBATCH -A <account>
#SBATCH -t 00:30:00
#SBATCH -J q12x
#SBATCH -o q12x-%j.out
set -u
Q=${Q:-$SCRATCH/q12x}
SRC=${SRC:-$Q/src/lbcert/q12x}
PY=${PY:-$Q/venv/bin/python}
STEAL=${STEAL:-1}               # work stealing + deadline hand-off; 0 = budget / resplit
XGEN=${XGEN:-$SRC/cpp_race/xgen}
WORK=${WORK:-$Q/work/m12r}
ROOTS=${ROOTS:?set ROOTS, e.g. ROOTS=0,2}
PROCS=${PROCS:-128}            # xgen processes per node (256 = one per hardware thread)
FDEPTH=${FDEPTH:-12}           # top frontier depth (sequential, threaded); deep enough for >= 3-4 jobs per slot
if [ "$STEAL" = 1 ]; then d_pre=0; d_bud=0; else d_pre=3; d_bud=100; fi
PRESPLIT=${PRESPLIT:-$d_pre}   # each top job first runs as a depth-PRESPLIT frontier (0 = off; single-threaded)
BUDGET=${BUDGET:-$d_bud}       # leaves per job before it is resplit (STEAL=1: handed off; 0 = no limit)
TAIL_THREADS=${TAIL_THREADS:-8}  # STEAL=1: scan threads for jobs started when donation cannot fill the slots
RDEPTH=${RDEPTH:-4}            # resplit frontier depth
OPTS=${OPTS:-}                 # extra xgen options (default k = 3)
XOPTS=${XOPTS:-}               # appended to OPTS, e.g. racing with cpp_race/xgen: "--race-stall 0 --race-cap 300"
AOPTS="$OPTS${XOPTS:+ $XOPTS}"   # all xgen options (OPTS itself stays as given, for CHAIN)
[ -n "${XG_CACHE:-}" ] && export XG_CACHE   # xgen scan-cache size (racing: 16000); inherited by every xgen
[ -n "${XG_FAILSCAN:-}" ] && export XG_FAILSCAN   # 1: a failed leaf certificate splits by the scan (cpp_race/xgen)
DEADLINE_MARGIN=${DEADLINE_MARGIN:-60}
NTH=$(nproc --all)

end=$(squeue -h -j "$SLURM_JOB_ID" -o %e)
deadline=$(( $(date -d "$end" +%s) - DEADLINE_MARGIN ))
echo "job $SLURM_JOB_ID nodes $SLURM_NNODES ($SLURM_JOB_NODELIST) roots $ROOTS procs $PROCS fdepth $FDEPTH presplit $PRESPLIT budget $BUDGET steal $STEAL end $end"
echo "xgen $XGEN opts [$AOPTS] XG_CACHE ${XG_CACHE:-unset} XG_FAILSCAN ${XG_FAILSCAN:-unset}"

todo() {   # prints the number of pending jobs over ROOTS (a root without a frontier counts as 1)
  $PY - "$WORK" "$ROOTS" <<'EOF'
import os, sys
W, roots = sys.argv[1], [int(x) for x in sys.argv[2].split(',')]
def pend(R, jid):
    out, sub = os.path.join(R, 'job_%s.nodes' % jid), os.path.join(R, 'job_%s.jobs' % jid)
    if not os.path.exists(out):
        return 0 if os.path.exists(os.path.join(R, 'failed', jid + '.job')) else 1
    return sum(pend(R, '%s.%s' % (jid, ln.split()[0])) for ln in open(sub)) if os.path.exists(sub) else 0
n = 0
for k in roots:
    R = os.path.join(W, 'r%d' % k)
    if not os.path.exists(os.path.join(R, 'top.nodes')):
        n += 1
    else:
        n += sum(pend(R, ln.split()[0]) for ln in open(os.path.join(R, 'jobs.txt')))
print(n)
EOF
}

if [ "${CHAIN:-0}" = 1 ] && [ ! -e "$WORK/STOP" ] && [ "$(todo)" -gt 0 ]; then
  next=$(sbatch --parsable -N "$SLURM_NNODES" --dependency=afterany:"$SLURM_JOB_ID" \
         --export=ALL,ROOTS="$ROOTS",CHAIN=1 "$SRC/nersc/q12x.sbatch")
  echo "queued successor $next"
fi

# (1) missing top frontiers, one root per node in parallel
i=0
for k in ${ROOTS//,/ }; do
  if [ ! -e "$WORK/r$k/top.nodes" ]; then
    echo "frontier root $k depth $FDEPTH start $(date +%T)"
    timeout --signal=TERM $(( deadline - $(date +%s) )) \
      srun -N 1 -n 1 -c "$NTH" --cpu-bind=none --exact \
      $PY "$SRC/run_root.py" "$WORK" "$k" --frontier-only --depth "$FDEPTH" --fthreads "$NTH" --xgen "$XGEN" --opts="$AOPTS" &
    i=$((i + 1))
    if [ "$i" -ge "$SLURM_NNODES" ]; then wait; i=0; fi
  fi
done
wait
echo "frontiers done $(date +%T)"
[ "${FRONTIER_ONLY:-0}" = 1 ] && exit 0

# (2) workers: one qrun per node
steal=(); [ "$STEAL" = 1 ] && steal=(--steal --tail-threads "$TAIL_THREADS")
srun -N "$SLURM_NNODES" --ntasks-per-node=1 -c "$NTH" --cpu-bind=none \
  $PY "$SRC/nersc/qrun.py" "$WORK" "$ROOTS" --procs "$PROCS" --xgen "$XGEN" --opts="$AOPTS" \
  --budget "$BUDGET" --resplit-depth "$RDEPTH" --presplit-depth "$PRESPLIT" --deadline "$deadline" ${steal[@]+"${steal[@]}"}
echo "workers done $(date +%T); pending jobs: $(todo)"
