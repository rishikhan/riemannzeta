#!/bin/bash
#SBATCH -A <account>
#SBATCH -q debug
#SBATCH -C cpu
#SBATCH -N 8
#SBATCH -t 00:30:00
#SBATCH -J q12cma
#SBATCH --dependency=singleton
#SBATCH -o logs/%j.out
# 6 pm_worker.py slots per node, 42 threads each, unbound (2x oversubscribed on physical cores); the driver runs on the login node.
B=${B:-$SCRATCH/q12win}         # holds repo/ (this repository), venv/, bin/ and run/
RUN=${RUN:-$B/run/cma}
export GMIN12LP_BINDIR=$B/bin PIPELINE_BINDIR=$B/bin PIPELINE_CXX=g++ CXX=g++
DEADLINE=$(( $(date +%s) + 30 * 60 - 45 ))
cd $B/repo/src/lbcert/q12win
srun --ntasks-per-node=6 -c 42 --cpu-bind=none $B/venv/bin/python pm_worker.py \
    --run $RUN --threads 42 --deadline $DEADLINE --est ${EST:-240}
