# src/lbcert: the generator of the Lean proofs

This directory holds the code that produced the Lean proofs in `proofs/`: the window search,
the model and tree build, and the Lean emission. It is the research code as it ran. The proofs
are checked from the archived Lean sources (`proofs/verify.sh`), so nothing
here is trusted. A tree or model error makes the Lean build fail.

The q = 10 code here is the copy that generated the q = 10 proof, except for default paths of
helper files and binaries, and it regenerates that proof's Lean source byte for byte. For q = 12,
`q12lean/gen12.py` gained the `--lib` option and the `Q`-dependent widths after the q = 12 run.
Its q = 12 output is unchanged by them.

## Builds

- `q12x/cpp_race`: `xgen`, the exact tree builder and checker (C++, HiGHS 1.11 and GMP):
  `make -C q12x/cpp_race xgen HIGHS=<prefix> GMP=<prefix>`. Its sources (`xgen.cpp` md5
  `8c8177e7`) built the trees of all three proofs.
- `gen/cpp` and `q12/cpp`: `libengine`, the leaf LP engine the Python side loads through ctypes:
  `make -C gen/cpp HIGHS=<prefix>` and `make -C q12/cpp HIGHS=<prefix> GMP=<prefix>`.
- `q12x/m12w/wdiag.cpp`: the margin diagnostic `run_m12.sh` calls; its header gives the build.
- `q12/gmin12_cpp`: the streaming minimizer with the cut-model LP that the window objective
  (`q12/cert12.py`) runs. `stream.py` compiles it on first use against `HIGHS_PREFIX`, a
  HiGHS 1.12 install, into `q12/gmin12_cpp/bin` (`GMIN12LP_BINDIR` overrides it).
- `pipeline/cppgmin.py` compiles `pipeline/cpp/*.cpp` on first use into `/tmp/pipeline_bin`
  (`PIPELINE_BINDIR` and `PIPELINE_CXX` override the directory and the compiler).

The builds write their binaries next to their sources; `.gitignore` lists them. Python needs the
repository's `requirements.txt`. `run_m12.sh` and `run_m10.sh` run 8 worker processes. `third_party/` holds the two
Apache-2.0 sources the Lean emission copies checker code from (`A031`, `A032` override their
paths).

## Steps, window to Lean source

1. **Window.** `q12win/cma12.py` runs CMA-ES over the window coefficients, scoring each window by
   a refit of the weights warm-started from earlier rounds (`winobj.evaluate`). `pm_driver.py`, `pm_worker.py` and
   `pm_job.sh` spread the evaluations over Perlmutter nodes. `val96.py` refits chosen windows at
   96 rounds. The windows of the paper are `q12win/work/final2_q12.json` (q = 12, the main
   theorem), `final_q11.json` and `final_q10.json`, with the refits
   `q12win/work/refit96_q12_pm_g18i16.json`, `refit96_q11_g20i2.json` and
   `refit96_q10_g41i7.json`. `src/sep_conditions_cert.py` certifies their
   window conditions.
2. **Window Lean and κ.** `q12x/m12w/lean_kappa.sh REFIT MODEL OUT` regenerates the window
   declarations from the template `q9lean/work/w16_v3.lean` (`w16/regen_window.py`) and
   computes the exact κ.
3. **Model.** `q12x/m12w/run_m12.sh REFIT OUT NAME` (q = 12) and `q10est/run_m10.sh REFIT OUT
   NAME` (q = 10, 11) build the certificate model: weights quantized at end-gap floor 2^22,
   c = ε − 6·10⁻⁷, fine blocks where the leaf margin is small, then the table minimum and
   diagnostics. build9 logs `pv error AttributeError(...)`: its positive-variation replay is
   written for 12 window harmonics, and `lean_kappa.sh` runs the 16-harmonic window checks.
   `q9win/build9.py` starts from `gen/work/v2/model.pkl` (sha256
   `ae9676cc…74d0`, built by `gen/build_model.py` from attempt-031).
4. **Trees.** `xgen tree` per root with `XG_FAILSCAN=1 XG_WIDE=4 XG_WIDE_NARROW=0.01
   XG_WIDTHFIX=1 XG_CACHE=16000` and `--maxdepth 400 --race-stall 0 --race-cap 300`. q = 12 ran
   on Perlmutter through `q12x/nersc/q12x.sbatch` and `q12x/nersc/qrun.py`, assembled with
   `q12x/run_root.py WORK k --check`. q = 10 and 11 ran with `q10est/buildroots.sh` and
   `q11trees/buildtree.py`.
5. **Table and checks.** `q12x/finalize.py WORK --roots 0,...,8 --par --procs 10` selects the
   shared tangent-point table and writes `trees.pkl` and `table.lean.txt`. `xgen check` and
   `q12x/pycheck_par.py` check every tree exactly against the table.
6. **Lean source.** From `q12lean/`:

       gen12.py WIN.lean WORK/model.pkl WORK/pts.pkl OUT --trees WORK/trees.pkl \
         --ptn WORK/table.lean.txt --fast --cut-leaves 400 --super-leaves 20000 \
         --module-leaves 20000 --nest-leaves 400 --procs 4 --lib Q12 --date 2026-10-26

   writes the library `OUT/Q12` (base module, data modules, `Final.lean`, `Simple.lean`). The
   q = 10 and 11 runs used `--lib Q10` / `--lib Q11` and `--date 2026-10-27`.
7. **Build and check.** The archives in `proofs/` hold each library in a workspace of
   anthropics/zeta-23-lean with the challenge's comparator layer. `proofs/verify.sh` builds and
   checks it. `q12lean/kreplay/PReplay.lean` is the parallel Lean kernel replay it runs.

## The q = 9 entry

The q = 9 proof is the riemannzeta.fun entry. Its model, point set, trees, range-coded walk
words and tangent-point table are shipped under `q9/work/q9a/` and `q9sparse/work/`, so the
entry regenerates from the window in 10 to 20 seconds. From the repository root:

    L=src/lbcert; O=results/rerun/q9; mkdir -p $O
    python $L/w16/regen_window.py $L/q9lean/work/w16_v3.lean -o $O/win_q9.lean \
      --window results/sepsearch/best_q9_j16.json
    python $L/q9lean/gen9.py $O/win_q9.lean $L/q9/work/q9a/full9/model.pkl $L/q9/work/q9a/pts.pkl \
      $O/full_ZF.lean --trees $L/q9sparse/work/z_F_trees.pkl --eformat $L/q9sparse/work/e_F/wl.txt \
      --kfmt --cut-leaves 400 --opt gsplit --opt yrow --opt helpers --opt notn --opt adjlam \
      --opt sparse --ptn $L/q9sparse/work/milp/hull_final.txt --prune $L/q9lean/dead/removed.names --pack
    python $L/q9lean/postfix.py $O/full_ZF.lean $O/Solution_Z.lean --sparse --ptn 4701
    python $L/q9lean/skip.py $O/Solution_Z.lean $O/Solution_Zskip.lean

`$O/Solution_Zskip.lean` has SHA-256 `af26b6bb7f217c329f9223318f710055437090e2187f934791212100228d696c`,
the hash of `q9/ws/comparator/Solution/Candidate.lean` in the q9 archive. `gen9.py` reads attempt-032 from
`third_party/` and checks its hash. `postfix.py` renames the decoder namespace and adds the
dated Changes lines. `skip.py` adds `set_option debug.skipKernelTC true`.
