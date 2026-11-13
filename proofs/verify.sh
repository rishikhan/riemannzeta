#!/usr/bin/env bash
# Build and check one generated Lean proof.
#
#   bash proofs/verify.sh q10              # build; check axioms; print the statements
#   bash proofs/verify.sh q10 --deep       # also: lean4export, nanoda, parallel Lean kernel replay
#   bash proofs/verify.sh q10 --compare    # also: the challenge's comparator against its templates
#
# Proofs: q9 (the riemannzeta.fun entry), q10, q11, q12 (Theorem 1.2). Run proofs/fetch.sh first.
# Needs elan (https://github.com/leanprover/elan); --deep and --compare also need git and cargo.
# THREADS (default 8) sets LEAN_NUM_THREADS for the build and the thread count of nanoda and the
# replay. Each archive's logs/ gives the time and memory of the run of record.
#
# Before building, the script regenerates the trusted statement layer (ChallengeDeps/CandidateSpec,
# Challenge.Candidate and PrintAxioms.Candidate) from proofs/templates and the κ in
# proofs/archives.tsv, so the statements come from this repository, not from the archive.
set -euo pipefail
q=${1:?usage: verify.sh q9|q10|q11|q12 [--deep] [--compare]}; shift
deep=0; compare=0
for a in "$@"; do case "$a" in --deep) deep=1 ;; --compare) compare=1 ;; *) echo "unknown option $a" >&2; exit 2 ;; esac; done
here=$(cd "$(dirname "$0")" && pwd)
ws="$here/$q/ws"; out="$here/$q/check"
[ -d "$ws" ] || { echo "proofs/$q/ws is missing; run proofs/fetch.sh $q" >&2; exit 1; }
THREADS=${THREADS:-8}
mkdir -p "$out"

# The record the challenge held when these proofs were built (attempt ajp88-ra-window-nine-point).
RECORD='(1669044344675499575055516274525441801367 : ℝ) / 2477793188117925391575000000000000000000'
line=$(awk -F'\t' -v q="$q" '$1 == q' "$here/archives.tsv")
num=$(cut -f5 <<<"$line"); den=$(cut -f6 <<<"$line")
[ -n "$num" ] && [ -n "$den" ] || { echo "no κ for $q in archives.tsv" >&2; exit 1; }

# The three statements of the challenge template, and the two N0simple statements of the
# generated proofs (q10..q12 only); and the only axioms any of them may use.
tnames="candidate_strict_improvement candidate_critical_line_bound candidate_critical_line_bound_cumulative"
axioms="[propext, Classical.choice, Quot.sound]"
if [ "$q" = q9 ]; then
  module=Solution.Candidate; names=$tnames
  # The solution file has #print axioms for the three theorems near its end, before a license notice.
  targets="Solution.Candidate"; axfile="comparator/Solution/Candidate.lean"
else
  lib=Q${q#q}; module=$lib.Simple
  names="$tnames candidate_simple_critical_line_bound candidate_simple_critical_line_bound_cumulative"
  # q12's root module imports only $lib.Final, so name $lib.Simple explicitly.
  targets="$lib $lib.Simple"; axfile="$lib/Simple.lean"
fi

# ---- trusted statement layer, from proofs/templates
c="$ws/comparator"
spec=$(RECORD="$RECORD" NUM="$num" DEN="$den" perl -0pe \
  's/\{\{CURRENT_EXPRESSION\}\}/$ENV{RECORD}/; s/\{\{NUMERATOR\}\}/$ENV{NUM}/; s/\{\{DENOMINATOR\}\}/$ENV{DEN}/;' \
  "$here/templates/CandidateSpec.lean.tmpl")
if [ "$spec" != "$(cat "$c/ChallengeDeps/CandidateSpec.lean")" ]; then
  echo "NOTE: the archive's CandidateSpec.lean differs from the template; replacing it"
  printf '%s\n' "$spec" > "$c/ChallengeDeps/CandidateSpec.lean"
fi
mkdir -p "$c/Challenge" "$c/PrintAxioms"
cp "$here/templates/Challenge.Candidate.lean" "$c/Challenge/Candidate.lean"
cp "$here/templates/PrintAxioms.Candidate.lean" "$c/PrintAxioms/Candidate.lean"
echo "candidateKappa = $num / $den"

# ---- build and axioms
echo "== build $targets (logs: proofs/$q/check/)"
cd "$ws"
lake exe cache get > "$out/cache.log" 2>&1
# The base module first: it is the largest single file, and building it alone keeps peak memory down.
[ "$q" = q9 ] || LEAN_NUM_THREADS=2 lake build "$lib.Base" > "$out/build_base.log" 2>&1
LEAN_NUM_THREADS=$THREADS lake build $targets > "$out/build.log" 2>&1
if grep "declaration uses 'sorry'" "$out/build.log" | grep -vq "comparator/Challenge/"; then
  echo "FAIL: the build reports sorry" >&2; exit 1
fi
for n in $names; do
  l=$(grep -E "${axfile//./\\.}:.*'$n' depends on axioms" "$out/build.log" | head -1 || true)
  [ -n "$l" ] || { echo "FAIL: no #print axioms line for $n" >&2; exit 1; }
  case "$l" in *"depends on axioms: $axioms") echo "  $n: $axioms" ;;
    *) echo "FAIL: $l" >&2; exit 1 ;; esac
done
echo "PASS build: every headline theorem depends only on $axioms"
echo "  (every generated module sets debug.skipKernelTC, so the build does not run the kernel; --deep and --compare do)"

# The statements as Lean elaborates them, for reading against the paper.
{ echo "import $module"; echo "set_option pp.proofs false"
  for n in $names; do echo "#check @$n"; done
  echo "#print candidateKappa"; } > "$out/Statements.lean"
lake env lean "$out/Statements.lean" > "$out/statements.txt" 2>&1 || { echo "FAIL: printing the statements" >&2; exit 1; }
echo "  statements: proofs/$q/check/statements.txt"

[ $deep = 1 ] || [ $compare = 1 ] || exit 0

# ---- tools, at the versions the riemannzeta.fun verifier pins
T="$here/.tools"; mkdir -p "$T"
if [ ! -x "$T/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export" ] || [ ! -x "$T/comparator/.lake/build/bin/comparator" ]; then
  echo "== build comparator 2732944 (lean4export b18d673) under the proof's toolchain"
  rm -rf "$T/comparator"
  git clone -q https://github.com/leanprover/comparator.git "$T/comparator"
  git -C "$T/comparator" checkout -q 273294467ce06429e6667ece7f5699f8678c9f4e
  cp "$ws/lean-toolchain" "$T/comparator/lean-toolchain"
  # lean4export (the exporter) and Export.Parse (which PReplay.lean imports) are not default targets.
  (cd "$T/comparator" && lake build comparator lean4export Export.Parse > "$T/comparator_build.log" 2>&1)
fi
if [ ! -x "$T/nanoda/target/release/nanoda_bin" ]; then
  echo "== build nanoda 4183202"
  rm -rf "$T/nanoda"
  git clone -q https://github.com/ammkrn/nanoda_lib.git "$T/nanoda"
  git -C "$T/nanoda" checkout -q 418320295890faed83a96fd97907b12a3b6728c2
  (cd "$T/nanoda" && cargo build --release > "$T/nanoda_build.log" 2>&1)
fi
lean4export="$T/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
nanoda="$T/nanoda/target/release/nanoda_bin"

if [ $deep = 1 ]; then
  echo "== export $module"
  lake env "$lean4export" "$module" -- $names > "$out/export" 2> "$out/export.err"
  echo "== nanoda"
  cat > "$out/nanoda.json" <<EOF
{"use_stdin":true,"permitted_axioms":["propext","Quot.sound","Classical.choice"],"unpermitted_axiom_hard_error":true,"nat_extension":true,"string_extension":true,"num_threads":$THREADS}
EOF
  "$nanoda" "$out/nanoda.json" < "$out/export" > "$out/nanoda.log" 2>&1 \
    || { echo "FAIL: nanoda (proofs/$q/check/nanoda.log)" >&2; exit 1; }
  echo "PASS nanoda"
  echo "== Lean kernel replay"
  (cd "$T/comparator" && lake env lean --run "$here/../src/lbcert/q12lean/kreplay/PReplay.lean" "$out/export" 40 "$THREADS") \
    > "$out/preplay.log" 2>&1 || true
  grep -q "PARALLEL REPLAY OK" "$out/preplay.log" \
    || { echo "FAIL: replay (proofs/$q/check/preplay.log)" >&2; exit 1; }
  echo "PASS replay: $(grep -o 'checked [0-9]*, rejected [0-9]*' "$out/preplay.log")"
fi

if [ $compare = 1 ]; then
  # The hosted check: the comparator builds Challenge.Candidate and the solution, exports both,
  # checks that each template theorem has the template's statement and permitted axioms only, and
  # runs nanoda and the Lean kernel on the solution. Both kernels run single-threaded here.
  echo "== comparator: $module against Challenge.Candidate"
  cat > "$c/config-check.json" <<EOF
{"challenge_module": "Challenge.Candidate", "solution_module": "$module",
 "theorem_names": ["candidate_strict_improvement", "candidate_critical_line_bound", "candidate_critical_line_bound_cumulative"],
 "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": true}
EOF
  # The hosted verifier runs each child under landrun, a sandbox. This shim runs it directly,
  # passing only the environment variables landrun would.
  cat > "$T/landrun" <<'EOF'
#!/usr/bin/env bash
envs=()
while [[ $# -gt 0 && "$1" != "--" ]]; do
  case "$1" in
    --env) k="$2"; shift 2
           if [[ "$k" == *=* ]]; then envs+=("$k"); elif [[ -v $k ]]; then envs+=("$k=${!k}"); fi ;;
    --ro|--rw|--rwx|--rox) shift 2 ;;
    *) shift ;;
  esac
done
shift
exec env -i "${envs[@]}" "$@"
EOF
  chmod +x "$T/landrun"
  COMPARATOR_LANDRUN="$T/landrun" COMPARATOR_LEAN4EXPORT="$lean4export" COMPARATOR_NANODA="$nanoda" \
    lake env "$T/comparator/.lake/build/bin/comparator" comparator/config-check.json > "$out/comparator.log" 2>&1 || true
  grep -q "Your solution is okay!" "$out/comparator.log" \
    || { echo "FAIL: comparator (proofs/$q/check/comparator.log)" >&2; exit 1; }
  echo "PASS comparator: $(grep -E 'accepts the solution' "$out/comparator.log" | tr '\n' ' ')"
fi
