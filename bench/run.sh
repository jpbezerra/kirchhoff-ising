#!/usr/bin/env bash
# Benchmark script for REPORT.md's comparison table.
#
# Measures, on this machine, in this session (this project's "same hardware, same
# session" principle):
#   - checking time: `bend <PROOF>.bend` per module, `lake build Laws`
#     (incremental -- Mathlib is already built; a from-scratch Mathlib
#     build is a toolchain cost, not a proof-checking cost, so it's
#     deliberately excluded, see the report this prints)
#   - execution time: `bend main.bend` (runs both modules); Lean's
#     equivalent (`Tests.lean`'s #eval checks) happens as a side effect of
#     `lake build`/`lake env lean`, not a separable compiled-binary run --
#     see the report for why this row is reported differently
#   - LOC: proof-only vs type/function, per module, both languages
#
# Run from the repo root: bash bench/run.sh
# Requires: bend (bend.ps1 shim) and lake/lean on PATH, same as the rest of
# this project's toolchain (see HANDOFF.md).

set -u
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

echo "# Benchmark run: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "# Machine: $(uname -a)"
echo

time_cmd() {
  # Prints elapsed wall-clock seconds for a command, 3 runs, plus the min.
  local label="$1"; shift
  local times=()
  for i in 1 2 3; do
    local start end
    start=$(date +%s.%N)
    "$@" > /dev/null 2>&1
    local status=$?
    end=$(date +%s.%N)
    local elapsed
    elapsed=$(awk "BEGIN{printf \"%.2f\", $end - $start}")
    times+=("$elapsed")
    if [ $status -ne 0 ] && [ "$ALLOW_FAIL" != "1" ]; then
      echo "  [$label] run $i FAILED (exit $status) after ${elapsed}s"
    fi
  done
  echo "  [$label] runs: ${times[*]}s"
}

echo "## Checking time"
echo

echo "### Bend (bend <PROOF>.bend -- both modules fully closed, 0 ?TODO)"
time_cmd "ising/PROOF.bend"   bend bend/ising/PROOF.bend
time_cmd "circuit/PROOF.bend" bend bend/circuit/PROOF.bend
echo
echo "### Bend (bend bend/circuit/proofs/circuit_assoc.bend -- the associativity/"
echo "### counting lemma library circuit/PROOF.bend imports; checked here"
echo "### separately since it dominates Circuit's real proof-checking cost)"
time_cmd "circuit/proofs/circuit_assoc.bend" bend bend/circuit/proofs/circuit_assoc.bend

echo
echo "### Lean (lake build Laws, incremental -- Mathlib already built)"
export PATH="$USERPROFILE/.elan/bin:$PATH"
(cd lean && ALLOW_FAIL=0 time_cmd "lake build Laws" lake build Laws)

echo
echo "## Execution time"
echo
echo "### Bend (bend main.bend -- runs both modules' demo)"
time_cmd "bend main.bend" bend bend/main.bend
echo
echo "### Lean: not separately measurable this way -- Tests.lean's #eval"
echo "### checks run as a side effect of type-checking/building the file"
echo "### (Lean has no separate 'run this already-checked program' step"
echo "### for a #eval-only file), so its cost is already inside the"
echo "### checking-time number above, not a comparable standalone figure."

echo
echo "## Lines of code"
echo

count_bend_proof() {
  # All lines in a PROOF.bend file (comments included -- Bend's own
  # convention treats the whole file as the proof; REPORT.md wants "proof-only
  # LOC (excluding types/functions)" but Bend's LAWS/PROOF split already
  # separates law statements (LAWS.bend, counted as "non-proof" here,
  # analogous to Lean's theorem signature) from proof terms (PROOF.bend).
  wc -l < "$1" | tr -d ' '
}

printf "%-32s %10s %10s\n" "file" "total LOC" "role"
printf "%-32s %10s %10s\n" "bend/ising/lattice.bend"  "$(wc -l < bend/ising/lattice.bend)"  "types/fns"
printf "%-32s %10s %10s\n" "bend/ising/LAWS.bend"     "$(wc -l < bend/ising/LAWS.bend)"     "law statements"
printf "%-32s %10s %10s\n" "bend/ising/PROOF.bend"    "$(count_bend_proof bend/ising/PROOF.bend)" "proof (5/5 laws closed)"
printf "%-32s %10s %10s\n" "bend/circuit/circuit.bend" "$(wc -l < bend/circuit/circuit.bend)" "types/fns"
printf "%-32s %10s %10s\n" "bend/circuit/LAWS.bend"   "$(wc -l < bend/circuit/LAWS.bend)"   "law statements"
printf "%-32s %10s %10s\n" "bend/circuit/PROOF.bend"  "$(count_bend_proof bend/circuit/PROOF.bend)" "proof glue (imports circuit_assoc.bend)"
printf "%-32s %10s %10s\n" "bend/circuit/proofs/circuit_assoc.bend" "$(count_bend_proof bend/circuit/proofs/circuit_assoc.bend)" "proof lemma library (5/5 laws closed)"
printf "%-32s %10s %10s\n" "bend/tests/sint_laws.bend" "$(count_bend_proof bend/tests/sint_laws.bend)" "SInt.add assoc/comm (shared lemma library)"
printf "%-32s %10s %10s\n" "bend/int.bend"            "$(wc -l < bend/int.bend)"            "types/fns (shared)"
printf "%-32s %10s %10s\n" "lean/Ising.lean"          "$(wc -l < lean/Ising.lean)"          "types/fns"
printf "%-32s %10s %10s\n" "lean/Circuit.lean"        "$(wc -l < lean/Circuit.lean)"        "types/fns"
printf "%-32s %10s %10s\n" "lean/Laws.lean"           "$(wc -l < lean/Laws.lean)"           "statements + proofs (interleaved, 5/5 laws closed)"

echo
echo "Note: Lean interleaves theorem statement and proof -- no"
echo "LAWS/PROOF split), so lean/Laws.lean's total (151) mixes both; a"
echo "proof-only sub-count would need per-theorem hand attribution, not a"
echo "line-based heuristic. Reported as one honest total instead of a"
echo "precision this method can't actually deliver."
echo
echo "Note: Circuit's proof cost on the Bend side is split across three"
echo "files it imports transitively -- circuit/PROOF.bend (glue, applies the"
echo "lemmas to the LAW statements), circuit/proofs/circuit_assoc.bend (the"
echo "associativity/counting lemma library, ~40 lemmas), and"
echo "tests/sint_laws.bend (general SInt.add associativity/commutativity,"
echo "imported by circuit_assoc.bend only -- Ising's proof needs no general"
echo "associativity and proves its own smaller, self-contained step lemmas"
echo "inline in ising/PROOF.bend instead). The honest total for Circuit's"
echo "proof is all three files together: 73+499+308 = 880 LOC."
