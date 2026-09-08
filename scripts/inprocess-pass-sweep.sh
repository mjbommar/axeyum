#!/usr/bin/env bash
# Per-pass sweep over a list of DIMACS files, one row per (file, arm).
#
# Usage:
#   scripts/inprocess-pass-sweep.sh <cnf_list.txt> <wall|conflicts> <budget> <out.jsonl>
#
#   wall       budget is MILLISECONDS of search; driver `inprocess_pass_cost`
#              (adds the setup/work split and a wall-clock verdict).
#   conflicts  budget is CONFLICTS; driver `inprocess_profile`. This mode is the
#              reproduction of ADR-1750's protocol, whose break-even is
#              denominated in conflicts — a deterministic unit that does not move
#              with host load, which is exactly why it is the one worth
#              reproducing.
#
# ARM ORDER IS ROTATED PER FILE. Running the arms in a fixed order gives the
# first arm a cold page cache and the last one a warm one, on every file, in the
# same direction — a systematic bias that looks exactly like an arm being
# faster. Rotating makes it noise instead of bias. It does not remove it, so a
# difference smaller than the rotation's own spread is not a difference.
set -uo pipefail

cd "$(dirname "$0")/.."

list="${1:-}"
mode="${2:-}"
budget="${3:-}"
out="${4:-}"
if [[ -z "$list" || -z "$mode" || -z "$budget" || -z "$out" ]]; then
  echo "usage: scripts/inprocess-pass-sweep.sh <cnf_list.txt> <wall|conflicts> <budget> <out.jsonl>" >&2
  exit 2
fi

case "$mode" in
  wall)      bin="target/release/examples/inprocess_pass_cost"
             arms=(off subsume vivify bve preprocess preprocess-full) ;;
  conflicts) bin="target/release/examples/inprocess_profile"
             # ADR-1750's four arms exactly, so the reproduction is a
             # reproduction and not a differently-shaped experiment.
             arms=(off subsume bve preprocess) ;;
  *) echo "FAIL: mode must be wall or conflicts" >&2; exit 2 ;;
esac
if [[ ! -x "$bin" ]]; then
  echo "FAIL: missing $bin" >&2
  exit 2
fi

cpus="${SWEEP_CPUS:-0-5}"
mem_gb="${MEM_GB:-32}"
per_run_s="${PASS_TIMEOUT_S:-1200}"

echo "pass-sweep mode=$mode budget=$budget arms=${arms[*]} cpus=$cpus load_start=$(cut -d' ' -f1-3 /proc/loadavg)" >&2

: > "$out"
expected=0
file_index=0
while IFS= read -r cnf; do
  [[ -z "${cnf// }" ]] && continue
  [[ -f "$cnf" ]] || { echo "FAILED-MISSING $cnf" >&2; continue; }
  file_index=$(( file_index + 1 ))
  count=${#arms[@]}
  for (( k = 0; k < count; k++ )); do
    arm="${arms[$(( (k + file_index) % count ))]}"
    expected=$(( expected + 1 ))
    if ! MEM_LIMIT_GB="$mem_gb" timeout "$per_run_s" \
         taskset -c "$cpus" ./scripts/mem-run.sh "$bin" "$cnf" "$budget" "$arm" >>"$out" 2>/dev/null; then
      # A killed run is recorded, not dropped: a per-pass table over "the runs
      # that survived" silently excludes exactly the expensive arm it is meant
      # to price.
      printf '{"file":"%s","arm":"%s","verdict":"killed"}\n' "$cnf" "$arm" >>"$out"
    fi
  done
done <"$list"

rows=$(grep -c '"arm"' "$out")
echo "pass-sweep expected=$expected rows=$rows files=$file_index load_end=$(cut -d' ' -f1-3 /proc/loadavg)" >&2
# An EMPTY population passes a rows==expected check, because 0 == 0. That is a
# guard that cannot fail in the one case where the output is most misleading: a
# report over zero rows prints "no difference between the arms". Measured here —
# this sweep was launched against a list that did not exist yet, printed
# `files=0`, and exited 0. So the population size is asserted separately.
if (( file_index == 0 )); then
  echo "FAIL: no readable DIMACS files in $list — this measured nothing" >&2
  exit 1
fi
if [[ "$rows" != "$expected" ]]; then
  echo "FAIL: $rows rows for $expected expected runs" >&2
  exit 1
fi
