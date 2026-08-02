#!/usr/bin/env bash
# Head-to-head parity measurement against the division's reference solver.
#
# WHY THIS EXISTS
# ---------------
# "Are we at parity?" had been answered with prose over numbers the reporter
# chose after seeing the data. Every one of these knobs was used at least once
# in this repo's history to make a gap look smaller than it is:
#
#   * hand-picked benchmark slices instead of an external list
#   * a file-size cap that happened to exclude the reference's best cases
#   * a 2-second budget, where both solvers time out and distance collapses
#   * a denominator quietly narrowed to "files with a declared :status"
#   * a weaker reference (a language binding, or an in-process oracle)
#   * retargeting mid-report from the division winner to an easier peer
#   * reporting the delta ("5% -> 30%") instead of the level ("30% vs 40.5%")
#
# None of that requires a false statement, which is exactly why the honest
# reporting rule has to be mechanical rather than cultural. This script fixes
# every choice BEFORE the run and prints four numbers. Nothing here is
# selected after the data is visible.
#
# THE RULES
# ---------
#   1. The benchmark list is a committed file. This script never samples.
#   2. The budget is a protocol constant, not a flag you tune per run.
#   3. The reference is the division winner's real binary, same machine,
#      same budget. Never a binding, never an in-process oracle.
#   4. The denominator is the whole list. unknown / unsupported / timeout /
#      crash / OOM / parse failure all count as NOT SOLVED.
#   5. Any disagreement -- with a declared :status, or with the reference --
#      is an immediate FAIL. It is not a footnote and not a percentage.
#
# Results append to bench-results/PARITY.md. That file is history: entries are
# never edited or removed, so a number going down stays visible.
#
# Usage:
#   scripts/parity-run.sh <division>
#
# Reads: bench-results/parity-lists/<division>.txt   (one benchmark path per line)
# Env:
#   PARITY_BUDGET_S   per-file wall budget, default 24 (SMT-COMP publishes a
#                     24s score precisely so short runs are comparable)
#   PARITY_MEM_GB     per-file memory cap, default 8
set -uo pipefail

cd "$(dirname "$0")/.."

division="${1:-}"
if [[ -z "$division" ]]; then
  echo "usage: scripts/parity-run.sh <division>" >&2
  exit 2
fi

budget_s="${PARITY_BUDGET_S:-24}"
mem_gb="${PARITY_MEM_GB:-8}"
list="bench-results/parity-lists/${division}.txt"
out="bench-results/PARITY.md"

if [[ ! -f "$list" ]]; then
  echo "FAIL: no committed benchmark list at $list" >&2
  echo "      Create it deliberately and commit it BEFORE running." >&2
  exit 2
fi

# The reference solver per division: the actual winner's binary.
case "$division" in
  QF_BV|QF_ABV|QF_AUFBV|QF_FP|QF_BVFP|QF_ABVFP)
    reference_bin="/nas3/data/axeyum/harness/bin/bitwuzla" ;;
  UF|UFLIA|UFNIA|QF_UF|QF_SLIA|QF_S|QF_SEQ|QF_DT|QF_AUFLIA)
    reference_bin="/nas3/data/axeyum/harness/bin/cvc5" ;;
  *)
    reference_bin="/usr/bin/z3" ;;
esac

axeyum_bin="target/release/examples/smtcomp_cli"
for bin in "$axeyum_bin" "$reference_bin"; do
  if [[ ! -x "$bin" ]]; then
    echo "FAIL: missing binary $bin" >&2
    exit 2
  fi
done

solver_sha="$(git rev-parse --short HEAD)"

# REFUSE a run whose binary cannot be reproduced from the recorded SHA.
#
# The old behaviour was to stamp the ledger entry "DIRTY WORKTREE — result not
# reproducible" and run anyway. That is honest but arrives far too late: the
# sweep has already cost hours of machine time and the number it produces cannot
# be defended. It happened on 2026-08-01 — a QF_BV run was measured with another
# lane's uncommitted 234-line `route_trace.rs` compiled into the binary.
#
# Scoped to what actually reaches the binary (`crates/`, the manifests), NOT the
# whole tree: this is a shared checkout where a docs lane always has something
# dirty, and refusing on that would train people to set the override reflexively.
# The whole-tree stamp below is kept as informational for exactly that case.
#
# Escape hatch `PARITY_ALLOW_DIRTY=1` exists for deliberate A/B of an uncommitted
# change; it still stamps the entry, so the ledger stays honest either way.
if ! git diff --quiet -- crates Cargo.toml Cargo.lock 2>/dev/null; then
  if [[ "${PARITY_ALLOW_DIRTY:-0}" != "1" ]]; then
    echo "FAIL: uncommitted changes under crates/ or the manifests — the binary" >&2
    echo "      this would measure cannot be rebuilt from ${solver_sha}, so the" >&2
    echo "      ledger entry would be unreproducible." >&2
    echo >&2
    echo "      Measure a clean tree instead:" >&2
    echo "        git worktree add --detach /tmp/axeyum-parity-clean HEAD" >&2
    echo "        cd /tmp/axeyum-parity-clean" >&2
    echo "        cargo build --release -p axeyum-bench --example smtcomp_cli" >&2
    echo "        ./scripts/parity-run.sh $division" >&2
    echo >&2
    echo "      (\`--features full\` is NOT valid on axeyum-bench and will error.)" >&2
    echo "      Deliberate uncommitted A/B: re-run with PARITY_ALLOW_DIRTY=1." >&2
    git diff --stat -- crates Cargo.toml Cargo.lock >&2
    exit 2
  fi
  echo "parity-run: PARITY_ALLOW_DIRTY=1 — measuring an uncommitted tree" >&2
fi

dirty=""
git diff --quiet || dirty=" (DIRTY WORKTREE — result not reproducible)"
list_sha="$(sha256sum "$list" | cut -c1-12)"
reference_version="$("$reference_bin" --version 2>&1 | head -1 | tr -d '\n')"
total=$(grep -cve '^\s*$' "$list")
# Load at start AND end. The 24s budget is WALL CLOCK on a machine shared with
# other users, so contention silently costs files: a scored UF file decides at
# 20.54s of its 24s budget when the box is quiet, and anything above that band is
# a coin flip. Observed 38.8 load average on 24 cores with six unrelated `java`
# processes burning ~1100% CPU. Without this recorded, a depressed run is
# indistinguishable after the fact from a real regression.
# The bias is one-directional -- contention only LOSES files and cannot produce a
# wrong verdict -- so every ratio here is a LOWER BOUND.
load_start=$(cut -d' ' -f1-3 /proc/loadavg 2>/dev/null || echo "?")

# Declared :status, when the benchmark carries one. Absent is not an excuse to
# drop the file from the denominator -- it only means we cannot catch a wrong
# answer on it from the file alone; the cross-check against the reference still
# applies.
declared_status() {
  grep -m1 ':status' "$1" 2>/dev/null \
    | grep -oE '\b(unsat|sat|unknown)\b' | head -1
}

# One run, hard-capped in both time and memory. Anything that is not a clean
# sat/unsat prints "unsolved" -- crashes, OOMs and timeouts included.
#
# Each solver gets ITS OWN budget flag. Passing axeyum's `--timeout-ms` to z3
# made z3 score 0/3 in the first smoke test: it rejects the unknown flag and
# exits. That error inflates our ratio, which is precisely the direction this
# script exists to guard against -- so the external `timeout` is the real
# enforcement and the native flag is only a courtesy to let a solver exit
# cleanly and report `unknown` rather than be killed.
run_one() {
  local bin="$1" file="$2" verdict
  local -a cmd
  case "$(basename "$bin")" in
    smtcomp_cli) cmd=("$bin" "$file" --timeout-ms "$((budget_s * 1000))") ;;
    z3)          cmd=("$bin" "-T:${budget_s}" "$file") ;;
    cvc5)        cmd=("$bin" "--tlimit=$((budget_s * 1000))" "$file") ;;
    # NOTE THE UNITS: bitwuzla's --time-limit is MILLISECONDS, like cvc5's
    # --tlimit, while z3's -T: is SECONDS. Passing seconds here gave the
    # reference a 24 ms budget -- a ~1000x handicap that inflates our ratio by
    # making the reference look useless. Caught by smoke_reference on the very
    # first real run.
    bitwuzla)    cmd=("$bin" "--time-limit" "$((budget_s * 1000))" "$file") ;;
    *)           cmd=("$bin" "$file") ;;
  esac
  verdict=$(MEM_LIMIT_GB="$mem_gb" timeout "$((budget_s + 5))" \
            ./scripts/mem-run.sh "${cmd[@]}" 2>/dev/null \
            | grep -oE '^(sat|unsat)$' | tail -1)
  echo "${verdict:-unsolved}"
}

# Fail loudly if the reference cannot run AT ALL. A reference scoring zero
# because of a bad invocation looks like a win for us, so this aborts rather
# than warns -- the first version only warned, and a run sailed past it for
# minutes with bitwuzla on a 24 ms budget.
#
# Probe SEVERAL benchmarks, not just the first. Probing one conflates "the
# reference is broken" with "the first file is hard", and that is not
# hypothetical: the first UF benchmark is 196 KB, carries `:status unknown`,
# and cvc5 cannot decide it in 24 s or even 30 s. A single-file probe aborted
# the whole UF division over a legitimately hard instance. Abort only when the
# reference decides NONE of the probes, which still catches a crippled
# invocation (a 24 ms budget solves none of them either).
smoke_reference() {
  local probes=0 solved=0 verdict
  while IFS= read -r probe && (( probes < 5 )); do
    [[ -f "$probe" ]] || continue
    probes=$((probes + 1))
    verdict=$(run_one "$reference_bin" "$probe")
    [[ "$verdict" != "unsolved" ]] && solved=$((solved + 1))
  done < "$list"
  if (( probes > 0 && solved == 0 )); then
    echo "FAIL: the reference decided 0 of $probes probe benchmarks." >&2
    echo "      $reference_bin" >&2
    echo "      A crippled reference reads as a win for us, so this ABORTS." >&2
    echo "      Verify the invocation (check the BUDGET UNITS -- bitwuzla and" >&2
    echo "      cvc5 take milliseconds, z3 takes seconds)." >&2
    echo "      Set PARITY_ALLOW_WEAK_REFERENCE=1 only if the reference really" >&2
    echo "      is beaten by all $probes." >&2
    [[ "${PARITY_ALLOW_WEAK_REFERENCE:-0}" == "1" ]] || exit 2
  fi
}

smoke_reference

# Per-file record. Without this, the only per-file decline data available came
# from a DIFFERENT, ad-hoc census slice -- and reasoning across the two corpora
# produced a lever ("28 UF files decline through the reduction path") whose 28
# files turned out to have ZERO overlap with this scored list. Target levers from
# the corpus that is actually scored.
sidecar="bench-results/parity-details/${division}.tsv"
mkdir -p "$(dirname "$sidecar")"
printf 'file\taxeyum\treference\tdeclared\n' > "$sidecar"

axeyum_solved=0
reference_solved=0
both=0
axeyum_only=0
reference_only=0
disagreements=0
disagreement_log=""

while IFS= read -r file; do
  [[ -z "$file" ]] && continue
  if [[ ! -f "$file" ]]; then
    disagreements=$((disagreements + 1))
    disagreement_log+=$'\n'"    MISSING BENCHMARK: $file"
    continue
  fi

  a=$(run_one "$axeyum_bin" "$file")
  r=$(run_one "$reference_bin" "$file")
  expected=$(declared_status "$file")

  printf '%s\t%s\t%s\t%s\n' "$(basename "$file")" "$a" "$r" "${expected:-none}" >> "$sidecar"

  [[ "$a" != "unsolved" ]] && axeyum_solved=$((axeyum_solved + 1))
  [[ "$r" != "unsolved" ]] && reference_solved=$((reference_solved + 1))
  if [[ "$a" != "unsolved" && "$r" != "unsolved" ]]; then both=$((both + 1))
  elif [[ "$a" != "unsolved" ]]; then axeyum_only=$((axeyum_only + 1))
  elif [[ "$r" != "unsolved" ]]; then reference_only=$((reference_only + 1))
  fi

  # Soundness. Either cross-check firing is a hard failure of the whole run.
  if [[ "$a" != "unsolved" && -n "$expected" && "$expected" != "unknown" && "$a" != "$expected" ]]; then
    disagreements=$((disagreements + 1))
    disagreement_log+=$'\n'"    vs :status — $file: axeyum=$a declared=$expected"
  fi
  if [[ "$a" != "unsolved" && "$r" != "unsolved" && "$a" != "$r" ]]; then
    disagreements=$((disagreements + 1))
    disagreement_log+=$'\n'"    vs reference — $file: axeyum=$a reference=$r"
  fi
done < "$list"

ratio="n/a"
if (( reference_solved > 0 )); then
  ratio=$(awk -v a="$axeyum_solved" -v r="$reference_solved" 'BEGIN{printf "%.1f", 100*a/r}')
fi

verdict="FAIL"
if (( disagreements == 0 )); then verdict="SOUND"; fi

mkdir -p "$(dirname "$out")"
if [[ ! -f "$out" ]]; then
  cat > "$out" <<'HEADER'
# Parity ledger

Append-only. Written by `scripts/parity-run.sh`; entries are never edited or
removed, so a number that goes down stays visible.

Read the **ratio** — axeyum solved as a percentage of what the reference solved
on the identical list, same machine, same budget. It is the only headline.
`DISAGREEMENTS > 0` voids the entry regardless of the ratio: a wrong answer is
not a score.

HEADER
fi

{
  echo "## ${division} — $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo
  echo "| field | value |"
  echo "|---|---|"
  echo "| axeyum solved | ${axeyum_solved}/${total} |"
  echo "| reference solved | ${reference_solved}/${total} |"
  echo "| **ratio (axeyum / reference)** | **${ratio}%** |"
  echo "| **disagreements** | **${disagreements}** |"
  echo "| soundness | ${verdict} |"
  echo "| both / axeyum-only / reference-only | ${both} / ${axeyum_only} / ${reference_only} |"
  echo "| reference | \`${reference_version}\` |"
  echo "| protocol | ${budget_s}s wall, ${mem_gb}GiB, per-file |"
  echo "| benchmark list | \`${list}\` (sha256 ${list_sha}, ${total} files) |"
  echo "| solver commit | \`${solver_sha}\`${dirty} |"
  echo "| load average (start / end) | ${load_start} / $(cut -d' ' -f1-3 /proc/loadavg 2>/dev/null || echo '?') — 24 cores; a high load DEPRESSES this result |"
  echo "| per-file detail | \`${sidecar}\` |"
  if (( disagreements > 0 )); then
    echo
    echo "DISAGREEMENTS:"
    echo '```'
    echo "${disagreement_log}"
    echo '```'
  fi
  echo
} >> "$out"

echo "${division}: axeyum ${axeyum_solved}/${total}, reference ${reference_solved}/${total}, ratio ${ratio}%, disagreements ${disagreements} (${verdict})"
echo "appended to ${out}"

(( disagreements == 0 ))
