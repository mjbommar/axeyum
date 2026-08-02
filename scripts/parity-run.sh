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
#
# EVIDENCE MODE (off by default)
# ------------------------------
#   PARITY_EVIDENCE=1            run axeyum with AXEYUM_EVIDENCE=1 and record a
#                                `certified / unsat` cell per division.
#   PARITY_EVIDENCE_BUDGET_S     axeyum's per-file budget in evidence mode only
#                                (default: PARITY_BUDGET_S). Producing and
#                                re-checking a proof costs real time ON TOP OF
#                                deciding, so measuring evidence at the plain
#                                budget would silently trade decided files for
#                                certified ones and understate BOTH numbers.
#
# Decide-rate is measured per file and moved because every file was visible.
# The second front -- "every unsat/valid carries a machine-checkable proof" --
# had no such column, so nobody could state what fraction of our unsats are
# actually certified. This makes that a number on the same population.
#
# Evidence-mode entries are STAMPED as such in the ledger and their ratio is NOT
# comparable to a default entry: the axeyum budget may differ and the evidence
# front door is a different route. The ratio itself is computed identically.
set -uo pipefail

cd "$(dirname "$0")/.."

division="${1:-}"
if [[ -z "$division" ]]; then
  echo "usage: scripts/parity-run.sh <division>" >&2
  exit 2
fi

budget_s="${PARITY_BUDGET_S:-24}"
mem_gb="${PARITY_MEM_GB:-8}"
evidence_mode="${PARITY_EVIDENCE:-0}"
# axeyum's budget. Identical to the protocol budget unless evidence mode asks for
# more; the REFERENCE always runs at the protocol budget, so it is never handed a
# handicap by this knob.
axeyum_budget_s="$budget_s"
if [[ "$evidence_mode" == "1" ]]; then
  axeyum_budget_s="${PARITY_EVIDENCE_BUDGET_S:-$budget_s}"
  export AXEYUM_EVIDENCE=1
fi
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
  # QF_LIA's SMT-COMP 2025 winner is OpenSMT (4,579/4,825 = 94.9 %), which is
  # NOT on this machine. cvc5 is the strongest reference we actually have: it
  # placed *2nd in this very division* (4,443/4,825 = 92.1 %), 136 benchmarks
  # behind the winner. The fallthrough would have used `/usr/bin/z3` 4.13.3,
  # which **did not compete in SMT-COMP 2025 at all** -- picking it would be
  # exactly the "a weaker reference" knob this script's header lists. Choosing
  # cvc5 makes our ratio HARDER, which is the correct direction for a knob we
  # are allowed to set. If OpenSMT is ever installed, move this arm to it.
  QF_LIA|QF_ALIA|QF_LRA|QF_LIRA)
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

# The informational stamp, scoped to what can actually change the RESULT.
#
# It used to test `git diff --quiet` over the WHOLE tree, which made it lie: this
# script appends to `bench-results/PARITY.md` and rewrites
# `bench-results/parity-details/<div>.tsv`, so after the first division in a
# worktree the tree is dirty BY THIS SCRIPT'S OWN DOING, and every subsequent run
# was stamped "not reproducible". Observed 2026-08-02: three sweeps in one clean
# detached worktree at `44fe20862` produced a clean QF_BV entry and falsely
# stamped UF and QF_SLIA — same commit, same binary, same worktree. A warning
# that fires on its own side effects trains readers to ignore it, which is worse
# than not having it, because the stamp matters exactly when it is rare.
dirty=""
git diff --quiet -- crates Cargo.toml Cargo.lock scripts \
  || dirty=" (DIRTY WORKTREE — result not reproducible)"
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
#
# `last_evidence` is a side channel, set ONLY on the evidence-mode axeyum path.
# It carries the `; evidence …` line the CLI prints (see smtcomp_cli.rs) so the
# caller can score `certified / unsat` without a second run.
last_evidence=""
run_one() {
  local bin="$1" file="$2" verdict raw
  local b="$budget_s"
  [[ "$(basename "$bin")" == "smtcomp_cli" ]] && b="$axeyum_budget_s"
  local -a cmd
  case "$(basename "$bin")" in
    smtcomp_cli) cmd=("$bin" "$file" --timeout-ms "$((b * 1000))") ;;
    z3)          cmd=("$bin" "-T:${b}" "$file") ;;
    cvc5)        cmd=("$bin" "--tlimit=$((b * 1000))" "$file") ;;
    # NOTE THE UNITS: bitwuzla's --time-limit is MILLISECONDS, like cvc5's
    # --tlimit, while z3's -T: is SECONDS. Passing seconds here gave the
    # reference a 24 ms budget -- a ~1000x handicap that inflates our ratio by
    # making the reference look useless. Caught by smoke_reference on the very
    # first real run.
    bitwuzla)    cmd=("$bin" "--time-limit" "$((budget_s * 1000))" "$file") ;;
    *)           cmd=("$bin" "$file") ;;
  esac
  # DEFAULT PATH — byte-identical to what every recorded baseline measured.
  # Evidence mode takes the branch below instead; it is never on by default.
  if [[ "$evidence_mode" != "1" || "$(basename "$bin")" != "smtcomp_cli" ]]; then
    verdict=$(MEM_LIMIT_GB="$mem_gb" timeout "$((b + 5))" \
              ./scripts/mem-run.sh "${cmd[@]}" 2>/dev/null \
              | grep -oE '^(sat|unsat)$' | tail -1)
    echo "${verdict:-unsolved}"
    return
  fi

  # Evidence mode: capture stdout whole so the `; evidence …` line survives
  # alongside the verdict. The verdict is extracted with the SAME expression as
  # above, so what counts as solved does not change.
  raw=$(MEM_LIMIT_GB="$mem_gb" timeout "$((b + 5))" \
        ./scripts/mem-run.sh "${cmd[@]}" 2>/dev/null)
  verdict=$(printf '%s\n' "$raw" | grep -oE '^(sat|unsat)$' | tail -1)
  last_evidence=$(printf '%s\n' "$raw" | grep -m1 '^; evidence ' || true)
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
#
# ...EXCEPT IT DOES NOT, AND THAT WAS MEASURED, NOT REASONED (2026-08-02, adding
# QF_LIA). The "solves none of them either" clause is a QF_BV/UF observation
# generalised without checking. On QF_LIA the first two committed benchmarks are
# decided by cvc5 in ~0.1 s, so a deliberately crippled `--tlimit=24` (seconds
# passed where milliseconds are expected -- a 1000x handicap) still scored 2/5
# and the guard stayed silent. The whole run then proceeds against a reference
# that cannot solve anything hard, and the inflated ratio reads as a win for us.
#
# So the count test is necessary but NOT sufficient, and the second test below
# targets the unit bug directly rather than through its side effect. A reference
# given its real budget BURNS that budget on a file it cannot decide; a reference
# given 24 ms returns "unsolved" almost immediately. Measured on the same five
# QF_LIA probes: at `--tlimit=24000` the undecided probes ran the full ~24 s wall,
# at `--tlimit=24` they returned in 2.3 s (parse time alone). That gap is the
# signature, and it does not depend on how easy the division's easy files are.
#
# The rule is "EVERY undecided probe came back early", not "any", so one fast
# unsupported-logic or OOM exit cannot trip it. When the reference decides all
# five probes there is nothing to time and the test abstains -- and a reference
# going 5/5 is self-evidently not crippled.
#
# TIMING PRIMITIVE: bash's `EPOCHREALTIME`, deliberately NOT `date +%s%3N`. On
# this machine `date` is uutils coreutils 0.8.0, whose `%3N` is broken -- it
# returns an 18-digit value (`178567738728633065`) rather than a 13-digit
# millisecond stamp. The first version of this check used it, computed a garbage
# elapsed time, and silently never fired: a guard that cannot fail is worse than
# no guard. EPOCHREALTIME is a bash builtin with exactly 6 decimal places, so
# stripping the dot yields microseconds with no subprocess and no `date` variant
# to trip over.
now_ms() { local us="${EPOCHREALTIME/./}"; echo $(( 10#$us / 1000 )); }

smoke_reference() {
  local probes=0 solved=0 verdict start elapsed
  local unsolved_probes=0 unsolved_fast=0
  local floor_ms=$(( budget_s * 1000 / 2 ))
  while IFS= read -r probe && (( probes < 5 )); do
    [[ -f "$probe" ]] || continue
    probes=$((probes + 1))
    start=$(now_ms)
    verdict=$(run_one "$reference_bin" "$probe")
    elapsed=$(( $(now_ms) - start ))
    if [[ "$verdict" != "unsolved" ]]; then
      solved=$((solved + 1))
    else
      unsolved_probes=$((unsolved_probes + 1))
      (( elapsed < floor_ms )) && unsolved_fast=$((unsolved_fast + 1))
    fi
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
  if (( unsolved_probes > 0 && unsolved_fast == unsolved_probes )); then
    echo "FAIL: the reference did not USE its ${budget_s}s budget." >&2
    echo "      $reference_bin" >&2
    echo "      All ${unsolved_probes} undecided probe(s) returned in under" >&2
    echo "      $(( floor_ms / 1000 ))s. A correctly budgeted solver burns the" >&2
    echo "      whole budget before giving up, so the budget is not reaching it." >&2
    echo "      CHECK THE UNITS: bitwuzla --time-limit and cvc5 --tlimit are" >&2
    echo "      MILLISECONDS; z3 -T: is SECONDS. Passing seconds as milliseconds" >&2
    echo "      is a ~1000x handicap that inflates our ratio." >&2
    echo "      Set PARITY_ALLOW_WEAK_REFERENCE=1 only after verifying the" >&2
    echo "      invocation by hand." >&2
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
if [[ "$evidence_mode" == "1" ]]; then
  printf 'file\taxeyum\treference\tdeclared\tevidence_kind\tcertified\trecheck\n' > "$sidecar"
else
  printf 'file\taxeyum\treference\tdeclared\n' > "$sidecar"
fi

unsat_count=0
certified_unsats=0
rechecked_unsats=0
bad_certificates=0
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

  last_evidence=""
  a=$(run_one "$axeyum_bin" "$file")
  r=$(run_one "$reference_bin" "$file")
  expected=$(declared_status "$file")

  if [[ "$evidence_mode" == "1" ]]; then
    # Parse the CLI's single `; evidence kind=… certified=… recheck=… ms=…` line.
    # Absent (crash / timeout / kill) means NO evidence -- scored as uncertified,
    # never as missing data.
    ev_kind=$(sed -n 's/.*kind=\([^ ]*\).*/\1/p' <<< "$last_evidence")
    ev_certified=$(sed -n 's/.*certified=\([^ ]*\).*/\1/p' <<< "$last_evidence")
    ev_recheck=$(sed -n 's/.*recheck=\([^ ]*\).*/\1/p' <<< "$last_evidence")
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$(basename "$file")" "$a" "$r" \
      "${expected:-none}" "${ev_kind:-none}" "${ev_certified:-0}" "${ev_recheck:-none}" >> "$sidecar"
    if [[ "$a" == "unsat" ]]; then
      unsat_count=$((unsat_count + 1))
      [[ "$ev_certified" == "1" ]] && certified_unsats=$((certified_unsats + 1))
      [[ "$ev_recheck" == "ok" ]] && rechecked_unsats=$((rechecked_unsats + 1))
    fi
    # A certificate that does not re-check is a soundness alarm, not a statistic.
    # It voids the entry the same way a wrong verdict does.
    if [[ "$ev_recheck" == "FAIL" ]]; then
      bad_certificates=$((bad_certificates + 1))
      disagreements=$((disagreements + 1))
      disagreement_log+=$'\n'"    CERTIFICATE FAILED TO RE-CHECK — $file (kind=${ev_kind:-none})"
    fi
  else
    printf '%s\t%s\t%s\t%s\n' "$(basename "$file")" "$a" "$r" "${expected:-none}" >> "$sidecar"
  fi

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

# `certified / unsat` -- the Lean-parity front made a number on the SAME
# population the decide-rate is measured on. Denominator is every `unsat` axeyum
# produced in this run; nothing is dropped for being hard or uncertified.
certified_ratio="n/a"
rechecked_ratio="n/a"
if (( unsat_count > 0 )); then
  certified_ratio=$(awk -v c="$certified_unsats" -v u="$unsat_count" 'BEGIN{printf "%.1f", 100*c/u}')
  rechecked_ratio=$(awk -v c="$rechecked_unsats" -v u="$unsat_count" 'BEGIN{printf "%.1f", 100*c/u}')
fi

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

entry_title="## ${division} — $(date -u +%Y-%m-%dT%H:%M:%SZ)"
if [[ "$evidence_mode" == "1" ]]; then
  entry_title+=" — EVIDENCE MODE"
fi

{
  echo "$entry_title"
  echo
  if [[ "$evidence_mode" == "1" ]]; then
    echo "Evidence mode (\`PARITY_EVIDENCE=1\` → \`AXEYUM_EVIDENCE=1\`). axeyum routed"
    echo "through the evidence front door, which produces AND re-checks a certificate"
    echo "on top of deciding. The **ratio here is NOT comparable to a default entry**"
    echo "(different route, and axeyum ran at ${axeyum_budget_s}s vs the ${budget_s}s protocol"
    echo "budget). The headline for this entry is \`certified / unsat\`."
    echo
  fi
  echo "| field | value |"
  echo "|---|---|"
  echo "| axeyum solved | ${axeyum_solved}/${total} |"
  echo "| reference solved | ${reference_solved}/${total} |"
  echo "| **ratio (axeyum / reference)** | **${ratio}%** |"
  echo "| **disagreements** | **${disagreements}** |"
  echo "| soundness | ${verdict} |"
  if [[ "$evidence_mode" == "1" ]]; then
    echo "| **certified / unsat** | **${certified_unsats}/${unsat_count} = ${certified_ratio}%** |"
    echo "| re-checked here (text-only) / unsat | ${rechecked_unsats}/${unsat_count} = ${rechecked_ratio}% |"
    echo "| certificates that FAILED to re-check | ${bad_certificates} |"
    echo "| axeyum budget (evidence) | ${axeyum_budget_s}s |"
  fi
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
if [[ "$evidence_mode" == "1" ]]; then
  echo "${division}: certified ${certified_unsats}/${unsat_count} unsats = ${certified_ratio}% (re-checked here ${rechecked_unsats}/${unsat_count} = ${rechecked_ratio}%, bad certs ${bad_certificates})"
fi
echo "appended to ${out}"

(( disagreements == 0 ))
