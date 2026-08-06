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
fi
# AXEYUM_EVIDENCE is passed PER INVOCATION (see `run_one`), never exported here.
# An earlier version exported it, which silently put the SCORED run on the
# evidence route too: the entry read `axeyum solved 147/200` against a 184/200
# baseline, and `certified/unsat` was again computed over a route-narrowed
# denominator. The scored run must be the shipped default configuration, so
# `run_one` also `env -u`s the variable out of the scored invocation -- an
# inherited `AXEYUM_EVIDENCE=1` from the caller's shell cannot change what this
# script scores either.
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
  # Same reasoning as QF_LIA above: the fallthrough is `/usr/bin/z3` 4.13.3,
  # which did NOT compete in SMT-COMP 2025, so using it would be the "weaker
  # reference" knob this script's header warns about. cvc5 is the strongest
  # binary actually installed here and is a serious entrant in both divisions,
  # which makes our ratio harder — the correct direction for a knob we are
  # allowed to set.
  QF_IDL|QF_RDL|QF_UFLIA|QF_UFNIA|QF_NIA|QF_NRA)
    reference_bin="/nas3/data/axeyum/harness/bin/cvc5" ;;
  *)
    reference_bin="/usr/bin/z3" ;;
esac

# Extra flags handed to the REFERENCE, e.g. its competition portfolio.
#
# The UF entries on this board were measured against PLAIN cvc5, and that
# flatters us on exactly the files our finite-model-finding work wins: SMT-COMP
# runs cvc5 with a portfolio that enables `--finite-model-find`. Measuring
# against the plain binary and reporting the ratio is not false, but it is the
# "a weaker reference" knob this script's header lists, so the option exists to
# make the harder comparison runnable — and the entry RECORDS what was passed,
# so a portfolio run can never be mistaken for a plain one.
#
# Word-split deliberately (not an array) so a caller can pass several flags in
# one variable; the values here are solver flags, never paths.
read -r -a reference_extra_opts <<<"${PARITY_REFERENCE_OPTS:-}"
reference_options="${PARITY_REFERENCE_OPTS:-}"

axeyum_bin="target/release/examples/smtcomp_cli"
for bin in "$axeyum_bin" "$reference_bin"; do
  if [[ ! -x "$bin" ]]; then
    echo "FAIL: missing binary $bin" >&2
    exit 2
  fi
done

solver_sha="$(git rev-parse --short HEAD)"

# RECORD THE CONFIGURATION THAT WAS MEASURED.
#
# Every A/B lever in `smtcomp_cli` is an env var, so a sweep run with a lever on
# produced an entry indistinguishable from a default-config one. That is exactly
# the "reporting a number obtained under conditions the reader cannot see"
# failure this script exists to prevent, and it was one env var away from
# happening the first time a default-off solver flag looked good.
#
# The reference side gets the same treatment: the UF entries on this board were
# measured against PLAIN cvc5, not its competition portfolio (which enables
# finite model finding — precisely what wins the files our own FMF work wins).
# Recording "<none>" makes that visible in the entry instead of in a footnote
# someone has to remember.
axeyum_options=""
for lever in AXEYUM_NESTED_QUANT AXEYUM_CNF_INPROCESSING AXEYUM_CNF_VIVIFY \
             AXEYUM_EVIDENCE AXEYUM_TIMEOUT_MS AXEYUM_MAX_GROUND_TERMS; do
  if [[ -n "${!lever:-}" ]]; then
    axeyum_options+="${axeyum_options:+ }${lever}=${!lever}"
  fi
done
axeyum_options="${axeyum_options:-<none — shipped default configuration>}"

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

# WARN when the box is already loaded enough to cost files.
#
# Every ratio here is a LOWER bound -- contention only ever loses files and
# cannot produce a wrong verdict -- but "lower bound" stops being a footnote and
# starts being the headline once the load is high. Measured on 2026-08-02: the
# same UF list was swept at load 2 and at load 32 on this box, and a scored file
# that decides at 20.5s of its 24s budget when quiet is a coin flip when loaded.
#
# This warns rather than refuses on purpose. Refusing would make the harness
# unusable on a shared machine, and an operator who knowingly measures under
# load and reads the recorded number as a floor is doing something legitimate.
# What is NOT legitimate is discovering the load afterwards, so the threshold
# speaks up front and the entry keeps the numbers either way.
load_one=$(cut -d' ' -f1 /proc/loadavg 2>/dev/null || echo 0)
cores=$(nproc 2>/dev/null || echo 1)
if awk -v l="$load_one" -v c="$cores" 'BEGIN { exit !(l > c / 2) }'; then
  echo "parity-run: WARNING — load ${load_one} on ${cores} cores before the sweep." >&2
  echo "            Contention only LOSES files, so the ratio you get is a floor," >&2
  echo "            not an estimate. Re-run on a quiet box before treating a" >&2
  echo "            regression here as real. The entry records the load." >&2
fi

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
# `evidence_sink` is a side channel, written ONLY on the evidence-mode axeyum
# path. It carries the `; evidence …` line the CLI prints (see smtcomp_cli.rs)
# so the caller can score `certified / unsat` without a second run.
#
# It is a FILE, not a variable, on purpose: `run_one` is invoked as `$(run_one …)`,
# a command substitution, so it runs in a SUBSHELL and any variable it assigns is
# discarded on return. The first version of this used a global and silently scored
# 0/5 certified on a smoke list whose files each printed `certified=1`.
evidence_sink="$(mktemp)"
trap 'rm -f "$evidence_sink"' EXIT
#
# `$3` selects the EVIDENCE run: an EXTRA axeyum invocation, at its own budget,
# with AXEYUM_EVIDENCE=1. It never replaces the scored run -- see the loop.
run_one() {
  local bin="$1" file="$2" mode="${3:-plain}" verdict raw
  local b="$budget_s"
  local -a pre=(env -u AXEYUM_EVIDENCE)
  if [[ "$mode" == "evidence" ]]; then
    b="$axeyum_budget_s"
    pre=(env AXEYUM_EVIDENCE=1)
  fi
  local -a cmd
  case "$(basename "$bin")" in
    smtcomp_cli) cmd=("$bin" "$file" --timeout-ms "$((b * 1000))") ;;
    z3)          cmd=("$bin" "-T:${b}" "$file") ;;
    cvc5)        cmd=("$bin" "--tlimit=$((b * 1000))" "${reference_extra_opts[@]}" "$file") ;;
    # NOTE THE UNITS: bitwuzla's --time-limit is MILLISECONDS, like cvc5's
    # --tlimit, while z3's -T: is SECONDS. Passing seconds here gave the
    # reference a 24 ms budget -- a ~1000x handicap that inflates our ratio by
    # making the reference look useless. Caught by smoke_reference on the very
    # first real run.
    bitwuzla)    cmd=("$bin" "--time-limit" "$((budget_s * 1000))" "$file") ;;
    *)           cmd=("$bin" "$file") ;;
  esac
  # SCORED PATH — byte-identical to what every recorded baseline measured, and
  # it is what BOTH solvers take even when evidence mode is on.
  if [[ "$mode" != "evidence" ]]; then
    verdict=$(MEM_LIMIT_GB="$mem_gb" timeout "$((b + 5))" \
              "${pre[@]}" ./scripts/mem-run.sh "${cmd[@]}" 2>/dev/null \
              | grep -oE '^(sat|unsat)$' | tail -1)
    echo "${verdict:-unsolved}"
    return
  fi

  # Evidence run: capture stdout whole so the `; evidence …` line survives
  # alongside the verdict. The verdict is extracted with the SAME expression as
  # above, so what counts as solved does not change.
  raw=$(MEM_LIMIT_GB="$mem_gb" timeout "$((b + 5))" \
        "${pre[@]}" ./scripts/mem-run.sh "${cmd[@]}" 2>/dev/null)
  verdict=$(printf '%s\n' "$raw" | grep -oE '^(sat|unsat)$' | tail -1)
  printf '%s\n' "$raw" | grep -m1 '^; evidence ' > "$evidence_sink" || : > "$evidence_sink"
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
  # Sample the probes SPREAD ACROSS the list, not the first five.
  #
  # The list is a sorted stride, so its first five files all come from whichever
  # directory sorts first — one family, and often a systematically hard one.
  # Measured 2026-08-03: QF_UFLIA and QF_NIA both aborted with "the reference
  # decided 0 of 5", and cvc5 does genuinely time out on those five at 24s
  # standalone. The reference was fine; the SAMPLE was not, and the guard read a
  # hard corner of one family as a broken reference.
  #
  # Five evenly spaced files cross family boundaries, so "the reference decides
  # nothing" means what it is supposed to mean. This weakens the guard slightly
  # against a reference that fails only on the divisions's hardest family — an
  # acceptable trade against aborting valid sweeps, and the whole-list result
  # would expose that case anyway.
  local total_probe_lines
  total_probe_lines=$(grep -cve '^\s*$' "$list")
  local probe_step=$(( total_probe_lines / 5 ))
  (( probe_step < 1 )) && probe_step=1
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
  done < <(awk -v st="$probe_step" 'NR % st == 1 || st == 1' "$list")
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

# REFUSE to run two sweeps of the same division in the same worktree at once.
#
# Both would append to the same sidecar, interleaving rows from two runs into a
# file that looks plausible and is unusable: observed 2026-08-03, a
# double-launched QF_UFLIA left 401 rows for 200 benchmarks, every file twice.
# The ledger SUMMARIES survive that (each process counts its own loop), but the
# sidecar is what lanes read to find residuals, so a corrupted one silently
# misdirects the next piece of work.
#
# A directory is the lock because mkdir is atomic; the trap releases it on any
# exit path including the disagreement abort.
lockdir="${sidecar}.lock"
if ! mkdir "$lockdir" 2>/dev/null; then
  echo "FAIL: another ${division} sweep is already running in this worktree" >&2
  echo "      (lock: $lockdir). Two sweeps would interleave rows into one" >&2
  echo "      sidecar. Wait for it, or run in a separate worktree." >&2
  exit 2
fi
trap 'rmdir "$lockdir" 2>/dev/null' EXIT

# RESUME: reuse per-file verdicts already measured for this division.
#
# A full division is 200 files at up to 24s x2 solvers -- long enough that an
# interruption is not an edge case. Three UF sweeps were lost today: two reaped
# by the task runner within minutes, one killed with the session, each throwing
# away ~40 minutes of correct per-file work that was already sitting in the
# sidecar. Chunking does not help, because every invocation restarts the list
# from the top.
#
# With PARITY_RESUME=1 a file whose exact committed-list path is already in the
# sidecar reuses that row's verdicts instead of re-running both solvers. Legacy
# basename-only sidecars are accepted only when every reused basename is unique
# in the current list; ambiguity, duplicate rows and population drift fail
# closed. Nothing else changes: the loop still visits every file in the
# committed list, so the denominator, disagreement rules and summary are
# computed exactly as in a single run.
#
# Off by default -- a resumed entry mixes measurements from different moments
# (and so different machine load), which is fine for finishing an interrupted
# sweep but is not what you want when establishing a fresh baseline. The entry
# records that it was resumed.
declare -A cached_row=()
resumed_files=0
if [[ "${PARITY_RESUME:-0}" == "1" && -f "$sidecar" ]]; then
  resume_rows=$(mktemp)
  if ! python3 scripts/parity_resume.py "$list" "$sidecar" > "$resume_rows"; then
    rm -f "$resume_rows"
    exit 2
  fi
  while IFS=$'\t' read -r f a_v r_v d_v; do
    cached_row["$f"]="${a_v}"$'\t'"${r_v}"$'\t'"${d_v}"
    resumed_files=$((resumed_files + 1))
  done < "$resume_rows"
  rm -f "$resume_rows"
  echo "parity-run: resuming — ${resumed_files} files already measured in ${sidecar}" >&2
fi

if [[ "$evidence_mode" == "1" ]]; then
  printf 'file\taxeyum\treference\tdeclared\tevidence_verdict\tevidence_kind\tcertified\trecheck\tevidence_ms\n' > "$sidecar"
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

  # The SCORED axeyum run, at the protocol budget, on the shipped default route.
  # Evidence mode does NOT replace it -- it adds a second run below. Everything
  # the ledger scores (solved counts, ratio, disagreements) comes from this one,
  # so an evidence entry stays directly comparable to a default entry.
  # A cached row short-circuits BOTH solver runs. `expected` is re-read from the
  # benchmark rather than trusted from the cache, so a corrupted sidecar cannot
  # silence a declared-status disagreement.
  cache_key="$file"
  expected=$(declared_status "$file")
  if [[ -n "${cached_row[$cache_key]:-}" ]]; then
    IFS=$'\t' read -r a r _cached_declared <<<"${cached_row[$cache_key]}"
  else
    a=$(run_one "$axeyum_bin" "$file")
    r=$(run_one "$reference_bin" "$file")
  fi

  if [[ "$evidence_mode" == "1" ]]; then
    : > "$evidence_sink"
    ae=$(run_one "$axeyum_bin" "$file" evidence)
    last_evidence=$(cat "$evidence_sink")
    # Parse the CLI's single `; evidence kind=… certified=… recheck=… ms=…` line.
    # Absent (crash / timeout / kill) means NO evidence -- scored as uncertified,
    # never as missing data.
    ev_kind=$(sed -n 's/.*kind=\([^ ]*\).*/\1/p' <<< "$last_evidence")
    ev_certified=$(sed -n 's/.*certified=\([^ ]*\).*/\1/p' <<< "$last_evidence")
    ev_recheck=$(sed -n 's/.*recheck=\([^ ]*\).*/\1/p' <<< "$last_evidence")
    ev_ms=$(sed -n 's/.*ms=\([^ ]*\).*/\1/p' <<< "$last_evidence")
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$file" "$a" "$r" \
      "${expected:-none}" "$ae" "${ev_kind:-none}" "${ev_certified:-0}" \
      "${ev_recheck:-none}" "${ev_ms:-}" >> "$sidecar"
    # THE DENOMINATOR IS EVERY UNSAT WE ACTUALLY PRODUCE -- the scored run's,
    # not the evidence run's. Scoring `certified / (unsats the evidence route
    # itself decided)` reads 100% while a third of our unsats carry nothing,
    # because the files the evidence route cannot afford drop out of the
    # denominator along with their missing certificates. That is precisely the
    # "denominator quietly narrowed" failure this script's header names.
    if [[ "$a" == "unsat" ]]; then
      unsat_count=$((unsat_count + 1))
      if [[ "$ae" == "unsat" && "$ev_certified" == "1" ]]; then
        certified_unsats=$((certified_unsats + 1))
        [[ "$ev_recheck" == "ok" ]] && rechecked_unsats=$((rechecked_unsats + 1))
      fi
    fi
    # A certificate that does not re-check is a soundness alarm, not a statistic.
    # It voids the entry the same way a wrong verdict does.
    if [[ "$ev_recheck" == "FAIL" ]]; then
      bad_certificates=$((bad_certificates + 1))
      disagreements=$((disagreements + 1))
      disagreement_log+=$'\n'"    CERTIFICATE FAILED TO RE-CHECK — $file (kind=${ev_kind:-none})"
    fi
    # Two axeyum routes on one file are a free differential cross-check.
    if [[ "$a" != "unsolved" && "$ae" != "unsolved" && "$a" != "$ae" ]]; then
      disagreements=$((disagreements + 1))
      disagreement_log+=$'\n'"    axeyum default vs evidence route — $file: default=$a evidence=$ae"
    fi
  else
    printf '%s\t%s\t%s\t%s\n' "$file" "$a" "$r" "${expected:-none}" >> "$sidecar"
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
# population the decide-rate is measured on. Denominator is every `unsat` the
# SCORED axeyum run produced; nothing is dropped for being hard or uncertified.
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
    echo "Evidence mode (\`PARITY_EVIDENCE=1\`). Every scored number above and below is"
    echo "from the SAME default-route run at the ${budget_s}s protocol budget as any other"
    echo "entry -- evidence mode only ADDS a second axeyum run per file"
    echo "(\`AXEYUM_EVIDENCE=1\`, ${axeyum_budget_s}s) that produces and re-checks a certificate."
    echo
    echo "\`certified / unsat\` counts, over every \`unsat\` THE SCORED RUN PRODUCED, how many"
    echo "the evidence run also decided \`unsat\` **and** returned a checkable certificate for."
    echo "A file we can refute but cannot certify counts against us; it is not dropped."
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
    echo "| axeyum evidence-run budget | ${axeyum_budget_s}s (scored run stays at ${budget_s}s) |"
  fi
  echo "| both / axeyum-only / reference-only | ${both} / ${axeyum_only} / ${reference_only} |"
  echo "| reference | \`${reference_version}\` |"
  echo "| reference options | \`${reference_options:-<none — plain invocation, NOT a competition portfolio>}\` |"
  echo "| axeyum options | \`${axeyum_options}\` |"
  if (( resumed_files > 0 )); then
    echo "| resumed | ${resumed_files} of ${total} files reused from a prior interrupted sweep (mixed load) |"
  fi
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
