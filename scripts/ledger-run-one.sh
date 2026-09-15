#!/usr/bin/env bash
# Run ONE corpus file through the CLI under the board envelope, keep the
# stdout, and append one outcome-ledger row (ADR-2102).
#
# # Why this exists as a script rather than as five lines in each sweep
#
# The three sweep runners in this repository each inline the same capture, and
# each of them threw the capture away:
#
#     raw=$(timeout ... "$AX" "$f" 2>/dev/null)
#     v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
#
# One token kept, everything else discarded, and no `--trace` so there was
# nothing to keep anyway. `bench-results/dispatch-plan-sizing-20260915/README.md`
# measured that this is the harness CONVENTION, not one script's bug: the same
# pattern is in `quant-rounds/route-hit.sh`, `tier1-divisions/shard-run.sh` and
# `nested-array-ir/shard-run.sh`. That lane then had to RE-RUN 645 undecided
# Tier 1 rows to get back what those sweeps had already computed.
#
# So the capture becomes a file and the row becomes a library call, in ONE
# place. A sweep script calls this instead of inlining the pipeline, and the
# schema cannot drift at the writer because the writer does not format a row.
#
# # The envelope is the caller's, and it is not weakened here
#
# Same shape every board here uses: an outer `timeout` with headroom over the
# solver's own `--timeout-ms`, `ulimit -v`, and a pinned core. Those are
# arguments rather than constants so a sweep keeps the envelope it published.
#
# # `--trace` and verdict invariance
#
# `--trace` arms instrumentation only; PLAN-SIZING measured 644 of 644 verdicts
# unchanged by adding it. That is a MEASUREMENT, not a guarantee, so this script
# has `--no-trace-control`: it runs the same file on the same binary WITHOUT
# `--trace` and reports whether the verdict moved. The ledger row is written
# either way and the control's answer goes to stderr as `INVARIANCE ok|MOVED`,
# so a sweep can count it.
#
# Usage:
#   ledger-run-one.sh --sweep-id ID --arm A --binary PATH --binary-sha SHA \
#                     --file ABS_PATH --corpus-root DIR --outdir DIR \
#                     [--budget-s 24] [--headroom-s 16] [--vlimit-kb 8388608] \
#                     [--core 1,9] [--host NAME] [--ledger-dir DIR] \
#                     [--no-trace-control] [--note TEXT]
#
# Exit status: 0 when the row was appended, 2 on a usage/precondition failure.
# A solver non-zero exit is DATA (it lands in `exit_status`), not this script's
# failure -- an aborted file is an outcome the ledger exists to record.
set -u

usage() { sed -n '2,40p' "$0"; exit 2; }

SWEEP_ID=""; ARM=""; BIN=""; BIN_SHA=""; FILE=""; CORPUS_ROOT=""; OUTDIR=""
BUDGET_S=24; HEADROOM_S=16; VLIMIT_KB=$((8 * 1024 * 1024)); CORE=""; HOST=""
LEDGER_DIR=""; NOTE=""; INVARIANCE=0

while [ $# -gt 0 ]; do
  case "$1" in
    --sweep-id) SWEEP_ID="$2"; shift 2 ;;
    --arm) ARM="$2"; shift 2 ;;
    --binary) BIN="$2"; shift 2 ;;
    --binary-sha) BIN_SHA="$2"; shift 2 ;;
    --file) FILE="$2"; shift 2 ;;
    --corpus-root) CORPUS_ROOT="$2"; shift 2 ;;
    --outdir) OUTDIR="$2"; shift 2 ;;
    --budget-s) BUDGET_S="$2"; shift 2 ;;
    --headroom-s) HEADROOM_S="$2"; shift 2 ;;
    --vlimit-kb) VLIMIT_KB="$2"; shift 2 ;;
    --core) CORE="$2"; shift 2 ;;
    --host) HOST="$2"; shift 2 ;;
    --ledger-dir) LEDGER_DIR="$2"; shift 2 ;;
    --note) NOTE="$2"; shift 2 ;;
    --no-trace-control) INVARIANCE=1; shift ;;
    -h|--help) usage ;;
    *) echo "ledger-run-one: unknown argument $1" >&2; usage ;;
  esac
done

for required in SWEEP_ID ARM BIN BIN_SHA FILE OUTDIR; do
  if [ -z "${!required}" ]; then
    echo "ledger-run-one: --${required,,} is required" >&2
    exit 2
  fi
done
[ -x "$BIN" ] || { echo "ledger-run-one: $BIN is not executable" >&2; exit 2; }
[ -r "$FILE" ] || { echo "ledger-run-one: $FILE is not readable" >&2; exit 2; }

REPO_ROOT="$(cd -- "$(dirname -- "$0")/.." && pwd)"
[ -n "$HOST" ] || HOST="$(uname -n)"
# A sharded sweep gives every shard its OWN ledger directory: two concurrent
# appends to one INDEX.tsv over NFS are a read-then-append race, and a row
# here can exceed the 4 KiB that makes an `O_APPEND` write atomic. The
# consolidation step registers the finished files sequentially
# (`outcome_ledger.py register`).
[ -n "$LEDGER_DIR" ] || LEDGER_DIR="${AXEYUM_LEDGER_DIR:-$REPO_ROOT/bench-results/ledger}"

# The corpus-RELATIVE path, never the basename. The 16-division board records
# basenames and 370 of its 3,200 resolve to more than one corpus file, so its
# population is not reconstructible from what is committed. This column is what
# makes a ledger row joinable at all.
REL="$FILE"
if [ -n "$CORPUS_ROOT" ]; then
  case "$FILE" in
    "$CORPUS_ROOT"*) REL="${FILE#"$CORPUS_ROOT"}" ;;
  esac
fi
REL="${REL#/}"

mkdir -p "$OUTDIR" || exit 2
# One capture file per (arm, file), named from the relative path so two arms of
# the same sweep never collide and a re-read does not have to guess.
SLUG="$(printf '%s' "$REL" | tr '/' '_')"
CAPTURE="$OUTDIR/${ARM}__${SLUG}.out"

# The 1-minute load average AT FILE START. Recorded per row rather than per
# sweep because it moves within one sweep: the same binary scored 77, 79 and 85
# on one division in a single day purely on ambient load, and a level with no
# load beside it cannot be read against another one.
LOAD="$(awk '{print $1}' /proc/loadavg 2>/dev/null)"
[ -n "$LOAD" ] || LOAD="unknown"

run_cli() {  # $1 = "trace" | "bare"; prints "<exit>\t<elapsed_ms>"; stdout -> $2
  local mode="$1" out="$2" t0 t1 rc
  local -a cmd=("timeout" "$((BUDGET_S + HEADROOM_S))")
  if [ -n "$CORE" ]; then cmd+=("taskset" "-c" "$CORE"); fi
  local flags="--timeout-ms $((BUDGET_S * 1000))"
  if [ "$mode" = "trace" ]; then flags="$flags --trace"; fi
  t0=$(date +%s%N)
  "${cmd[@]}" bash -c "ulimit -v $VLIMIT_KB; exec \"\$0\" \"\$1\" $flags" \
      "$BIN" "$FILE" > "$out" 2>/dev/null
  rc=$?
  t1=$(date +%s%N)
  printf '%s\t%s' "$rc" "$(( (t1 - t0) / 1000000 ))"
}

read -r RC ELAPSED_MS <<< "$(run_cli trace "$CAPTURE")"

python3 "$REPO_ROOT/scripts/outcome_ledger.py" \
  --ledger-dir "$LEDGER_DIR" \
  append \
  --capture "$CAPTURE" \
  --sweep-id "$SWEEP_ID" \
  --arm "$ARM" \
  --corpus-path "$REL" \
  --binary-sha "$BIN_SHA" \
  --exit-status "$RC" \
  --elapsed-ms "$ELAPSED_MS" \
  --host "$HOST" \
  --core "${CORE:-unpinned}" \
  --load "$LOAD" \
  --note "$NOTE" \
  --quiet
APPEND_RC=$?
if [ "$APPEND_RC" -ne 0 ]; then
  echo "ledger-run-one: APPEND FAILED for $REL (exit $APPEND_RC)" >&2
  exit 2
fi

# Verdict invariance. Two extractions of the same token, one from each capture,
# with `--trace` the only difference between the runs. `grep -m1 -oE` on the
# bare verdict line is the harness's own convention, kept identical on both
# sides so the comparison is of the RUNS and not of two readers.
verdict_of() { grep -m1 -oE '^(sat|unsat|unknown)$' -- "$1" 2>/dev/null || true; }
TRACED="$(verdict_of "$CAPTURE")"
if [ "$INVARIANCE" -eq 1 ]; then
  CONTROL="$CAPTURE.notrace"
  read -r _ _ <<< "$(run_cli bare "$CONTROL")"
  BARE="$(verdict_of "$CONTROL")"
  if [ "${TRACED:-none}" = "${BARE:-none}" ]; then
    echo "INVARIANCE ok $REL ${TRACED:-none}" >&2
  else
    echo "INVARIANCE MOVED $REL traced=${TRACED:-none} bare=${BARE:-none}" >&2
  fi
fi

printf 'LEDGER-ROW\t%s\t%s\t%s\t%s\t%s\n' "$SWEEP_ID" "$ARM" "$REL" "${TRACED:-none}" "$RC"
