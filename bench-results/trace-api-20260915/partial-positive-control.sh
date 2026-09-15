#!/usr/bin/env bash
# ADR-2101 exit criterion C: the `partial` field, exercised end to end.
#
# Run the shipped CLI on a file that CANNOT finish in the budget -- one of
# ADR-2075's twelve `UFNIA` rows, wall-limited so the watchdog fires -- and
# show that
#
#   1. the emitted trail is schema 2 and says `"partial":true` in the FIELD,
#      not only in the `; partial ` prose prefix;
#   2. `scripts/route_trace_reader.py` accepts it, reports `partial=yes` with
#      `partial_source=field`, and still names a real `bound_by`;
#   3. the aggregate REFUSES to sum `decided_by` over it unless told.
#
# The negative half is the point.  A control that only shows the reader
# ACCEPTING a partial reading would pass on a reader that accepted everything,
# so a completed run is put through the same three checks and must come out the
# other way.
#
#   partial-positive-control.sh [out_dir]
set -u

W="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OUT="${1:-$W/bench-results/trace-api-20260915/control}"
CLI="${TA_CLI:-$W/target/release/examples/smtcomp_cli}"
CORPUS="${TA_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"

# One of ADR-2075's twelve, and the one whose committed receipt carries the
# fourteen `; partial ` lines the ADR quotes.
KILLED="UFNIA/lahiri-cav09-storm-queries/mqueue_example_2_2_2_4.smt2"
# A file that finishes well inside any budget, so the negative half is real.
FINISHES="${TA_FINISHES:-$W/corpus/qfbv-curated/crafted__bitops0.smt2}"

BUDGET_MS="${TA_BUDGET_MS:-6000}"

mkdir -p "$OUT" || exit 2
[ -x "$CLI" ] || { echo "ABORT: no CLI at $CLI (cargo build --release -p axeyum-bench --example smtcomp_cli)"; exit 2; }
[ -f "$CORPUS/$KILLED" ] || { echo "ABORT: corpus file missing: $CORPUS/$KILLED"; exit 2; }
[ -f "$FINISHES" ] || { echo "ABORT: negative-half file missing: $FINISHES"; exit 2; }

run_one() {
  local label="$1" path="$2" budget="$3"
  AXEYUM_TRACE=1 timeout -k 5 120 "$CLI" "$path" \
    --timeout-ms "$budget" --trace > "$OUT/$label.log" 2>&1
  echo "  $label: rc=$? verdict=$(tail -1 "$OUT/$label.log")"
}

echo "== running =="
run_one killed "$CORPUS/$KILLED" "$BUDGET_MS"
run_one finishes "$FINISHES" 60000
echo

echo "== the two route-trail lines, verbatim (first 240 bytes) =="
for label in killed finishes; do
  line=$(grep -m1 -E '^; (partial )?route-trail ' "$OUT/$label.log")
  if [ -z "$line" ]; then
    echo "  $label: NO TRAIL LINE"
  else
    echo "  $label: ${line:0:240}"
  fi
done
echo

echo "== the reader =="
python3 "$W/scripts/route_trace_reader.py" "$OUT/killed.log" "$OUT/finishes.log"
echo

echo "== the aggregate, both directions =="
python3 - "$W" "$OUT" <<'PY'
import sys

root, out = sys.argv[1], sys.argv[2]
sys.path.insert(0, root + "/scripts")
import route_trace_reader as rtr

killed = rtr.read_file(out + "/killed.log")
finishes = rtr.read_file(out + "/finishes.log")

rc = 0


def say(ok, text):
    global rc
    print(f"  [{'OK  ' if ok else 'FAIL'}] {text}")
    if not ok:
        rc = 1


say(killed.partial is True, f"killed run is PARTIAL (partial={killed.partial})")
say(
    killed.partial_source == "field",
    f"…and it came from the FIELD, not the prefix (source={killed.partial_source})",
)
say(killed.schema_version == 2, f"…schema {killed.schema_version}")
say(
    killed.bound_by is not None,
    f"…and it still names a bound_by the old `^; route ` grep could not see: {killed.bound_by}",
)
say(
    killed.in_flight_after is not None and killed.open_segment_ns is not None,
    f"…with the boundary and the open segment: after={killed.in_flight_after} "
    f"open_ms={None if killed.open_segment_ns is None else killed.open_segment_ns // 1_000_000}",
)

# The NEGATIVE half: a completed run must come out the other way, or the
# assertions above would pass on a reader that marked everything partial.
say(finishes.partial is False, f"completed run is NOT partial (partial={finishes.partial})")
say(
    finishes.decided_by is not None,
    f"…and it has a decider: {finishes.decided_by} -> {finishes.verdict}",
)

try:
    rtr.decided_by_counts([killed, finishes])
except rtr.PartialInAggregate as exc:
    say(True, f"the aggregate REFUSED the mix: {exc}")
else:
    say(False, "the aggregate summed a partial reading as a total")

told = rtr.decided_by_counts([killed, finishes], include_partial=True)
say(
    sum(told.values()) == 2,
    f"…and included it when told: {told}",
)

only_complete = rtr.decided_by_counts([finishes])
say(
    sum(only_complete.values()) == 1,
    f"…while the complete half alone needs no permission: {only_complete}",
)

sys.exit(rc)
PY
status=$?
echo
[ "$status" -eq 0 ] && echo "PARTIAL POSITIVE CONTROL: PASSED" || echo "PARTIAL POSITIVE CONTROL: FAILED"
exit "$status"
