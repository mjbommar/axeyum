#!/usr/bin/env bash
# A/B sweep of `AXEYUM_EUF_ONLINE_ATOMS` over one division's committed parity
# list, ONE BINARY, one arm per invocation.
#
# WHY A SCRIPT AND NOT A COMMAND LINE. The 2026-09-08 `uf-arith-overbound` lane
# had to establish an A/B protocol after an unpinned baseline mixed two binaries
# in one sweep; the arm is an environment variable here for exactly that reason,
# so the two columns differ in nothing but the policy.
#
# Usage:
#   scripts/euf-online-atoms-sweep.sh <arm> <list.txt> <smtcomp_cli> <out.tsv> [slots] [budget_s]
#
#   <arm>  refuse | sliced | whole   (the `AXEYUM_EUF_ONLINE_ATOMS` value)
#
# Protocol matches scripts/parity-run.sh: per-file wall budget (default 24 s),
# 8 GiB `ulimit -v`, `AXEYUM_TRACE=1` so the route trail and the
# `; euf-online-atoms` line are recorded.
#
# Columns: file, verdict, wall_ms, euf_online_outcome, euf_online_ms,
#          decided_by, bound_by, atoms_line.
#
# `verdict` is `unsolved` for anything that is not `sat`/`unsat` — timeout,
# unknown, crash, OOM, parse failure — which is the denominator rule
# `parity-run.sh` fixes and this script does not get to renegotiate.
set -uo pipefail

ARM="${1:?arm: refuse|sliced|whole}"
LIST="${2:?benchmark list}"
BIN="${3:?smtcomp_cli binary}"
OUT_TSV="${4:?output tsv}"
SLOTS="${5:-6}"
BUDGET_S="${6:-24}"
MEM_GB=8

case "$ARM" in
  refuse | sliced | whole) ;;
  *)
    echo "euf-online-atoms-sweep: unknown arm '$ARM' (refuse|sliced|whole)" >&2
    exit 2
    ;;
esac

if [ ! -x "$BIN" ]; then
  echo "euf-online-atoms-sweep: $BIN is not executable" >&2
  exit 2
fi

run_one() {
  # One file, one process. Everything this function prints is one TSV row.
  local file="$1"
  local start_ns end_ns wall_ms out verdict trail atoms
  start_ns=$(date +%s%N)
  out=$(timeout -k 5 "$((BUDGET_S + 20))" env \
    AXEYUM_TRACE=1 "AXEYUM_EUF_ONLINE_ATOMS=$ARM" \
    bash -c 'ulimit -v $(( '"$MEM_GB"' * 1024 * 1024 )); exec "$@"' \
    _ "$BIN" "$file" --timeout-ms "$((BUDGET_S * 1000))" 2>&1)
  end_ns=$(date +%s%N)
  wall_ms=$(((end_ns - start_ns) / 1000000))

  verdict=$(printf '%s\n' "$out" | grep -oE '^(sat|unsat)$' | tail -1)
  verdict="${verdict:-unsolved}"
  trail=$(printf '%s\n' "$out" | grep -m1 'route-trail' || true)
  atoms=$(printf '%s\n' "$out" | grep -m1 'euf-online-atoms' || true)

  # The euf-online attempt's own outcome and cost, read out of the trail JSON.
  # A missing attempt is `not-reached`, which is a DIFFERENT finding from a
  # decline and must not print as one.
  python3 - "$verdict" "$wall_ms" "$file" <<'PY' "$trail" "$atoms"
import json
import re
import sys

verdict, wall_ms, file = sys.argv[1], sys.argv[2], sys.argv[3]
trail, atoms = sys.argv[4], sys.argv[5]

outcome, elapsed_ms, decided_by, bound_by = "not-reached", "", "", ""
match = re.search(r'(\{"schema_version".*\})\s*$', trail)
if match:
    try:
        data = json.loads(match.group(1))
    except json.JSONDecodeError:
        data = None
    if data:
        for attempt in data.get("attempts", []):
            if attempt.get("route") == "euf-online":
                outcome = attempt.get("outcome", "?")
                elapsed_ms = str(attempt.get("elapsed_ns", 0) // 1_000_000)
            if attempt.get("outcome") == "decided":
                decided_by = attempt.get("route", "")
bound = re.search(r"bound_by=(\S+)", trail)
if bound:
    bound_by = bound.group(1)

atoms_line = re.sub(r"^.*?euf-online-atoms", "euf-online-atoms", atoms).strip()
print(
    "\t".join(
        [file, verdict, wall_ms, outcome, elapsed_ms, decided_by, bound_by, atoms_line]
    )
)
PY
}
export -f run_one
export ARM BIN BUDGET_S MEM_GB

printf 'file\tverdict\twall_ms\teuf_online_outcome\teuf_online_ms\tdecided_by\tbound_by\tatoms_line\n' > "$OUT_TSV"
# `xargs -P` rather than a shell loop: the sweep is 200 files x 24 s and a
# serial run is 80 minutes per arm. Rows arrive out of order and are sorted
# below, so the artifact is deterministic even though the run is not.
xargs -a "$LIST" -d '\n' -I{} -P "$SLOTS" bash -c 'run_one "$@"' _ {} >> "$OUT_TSV".unsorted 2>/dev/null

sort "$OUT_TSV".unsorted >> "$OUT_TSV"
rm -f "$OUT_TSV".unsorted

decided=$(tail -n +2 "$OUT_TSV" | cut -f2 | grep -cE '^(sat|unsat)$')
total=$(tail -n +2 "$OUT_TSV" | wc -l)
echo "arm=$ARM decided=$decided/$total  -> $OUT_TSV" >&2
