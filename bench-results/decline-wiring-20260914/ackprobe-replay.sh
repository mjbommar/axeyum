#!/usr/bin/env bash
# ADR-2030 -- the SAME ordering question, but inside the held-set REPLAY probe,
# which is where ADR-2020's 17 censused replays actually live.
#
# `ackprobe.sh` measures the shipped 24 s path. The replay probe re-runs a
# DISCARDED ground set on its own fresh budget, and although it enters the very
# same `check_auto`, "the same dispatcher" is an argument and this is a
# measurement. Both instruments are on here at once:
#
#   AXEYUM_QPROBE_HELD_SET_REPLAY=10000   the replay probe, 10 s per replay
#   AXEYUM_ACKPROBE=1                      the ordered Ackermann-site log
#
# The question: when a replay's `why=` is the `combined theories:` eager
# Ackermann refusal -- the string ADR-2020 censused 17 times -- was the route
# selector at `auto.rs:4068` engaged on the same term set BEFORE it?
#
# This is a DIAGNOSTIC, not an arm. Both variables only print. It is therefore
# not pinned to a reserved core: what it measures is the ORDER of lines, which
# ambient load does not reorder.
set -u
LIST="$1"; OUT="$2"; AX="$3"; LOGDIR="$4"; BUDGET="${5:-24}"
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
mkdir -p "$LOGDIR"

printf 'file\treplays\tcombined_replays\tpreceded_by_engaged\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  slug=$(printf '%s' "$f" | tr '/' '_')
  AXEYUM_ACKPROBE=1 AXEYUM_QPROBE_HELD_SET_REPLAY=10000 \
    timeout $((BUDGET + 40)) \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
    "$AX" "$CORPUS/$f" > /dev/null 2> "$LOGDIR/$slug.err"
  python3 - "$LOGDIR/$slug.err" "$f" >> "$OUT" <<'PY'
import re, sys
lines = open(sys.argv[1], errors="replace").read().splitlines()
ENG = re.compile(r"site=auto\.rs:4068 pairs=(\d+) .*engaged=true")
REPLAY = re.compile(r"QPROBE held-set-replay ")
COMBINED = re.compile(r"why=\w+\|combined_theories:")
replays = combined = preceded = 0
for i, line in enumerate(lines):
    if not REPLAY.search(line):
        continue
    replays += 1
    if not COMBINED.search(line):
        continue
    combined += 1
    # Was the selector engaged anywhere in the replay that produced this line?
    # The replay starts after the previous QPROBE held-set-replay line.
    start = 0
    for j in range(i - 1, -1, -1):
        if REPLAY.search(lines[j]):
            start = j + 1
            break
    if any(ENG.search(l) for l in lines[start:i]):
        preceded += 1
print(f"{sys.argv[2]}\t{replays}\t{combined}\t{preceded}")
PY
  echo "done $f"
done < "$LIST"
echo "DONE $OUT"
