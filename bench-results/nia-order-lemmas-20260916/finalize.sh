#!/usr/bin/env bash
# Pull the four A/B ledgers off the sweep host, analyse them, and write the
# mover list the 3x re-check consumes. Lane NIA-ORDER-LEMMAS, ADR-2136.
#
# It REFUSES on a short sweep rather than reporting percentages over whatever
# rows it found: a sweep that silently dropped files is a measurement of the
# subset that survived, and an analysis that cannot tell the difference is the
# shape ADR-2112 calls a tool that omits rather than refuses.
#
# usage: finalize.sh [remote-host] [remote-dir]
set -uo pipefail
HOST=${1:-s6}
RDIR=${2:-\~/nia-order-lemmas-20260916/out}
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

for f in ab-QF_NIA ab-QF_NRA ab-UFNIA ab-QF_NIA-heldout; do
    if ! ssh "$HOST" "cat $RDIR/$f.tsv" > "$HERE/$f.tsv" 2>/dev/null; then
        echo "ABORT: could not fetch $f.tsv from $HOST:$RDIR" >&2
        exit 2
    fi
    printf '%-24s %s rows\n' "$f" "$(grep -c . "$HERE/$f.tsv")"
done

echo
echo "=== pinned divisions (QF_NIA target, QF_NRA control, UFNIA target) ==="
python3 "$HERE/analyse-ab.py" \
    --list-dir "$HERE/lists" \
    --movers-out "$HERE/movers-pinned.txt" \
    "$HERE/ab-QF_NIA.tsv" "$HERE/ab-QF_NRA.tsv" "$HERE/ab-UFNIA.tsv"
pinned=$?

echo
echo "=== held-out QF_NIA draw ==="
# The held-out list is not named `ab-list-<DIV>.txt`, so coverage is checked
# against its own file by a symlinked name the analyser can find.
ln -sf heldout-QF_NIA.txt "$HERE/lists/ab-list-QF_NIA-heldout.txt"
python3 "$HERE/analyse-ab.py" \
    --list-dir "$HERE/lists" \
    --movers-out "$HERE/movers-heldout.txt" \
    "$HERE/ab-QF_NIA-heldout.tsv"
heldout=$?

echo
echo "FINALIZE pinned_rc=$pinned heldout_rc=$heldout"
echo "movers to re-check 3x per arm:"
wc -l "$HERE/movers-pinned.txt" "$HERE/movers-heldout.txt"
[ "$pinned" -eq 0 ] && [ "$heldout" -eq 0 ]
