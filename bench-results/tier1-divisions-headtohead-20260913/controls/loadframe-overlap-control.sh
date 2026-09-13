#!/usr/bin/env bash
# `loadframe.sh`'s OVERLAP column is the instrument behind this lane's only
# reference-frame claim ("no foreign pin held a core this board was using").
# A column that can only ever print `ok` would make that claim unfalsifiable,
# which is precisely the failure this repository keeps buying.
#
# So: run the classifier over pin specs whose answers are known, in BOTH
# directions.  It must fire on every spec that touches logical 5, 13, 6 or 14
# (and on any range spec, which cannot be tested by membership), and must stay
# silent on every spec that does not.
#
# THE CLASSIFIER IS EXTRACTED FROM `loadframe.sh`, NOT RE-TYPED.  A control that
# re-implements its subject passes while the shipped code is broken -- the
# 'a test must consume the declaration it names' failure, found twice in one
# evening in this repository.  The text between the `overlap-classifier`
# markers in loadframe.sh is what runs below, so a mutation of the shipped
# patterns changes what this suite measures.
set -u
cd "$(dirname "$0")"
LF=../loadframe.sh

BODY=$(sed -n '/>>> overlap-classifier/,/<<< overlap-classifier/p' "$LF")
[ -n "$BODY" ] \
  || { echo "FAIL: could not extract the classifier from loadframe.sh"; exit 1; }
# A non-empty extraction is not enough: an extraction that lost the case blocks
# would define a function that always returns `ok` and every MUST-fire row
# below would fail with a confusing message.  Say so here instead.
printf '%s' "$BODY" | grep -q 'esac' \
  || { echo "FAIL: the extracted classifier contains no case block"; exit 1; }

eval "classify() { local spec=\"\$1\" ov=ok
$BODY
printf '%s' \"\$ov\"; }"

fail=0
check() { # spec expected
  got=$(classify "$1")
  if [ "$got" != "$2" ]; then
    echo "FAIL: spec '$1' -> $got, expected $2"
    fail=1
  fi
}

# MUST fire -- these hold a core this board uses.
check '5'      OVERLAP
check '6'      OVERLAP
check '13'     OVERLAP
check '14'     OVERLAP
check '5,13'   OVERLAP
check '4,5'    OVERLAP
check '0,6'    OVERLAP
check '0-7'    OVERLAP   # range: untestable by membership, flagged on purpose

# MUST stay silent -- the inverted half.  A detector that flagged these would
# make its OVERLAP worth as little as one that never flags.
check '0'      ok
check '2'      ok
check '4'      ok
check '0,8'    ok
check '2,10'   ok
check '15'     ok        # contains '5' as a DIGIT, not as a CPU
check '1,3'    ok
check '12'     ok        # contains '2', and '1' next to '2'

[ "$fail" = 0 ] && echo "LOADFRAME-OVERLAP-OK: fires on 8 overlapping specs, silent on 8 clear ones"
exit "$fail"
