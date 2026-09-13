#!/usr/bin/env bash
# `check-artifact-integrity.py` passes over the real artifacts, which tells you
# nothing about whether it can fail.  This corrupts the DATA in five known ways
# -- one per property it claims to check -- in a scratch copy, and requires each
# corruption to be reported.
#
# Corrupting the data rather than the checker is the right mutation here: the
# checker's job is to notice that three files disagree, so the mutation has to
# be a disagreement.  Mutating the checker would only show that its own code is
# reachable.
set -u
cd "$(dirname "$0")"
LANE=$(cd .. && pwd)
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0

prep() { # -> a fresh scratch copy of the lane in $T/lane
  # `check-artifact-integrity.py` resolves the pinned lists as ../parity-lists,
  # so the scratch tree needs that directory beside the lane copy.  Without it
  # the checker fails for the WRONG reason and every corruption below would
  # "pass" on a missing-input error rather than on the corruption.
  rm -rf "$T/lane" "$T/parity-lists"
  cp -r "$LANE" "$T/lane"
  cp -r "$LANE/../parity-lists" "$T/parity-lists"
}
run() { (cd "$T/lane" && python3 check-artifact-integrity.py 2>&1); }

expect() { # label must-contain
  local out rc
  out=$(run); rc=$?
  if [ "$rc" = 0 ]; then
    echo "FAIL: $1 -> checker exited 0 on corrupted artifacts"; fail=1; return
  fi
  grep -q "$2" <<<"$out" || { echo "FAIL: $1 -> did not report '$2'"; fail=1; }
}

# Baseline: the real artifacts must pass, or every result below is meaningless.
prep
if ! run > /dev/null; then
  echo "FAIL: the UNCORRUPTED artifacts do not pass"; exit 1
fi

# 1. board no longer the pinned list: drop its last row.
prep
sed -i '$d' "$T/lane/ABV.tsv"
expect "board short of the pinned 200" "not the pinned list in order"

# 2. winnable list disagrees with the board: delete a line from it.
prep
sed -i '1d' "$T/lane/winnable/ALIA.txt"
expect "winnable list disagrees with the board" "winnable list disagrees"

# 3. census does not cover the winnable set: drop a census row.
prep
sed -i '2d' "$T/lane/census/ALIA.tsv"
expect "census short of the winnable set" "census does not cover"

# 4. a census row DECIDED a file the board called winnable.
prep
python3 - "$T/lane/census/ABV.tsv" <<'PY'
import pathlib, sys
p = pathlib.Path(sys.argv[1])
ls = p.read_text().rstrip("\n").split("\n")
f = ls[1].split("\t"); f[1] = "unsat"; ls[1] = "\t".join(f)
p.write_text("\n".join(ls) + "\n")
PY
expect "census contradicts the board" "DECIDED a file"

# 5. a missing winnable list is not the same as an empty one.
prep
rm "$T/lane/winnable/ABV.txt"
expect "winnable list absent" "winnable list is ABSENT"

# INVERTED HALF: a change that is NOT a violation must not be reported.  The
# board's TIMING columns are free to differ between runs; only verdicts and
# coverage are checked.  A checker that flagged this would fail on any re-run.
prep
python3 - "$T/lane/ABV.tsv" <<'PY'
import pathlib, sys
p = pathlib.Path(sys.argv[1])
ls = p.read_text().rstrip("\n").split("\n")
f = ls[1].split("\t"); f[2] = "23.99"; ls[1] = "\t".join(f)
p.write_text("\n".join(ls) + "\n")
PY
if ! run > /dev/null; then
  echo "FAIL: a changed TIMING was reported as an integrity violation"; fail=1
fi

[ "$fail" = 0 ] && echo "INTEGRITY-CONTROL-OK: 5 corruptions caught, 1 harmless change ignored"
exit "$fail"
