#!/usr/bin/env bash
# Emit the files a pass left `unsolved`, as the input list for the next pass.
#
# The confirm pass re-runs ONLY these. That asymmetry is deliberate and it is
# what makes the two-pass result honest in the direction that matters: a second
# pass can only move a file OFF the loss list, never onto it, so the loss list
# is an upper bound refined downward and the "already decided" count is a LOWER
# bound (contention only ever makes deciding harder).
#
# Usage: unsolved-of.sh <pass-tsv> > <list>
set -uo pipefail
awk -F'\t' 'NR > 1 && $3 == "unsolved" { print $1 }' "$1"
