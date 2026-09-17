#!/usr/bin/env bash
# One pinned core pair runs its half of the PINNED list, then its half of the
# HELD-OUT list, sequentially, and writes a DONE marker per population.
#
# Output names carry the shard and the population so two invocations on
# different shards cannot write the same file (ADR-2134's README §5: a
# duplicate launch once truncated a sizing run's output while rewriting it).
#
# Usage: drive-shard.sh <shard 0|1> <cores> <workdir> <bin>
set -u
SHARD="$1"; CORES="$2"; DIR="$3"; BIN="$4"
here="$(cd "$(dirname "$0")" && pwd)"
export AXEYUM_ARMS_SRC="$here/nra_real_root.rs"
: > "$DIR/shard$SHARD.done"
for pop in qfnra heldout; do
  "$here/ab-cad-env.sh" "$pop.$SHARD" "$here/$pop-shard$SHARD.txt" \
      "$DIR/$pop-shard$SHARD.tsv" "$CORES" "$BIN" 24 single-cell algebraic-witness \
      > "$DIR/$pop-shard$SHARD.log" 2>&1
  echo "$pop shard$SHARD EXIT=$?" >> "$DIR/shard$SHARD.done"
done
echo "ALLDONE" >> "$DIR/shard$SHARD.done"
