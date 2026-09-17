#!/usr/bin/env bash
# One pinned core pair runs its queue of (population, arm set) jobs
# sequentially and writes a DONE marker line per job (ADR-2134's shape).
#
# The four queues, as launched 2026-09-17 (2 shards of every list; shard k is
# lines k*100+1 .. k*100+100):
#   s5 1,9   : lra.0 (4 arms) -> heldout.0 (4 arms) -> rdl.0 (2 arms)
#   s5 3,11  : lra.1 (4 arms) -> heldout.1 (4 arms) -> rdl.1 (2 arms)
#   s6 1,9   : uflra.0 (4 arms) -> idl.0 (2 arms) -> screen16.0 (2 arms)
#   s6 3,11  : uflra.1 (4 arms) -> idl.1 (2 arms) -> screen16.1 (2 arms)
#
# Arm sets:
#   FOUR  = base | nz (ADR-2146) | sp (ADR-2147) | both
#   TWO   = base | both                         (the DL controls)
#   S16   = s16 (AXEYUM_LRA_ATOM_SCREEN=16) | s16both (screen + both levers)
#           -- the composition the census population is defined under.
#
# Usage: drive-shard.sh <queue: lra|uflra> <shard 0|1> <cores> <workdir>
set -u
QUEUE="$1"; SHARD="$2"; CORES="$3"; DIR="$4"
here="$(cd "$(dirname "$0")" && pwd)"
BIN="$here/smtcomp_cli"
mkdir -p "$DIR/lists"
shard_list() {  # <list> -> path of this shard's 100 lines
  local src="$here/lists/$1.txt" dst="$DIR/lists/$1.$SHARD.txt"
  sed -n "$((SHARD * 100 + 1)),$((SHARD * 100 + 100))p" "$src" > "$dst"
  echo "$dst"
}
FOUR=(base=- nz=AXEYUM_LRA_ADMIT_NONZEROS=1 sp=AXEYUM_LRA_DISEQ_SPLIT=1 "both=AXEYUM_LRA_ADMIT_NONZEROS=1 AXEYUM_LRA_DISEQ_SPLIT=1")
TWO=(base=- "both=AXEYUM_LRA_ADMIT_NONZEROS=1 AXEYUM_LRA_DISEQ_SPLIT=1")
S16=(s16=AXEYUM_LRA_ATOM_SCREEN=16 "s16both=AXEYUM_LRA_ATOM_SCREEN=16 AXEYUM_LRA_ADMIT_NONZEROS=1 AXEYUM_LRA_DISEQ_SPLIT=1")
DONE="$DIR/$QUEUE.$SHARD.done"
: > "$DONE"
run() {  # <tag> <listname> <arms...>
  local tag="$1" list="$2"; shift 2
  local l; l=$(shard_list "$list")
  "$here/ab-arms.sh" "$tag.$SHARD" "$l" "$DIR/$tag.$SHARD.tsv" "$CORES" "$BIN" 24 "$@" \
    > "$DIR/$tag.$SHARD.log" 2>&1
  echo "$tag.$SHARD EXIT=$? $(date -Is)" >> "$DONE"
}
case "$QUEUE" in
  lra)
    run lra QF_LRA-pinned "${FOUR[@]}"
    run heldout QF_LRA-heldout "${FOUR[@]}"
    run rdl QF_RDL-pinned "${TWO[@]}"
    ;;
  uflra)
    run uflra QF_UFLRA-pinned "${FOUR[@]}"
    run idl QF_IDL-pinned "${TWO[@]}"
    run screen16 QF_LRA-pinned "${S16[@]}"
    ;;
  *) echo "unknown queue $QUEUE"; exit 2 ;;
esac
echo "ALLDONE $(date -Is)" >> "$DONE"
