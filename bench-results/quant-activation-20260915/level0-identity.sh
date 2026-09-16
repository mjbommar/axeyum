#!/usr/bin/env bash
# QUANT-ACTIVATION -- is the SHIPPED arm actually unchanged?
#
#   level0-identity.sh <list> <out.tsv> <pin> <bin-base> <bin-lever> [budget_s]
#
# THE A/B CANNOT ANSWER THIS. Both of its arms are the NEW binary, one with the
# variable unset; so it measures level 0 against level 1 and says nothing about
# level 0 against the code that shipped before. "Byte for byte the historical
# behaviour" is an ARGUMENT about `positive_path_step` at level 0 -- and the diff
# also touches `NestedDiscovery::stage`, which runs at EVERY level because it
# records the replacement certificate that did not exist before. That is exactly
# the kind of claim this repository requires measured rather than reasoned.
#
# So: the base binary (the lane's pre-Rust commit) against the lever binary with
# the variable UNSET, interleaved per file on one pinned core, at the same
# envelope. Any row where the two disagree is a change to the shipped arm.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX_BASE="$4"; AX_LEVER="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX_BASE" ] || { echo "ABORT: $AX_BASE missing"; exit 2; }
[ -x "$AX_LEVER" ] || { echo "ABORT: $AX_LEVER missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }
HA=$(sha256sum "$AX_BASE" | cut -d' ' -f1)
HB=$(sha256sum "$AX_LEVER" | cut -d' ' -f1)
[ "$HA" = "$HB" ] && { echo "ABORT: both arms are the SAME binary"; exit 2; }

one() {  # $1 = binary; the variable is UNSET on both, deliberately
  local raw rc v
  raw=$(env -u AXEYUM_QINST_POSITIVE_PATH \
          timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$1" "$f" 2>/dev/null)
  rc=$?
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s' "${v:-none}" "$rc"
}

printf 'file\tbase\tbase_rc\tlevel0\tlevel0_rc\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  case "$f" in /*) : ;; *) f="$CORPUS$f" ;; esac
  if [ $((n % 2)) -eq 0 ]; then
    a=$(one "$AX_BASE"); b=$(one "$AX_LEVER")
  else
    b=$(one "$AX_LEVER"); a=$(one "$AX_BASE")
  fi
  printf '%s\t%s\t%s\n' "${f#"$CORPUS"}" "$a" "$b" >> "$OUT"
  n=$((n + 1))
done < "$LIST"
echo "LEVEL0-IDENTITY-DONE $n files -> $OUT"
