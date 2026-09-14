#!/usr/bin/env bash
# ADR-2035 -- REUSED VERBATIM from bench-results/decline-wiring-20260914,
# except for this header. Re-runs every MOVED row 3x per arm and classifies it.
#
# A row that moved once is not a result. STABLE-GAIN requires 3-for-3 in the
# gain direction on both arms; anything else is UNSTABLE and does not count
# toward the ship threshold.
#
# [ADR-2030]'s every LOSS was ONE row that lost in BOTH arms with different code
# and then inverted under re-runs -- the same row a byte-identical noise floor
# decides. So a single moved row is assumed to be inside the band until this
# says otherwise.
#
# Run on the SAME binary as the A/B here (sha256 printed below and in every
# runner log), because this lane's branch did not move between the two.
#
# Usage: rerun-moved.sh <file-with-one-path-per-line> <out.tsv> <core> <bin> <VAR> <VALUE> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; VAR="$5"; VALUE="$6"; BUDGET="${7:-24}"
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
VLIM=$((8 * 1024 * 1024))
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
echo "RERUN core=$PIN var=$VAR value=$VALUE sha256=$(sha256sum "$AX" | cut -d' ' -f1)"

one() {
  local mode="$1" f="$2" raw v
  if [ "$mode" = off ]; then
    raw=$(env -u "$VAR" timeout $((BUDGET + 16)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$CORPUS/$f" 2>&1)
  else
    raw=$(env "$VAR=$VALUE" timeout $((BUDGET + 16)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$CORPUS/$f" 2>&1)
  fi
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$'); printf '%s' "${v:-NONE}"
}

printf 'file\toff1\toff2\toff3\ton1\ton2\ton3\tclass\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  # Interleaved, same core, alternating: off on off on off on.
  o1=$(one off "$f"); n1=$(one on "$f")
  n2=$(one on "$f");  o2=$(one off "$f")
  o3=$(one off "$f"); n3=$(one on "$f")
  dec() { case "$1" in sat|unsat) return 0;; *) return 1;; esac; }
  offd=0; ond=0
  for v in "$o1" "$o2" "$o3"; do dec "$v" && offd=$((offd + 1)); done
  for v in "$n1" "$n2" "$n3"; do dec "$v" && ond=$((ond + 1)); done
  flip=no
  for a in "$o1" "$o2" "$o3"; do
    for b in "$n1" "$n2" "$n3"; do
      if dec "$a" && dec "$b" && [ "$a" != "$b" ]; then flip=yes; fi
    done
  done
  if [ "$flip" = yes ]; then cls=FLIP
  elif [ "$offd" -eq 0 ] && [ "$ond" -eq 3 ]; then cls=STABLE-GAIN
  elif [ "$offd" -eq 3 ] && [ "$ond" -eq 0 ]; then cls=STABLE-LOSS
  else cls=UNSTABLE
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$o1" "$o2" "$o3" "$n1" "$n2" "$n3" "$cls" >> "$OUT"
  echo "done $f -> $cls (off decided $offd/3, on decided $ond/3)"
done < "$LIST"
echo "DONE $OUT"
