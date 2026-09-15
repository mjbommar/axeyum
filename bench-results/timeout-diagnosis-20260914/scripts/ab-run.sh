#!/usr/bin/env bash
# TIMEOUT-DIAGNOSIS interleaved per-file A/B (ADR-2060).
#
# POLARITY, stated here so no reader has to infer it from a column name:
#
#   BASE = `smtcomp_cli` built from `main` @ 91c721f8e -- the merge base, where
#          `Decision::TimedOut` is a unit variant rendered as one fixed sentence
#          about the Fourier-Motzkin elimination for all six of its producers.
#
#   ARM  = `smtcomp_cli` built from this lane's branch -- where the variant is
#          `Decision::GaveUp(GaveUp)` with a reason per gate, and the `i128`
#          overflow producer is `Decision::Incomplete` instead.
#
# A GAIN is therefore "the ARM decided a file the BASE did not". The registered
# prediction is that there are none IN EITHER DIRECTION: this is a diagnosis
# change and every routing decision is unchanged by construction.
#
# TWO BINARIES, not one binary under two env values. The standing rule prefers
# one binary because a second build confounds the arm with everything else that
# changed between the two trees; here there is nothing else, and the change is
# unconditional code with no knob to flip, so a one-binary A/B is not available.
# Both are `--release` builds of `scripts/lane-snapshot.sh` extractions. The
# script REFUSES if the two binaries hash the same, because two identical arms
# would make every comparison below vacuous while looking like agreement.
#
# THREE CHANNELS, and they do not all have the same rule (PREREGISTRATION.md R2):
#   verdict      MUST NOT MOVE
#   exit status  MUST NOT MOVE  (ADR-2045's lever read losses=0 by verdict while
#                                creating five new aborts on clean files)
#   give-up      MUST MOVE      (if it moves on zero rows the arms are the same
#                                binary and the run is discarded, not reported)
#
# Both arms run with `--trace`, so the give-up channel exists for both and the
# verdict comparison is between two runs identical in everything but the binary.
#
# Usage: ab-run.sh <tag> <list> <out.tsv> <logdir> <cores> <base_bin> <arm_bin> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; LOGD="$4"; PIN="$5"; BASE_BIN="$6"; ARM_BIN="$7"
BUDGET="${8:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))   # 8 GiB, identical to the board run

[ -x "$BASE_BIN" ] || { echo "ABORT $TAG: $BASE_BIN missing"; exit 2; }
[ -x "$ARM_BIN" ]  || { echo "ABORT $TAG: $ARM_BIN missing";  exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT non-empty"; exit 2; }
hb=$(sha256sum "$BASE_BIN" | cut -c1-16)
ha=$(sha256sum "$ARM_BIN"  | cut -c1-16)
[ "$hb" = "$ha" ] && { echo "ABORT $TAG: the two arms are the SAME binary ($hb)"; exit 2; }
echo "$TAG base=$hb arm=$ha pin=$PIN budget=${BUDGET}s"
mkdir -p "$LOGD"

# One run. Echoes: verdict \t exit \t wall_ms \t giveup \t stderr1
run() {   # $1 = binary, $2 = stdout path, $3 = stderr path
  local bin="$1" so="$2" se="$3" t0 t1 rc v g e
  t0=$(date +%s%N)
  ( ulimit -v $VLIM
    exec timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      "$bin" "$f" --timeout-ms $((BUDGET * 1000)) --trace
  ) > "$so" 2> "$se"
  rc=$?
  t1=$(date +%s%N)
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' "$so")
  # EVERY give-up line, joined -- not just the first. A run that gives up more
  # than once must not be collapsed to one label.
  g=$(grep -h '^; give-up' "$so" 2>/dev/null | tr '\t' ' ' | paste -sd '~' -)
  e=$(grep -m1 -v '^[[:space:]]*$' "$se" 2>/dev/null | tr '\t' ' ' | cut -c1-200)
  printf '%s\t%s\t%s\t%s\t%s' \
    "${v:-none}" "$rc" "$(( (t1 - t0) / 1000000 ))" "${g:-none}" "${e:-none}"
}

printf 'file\tbase\tbase_rc\tbase_ms\tbase_giveup\tbase_err\tarm\tarm_rc\tarm_ms\tarm_giveup\tarm_err\tfirst\tstatus\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  key=$(printf '%s' "$f" | sha1sum | cut -c1-12)
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  if [ $((n % 2)) -eq 1 ]; then
    b=$(run "$BASE_BIN" "$LOGD/$key.B.out" "$LOGD/$key.B.err")
    a=$(run "$ARM_BIN"  "$LOGD/$key.A.out" "$LOGD/$key.A.err")
    first=base
  else
    a=$(run "$ARM_BIN"  "$LOGD/$key.A.out" "$LOGD/$key.A.err")
    b=$(run "$BASE_BIN" "$LOGD/$key.B.out" "$LOGD/$key.B.err")
    first=arm
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$f" "$b" "$a" "$first" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB_COMPLETE $TAG rows=$(( $(wc -l < "$OUT") - 1 ))"
