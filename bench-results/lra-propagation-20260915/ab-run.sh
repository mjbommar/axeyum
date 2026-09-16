#!/usr/bin/env bash
# ADR-2122: interleaved per-file A/B of ONE BINARY under TWO ENV VALUES.
#
#   A = AXEYUM_LRA_BOUND_PROPAGATION=off   (the shipped default)
#   B = AXEYUM_LRA_BOUND_PROPAGATION=on    (implied-bound propagation)
#
# # Why one binary here, where ADR-2100's runner needed two
#
# ADR-2100 is unconditional code, so its arms HAD to be two builds, and its
# runner refuses unless the two hash differently -- because two identical arms
# produce a perfect zero that looks exactly like agreement. This change is a
# lever, so the same risk exists in a different place: two arms that differ only
# in an environment variable the binary never READS are equally vacuous and
# equally invisible.
#
# So the guard is moved rather than dropped. `--mechanism-check` runs one file
# under both values and requires `implied_bound_passes` to be absent-or-zero in
# A and NONZERO in B. A run that cannot show that is refused, exactly as a run
# with two identical binaries is.
#
# Using one binary also removes a confound the two-binary form has: arm A here
# is the SAME machine code as arm B, so a difference cannot be a codegen or
# layout accident. `off` allocates no table and returns on the pass's first
# line, which is what makes it the shipped behaviour rather than an
# approximation of it.
#
# Both arms run BACK TO BACK on the SAME file on the SAME pinned core, and the
# arm order alternates per file, so ambient load cancels in the DIFFERENCE
# rather than landing on whichever arm ran second -- load has moved 23 verdicts
# in one division at fixed code on these boxes.
#
# EXIT STATUS is its own column per arm and is never folded into the verdict:
# ADR-2045 measured `losses=0` by verdict with five new ABORTS underneath it.
#
# Envelope: 24 s wall, 8 GiB `ulimit -v`, one pinned physical core pair.
#
# Usage: ab-run.sh <tag> <list> <out.tsv> <cores> <bin> [budget_s]
#        ab-run.sh --mechanism-check <file> <cores> <bin>
set -u

if [ "${1:-}" = "--mechanism-check" ]; then
  F="$2"; PIN="$3"; AX="$4"
  probe() {
    AXEYUM_LRA_BOUND_PROPAGATION="$1" timeout 60 taskset -c "$PIN" \
      bash -c "ulimit -v $((8 * 1024 * 1024)); exec \"\$0\" \"\$1\" --trace --timeout-ms 24000" \
      "$AX" "$F" 2>/dev/null | tr ' ' '\n' | sed -n 's/^implied_bound_passes=//p' | head -1
  }
  A=$(probe off); B=$(probe on)
  echo "mechanism-check: off=${A:-<absent>} on=${B:-<absent>}"
  # NOTE the single quotes: backticks inside DOUBLE quotes are command
  # substitution, so the obvious `off` in a message would try to RUN `off`,
  # print nothing, and leave a guard that says something different from what it
  # was written to say.
  case "${A:-0}" in
    ''|0|n/a) ;;
    *) echo 'FAIL: arm A ran passes; the off arm must run none'; exit 3;;
  esac
  case "${B:-0}" in
    ''|0|n/a)
      echo 'FAIL: arm B ran no pass at all. The lever is INERT on this file, and'
      echo '      every number from this A/B would be a comparison of off with off'
      echo '      -- a perfect zero that looks exactly like agreement.'
      exit 3;;
  esac
  echo "mechanism-check OK: the lever moves the engine on this file"
  exit 0
fi

TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT $TAG: $LIST unreadable"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }
H=$(sha256sum "$AX" | cut -d' ' -f1)

run_arm() {  # $1 = the lever value
  local t0 t1 raw rc v
  t0=$(date +%s%N)
  raw=$(AXEYUM_LRA_BOUND_PROPAGATION="$1" \
        timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s' "${v:-none}" "$(( (t1 - t0) / 1000000 ))" "$rc"
}

printf 'file\tA\tA_ms\tA_rc\tB\tB_ms\tB_rc\tfirst\tstatus\n' > "$OUT"
n=0
while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  [ -r "$f" ] || { echo "UNREADABLE $rel" >&2; continue; }
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  if [ $((n % 2)) -eq 1 ]; then
    first=A; a=$(run_arm off); b=$(run_arm on)
  else
    first=B; b=$(run_arm on); a=$(run_arm off)
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$rel" "$a" "$b" "$first" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB-DONE $TAG $n files -> $OUT  binary=$H"
