#!/usr/bin/env bash
# The mutation battery against the code that SHIPS, not the code the tests were
# first written against. Every mutant gets an external wall bound, because
# `no-tightening` does not fail -- it grinds, and "the suite never returned" has
# to be recorded as a kill of a different kind rather than confused with a pass.
set -u
SNAP="$1"
OUT="$2"
FILTERS="lra::warm lia_online::tests::warm_theory lia_online::tests::the_shipped lia_online::tests::dropping_the_rational"

run_arm() {
  local label="$1"
  echo "=== $label" >> "$OUT"
  (
    cd "$SNAP" || exit 1
    # shellcheck disable=SC2086
    timeout -k 5 300 cargo test -p axeyum-solver --lib --features full -- --test-threads=4 $FILTERS 2>&1
    echo "ARM_EXIT=$?"
  ) | grep -E "^test |^test result|^error|^ARM_EXIT" >> "$OUT"
}

: > "$OUT"
python3 /tmp/lia-warm-mutate.py "$SNAP" restore >/dev/null
run_arm "BASELINE (unmutated)"

for m in stale-columns unchecked-prefix stale-constraints no-tightening sorted-columns; do
  python3 /tmp/lia-warm-mutate.py "$SNAP" restore >/dev/null
  if ! python3 /tmp/lia-warm-mutate.py "$SNAP" "$m" >/dev/null; then
    echo "=== $m: ANCHOR MISS" >> "$OUT"
    continue
  fi
  run_arm "MUTANT $m"
done

python3 /tmp/lia-warm-mutate.py "$SNAP" restore >/dev/null
echo "=== done" >> "$OUT"
