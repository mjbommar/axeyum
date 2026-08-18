#!/usr/bin/env bash
# Prelude reuse differential gate (ADR-0464).
#
# Process-wide prelude reuse (`crates/axeyum-lean-kernel/src/prelude_cache.rs`)
# hands a caller a clone of a kernel built once per process instead of rebuilding
# it. The claim that makes that sound is narrow: a restored template is bit-
# exactly what a fresh build would have produced. The crate's own tests check
# that INSIDE one process by comparing whole exported environments.
#
# This script checks it from the OUTSIDE, on the binaries whose output the fact
# ledger actually consumes: every inventory example must produce BYTE-IDENTICAL
# stdout and stderr with reuse on (`AXEYUM_PRELUDE_CACHE=1`) and off
# (`AXEYUM_PRELUDE_CACHE=0`). Those two runs share no state, so agreement is a
# statement about the construction itself rather than about one process.
#
# WHY THE COUNTERS ARE CHECKED TOO. "The flag changed nothing" and "the flag was
# ignored" produce identical output, and this repository has shipped several
# gates that passed over zero work. Each example prints its reuse counters, so
# the script requires the cache-ON run to report hits>0 and the cache-OFF run to
# report hits=0. Without that, a typo in the variable name would make this gate
# compare a run to itself and pass forever.
#
# Usage:
#   scripts/check-prelude-reuse-equivalence.sh            # release (default)
#   AXEYUM_REUSE_GATE_PROFILE=debug scripts/…             # debug binaries
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

PROFILE="${AXEYUM_REUSE_GATE_PROFILE:-release}"
CARGO_FLAGS=()
if [ "$PROFILE" = "release" ]; then
    CARGO_FLAGS+=(--release)
fi

# Every example that builds a prelude and prints something a consumer reads,
# as `binary[:args]`. `prelude_build_timing` is deliberately EXCLUDED: it prints
# elapsed times, which are not reproducible and are exactly what this change
# alters.
#
# `nat_axiom_inventory` appears TWICE, and the second entry is the load-bearing
# one. Bare, it builds `logic, nat, real, integer, rat, string` and never the
# CONSTRUCTED carriers, so it is blind to the `PreludeKey::CReal` slot -- an
# empty result from a tool that was never pointed at the subject is
# indistinguishable from a strong negative result, and this repository has
# already read a `creal` zero out of a run that did not build `creal`. The
# `--include-constructed` entry is what puts `creal` and `complex` under the
# differential, which matters because a template slot wired to the wrong builder
# would hand back the AXIOMATIZED `Real` package under the name `CReal` and every
# "did it build?" check would still pass.
EXAMPLES=(
    nat_axiom_inventory
    nat_axiom_inventory:--include-constructed
    nat_theorem_inventory
    int_theorem_inventory
    theorem_axiom_footprint
    prelude_axiom_inventory
    arith_model_witness
    probe_add_structure
)

echo "== building examples (${PROFILE}) =="
if ! cargo build -q -p axeyum-lean-kernel "${CARGO_FLAGS[@]}" --examples; then
    echo "FAIL: examples did not build" >&2
    exit 1
fi

BIN_DIR="target/${PROFILE}/examples"
if [ -n "${CARGO_TARGET_DIR:-}" ]; then
    BIN_DIR="${CARGO_TARGET_DIR}/${PROFILE}/examples"
fi

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

failures=0
compared=0

for entry in "${EXAMPLES[@]}"; do
    example="${entry%%:*}"
    args=()
    if [ "$entry" != "$example" ]; then
        # shellcheck disable=SC2206 -- deliberate word splitting of the arg list
        args=(${entry#*:})
    fi
    label="${entry//[^A-Za-z0-9_.-]/_}"
    binary="${BIN_DIR}/${example}"
    if [ ! -x "$binary" ]; then
        echo "FAIL: ${entry}: binary not found at ${binary}" >&2
        failures=$((failures + 1))
        continue
    fi

    AXEYUM_PRELUDE_CACHE=1 "$binary" "${args[@]+"${args[@]}"}" \
        >"${WORK}/${label}.on.out" 2>"${WORK}/${label}.on.err"
    on_status=$?
    AXEYUM_PRELUDE_CACHE=0 "$binary" "${args[@]+"${args[@]}"}" \
        >"${WORK}/${label}.off.out" 2>"${WORK}/${label}.off.err"
    off_status=$?

    if [ "$on_status" -ne "$off_status" ]; then
        echo "FAIL: ${entry}: exit status differs (on=${on_status} off=${off_status})" >&2
        failures=$((failures + 1))
        continue
    fi

    if ! diff -q "${WORK}/${label}.on.out" "${WORK}/${label}.off.out" >/dev/null; then
        echo "FAIL: ${entry}: STDOUT differs between reuse on and off" >&2
        diff "${WORK}/${label}.off.out" "${WORK}/${label}.on.out" | head -20 >&2
        failures=$((failures + 1))
        continue
    fi

    if ! diff -q "${WORK}/${label}.on.err" "${WORK}/${label}.off.err" >/dev/null; then
        echo "FAIL: ${entry}: STDERR differs between reuse on and off" >&2
        diff "${WORK}/${label}.off.err" "${WORK}/${label}.on.err" | head -20 >&2
        failures=$((failures + 1))
        continue
    fi

    bytes=$(wc -c <"${WORK}/${label}.on.out")
    err_bytes=$(wc -c <"${WORK}/${label}.on.err")
    if [ "$bytes" -eq 0 ] && [ "$err_bytes" -eq 0 ]; then
        echo "FAIL: ${entry}: produced no output at all on either stream" >&2
        failures=$((failures + 1))
        continue
    fi

    compared=$((compared + 1))
    # BOTH streams, because several of these examples print their per-prelude
    # summary to STDERR and only the axiom rows to stdout -- `nat_axiom_inventory
    # --include-constructed` adds no stdout at all (creal and complex have no
    # axiom rows to print) and reporting stdout alone made the two entries look
    # like the same run.
    echo "ok: ${entry} identical (${bytes} stdout + ${err_bytes} stderr bytes)"
done

# The liveness half: prove the flag was honoured in BOTH directions, using the
# reuse counters rather than trusting that the environment variable took effect.
echo "== counter liveness =="
timing="${BIN_DIR}/prelude_build_timing"
if [ ! -x "$timing" ]; then
    echo "FAIL: prelude_build_timing binary not found at ${timing}" >&2
    exit 1
fi

on_line=$(AXEYUM_PRELUDE_CACHE=1 "$timing" 2 2>&1 >/dev/null | grep '^prelude-cache ')
off_line=$(AXEYUM_PRELUDE_CACHE=0 "$timing" 2 2>&1 >/dev/null | grep '^prelude-cache ')
echo "  cache on : ${on_line}"
echo "  cache off: ${off_line}"

on_hits=$(sed -n 's/.*hits=\([0-9]*\).*/\1/p' <<<"$on_line")
off_hits=$(sed -n 's/.*hits=\([0-9]*\).*/\1/p' <<<"$off_line")

if [ -z "$on_hits" ] || [ "$on_hits" -eq 0 ]; then
    echo "FAIL: reuse was ON but served zero restores -- this gate compared a run to itself" >&2
    failures=$((failures + 1))
fi
if [ -z "$off_hits" ] || [ "$off_hits" -ne 0 ]; then
    echo "FAIL: AXEYUM_PRELUDE_CACHE=0 still served ${off_hits} restores -- the flag is ignored" >&2
    failures=$((failures + 1))
fi

echo
echo "AXEYUM-PRELUDE-REUSE compared=${compared} failures=${failures}"

if [ "$compared" -lt "${#EXAMPLES[@]}" ]; then
    echo "FAIL: compared ${compared} of ${#EXAMPLES[@]} examples" >&2
    exit 1
fi
if [ "$failures" -ne 0 ]; then
    exit 1
fi
echo "PASS: prelude reuse is byte-identical to fresh construction"
