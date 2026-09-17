#!/usr/bin/env bash
# Gate for the cindergraph → Axeyum → sanitizer replay example
# (`python/examples/cindergraph_defects/`, item 16 of
# docs/plan/improvement-list-2026-09-16.md).
#
# Until 2026-09-17 `check.py` was an example with an exit status: it lifted
# twelve C samples into QF_BV, replayed every witness under a sanitizer, and
# exited 1 when one did not reproduce -- and nothing ran it. An unrun check is
# not a check. This wrapper is what puts it on the automatic path (`just
# py-check`, the Python block of `scripts/check.sh`) and, following the
# discipline every gate here keeps, makes the exit status depend on a SECOND
# reading of the evidence rather than on the driver's own opinion of itself:
#
#   1. It REFUSES (exit 2) when the toolchain the sweep needs is not there --
#      no `.venv`, no importable `axeyum._native`, no importable `cindergraph`.
#      A missing module must not be a green run. `uv sync --dev` installs the
#      pinned cindergraph; `uv run --no-sync maturin develop` builds the
#      extension.
#   2. It SKIPS (exit 0, loudly, never PASS) when `clang` is absent: every
#      replay compiles with `-fsanitize=...`, and three of the eleven finding
#      kinds are observable only with clang's sanitizers. Set
#      AXEYUM_REQUIRE_CINDERGRAPH_DEFECTS=1 to make that a failure instead --
#      any lane that publishes a claim about this example must.
#   3. It runs the sweep once, then hands the driver's stdout, its
#      `results.tsv` and the samples directory to
#      `scripts/check-cindergraph-defects.py`, which re-derives the verdict:
#      every function has an `// expect:` line and meets it, the per-verdict
#      counts equal the counts of those lines, no witness failed to replay,
#      every replayed witness replayed at ITS OWN line, the driver's wrong-line
#      control was refused, the cindergraph that ran is the commit
#      `pyproject.toml` pins, and the driver's counts agree with the table.
#
# Controls: `python3 scripts/tests/mutation_controls.py cindergraph-defects`
# deletes a sample's bounds check, breaks the lifter's usual-arithmetic rule,
# and makes `replay()` say yes to everything; each kills exactly one test of
# `scripts/tests/test_check_cindergraph_defects.py`.
#
# Prints one summary line:
#   CINDERGRAPH_DEFECTS|rows=N|replayed=N|dead=N|clean=N|bounded=N|no_oracle=N|failures=N|PASS
#
# ~15 s on the dev box (356 queries, 18 sanitizer builds).

set -uo pipefail

cd "$(dirname "$0")/.."

name=check-cindergraph-defects
PY="${AXEYUM_PY:-.venv/bin/python}"
CC="${AXEYUM_CC:-clang}"
SAMPLES=python/examples/cindergraph_defects/samples

refuse() {
  echo "$name: REFUSED -- $*" >&2
  echo "CINDERGRAPH_DEFECTS|REFUSED|$*"
  exit 2
}

# (1) The interpreter with the two modules the sweep imports. `import`, not a
# directory test: `.venv/` existing says nothing about what is in it (measured
# 2026-08-30 in scripts/check.sh's own guard).
[ -x "$PY" ] || refuse "no $PY (run: uv sync --dev)"
"$PY" -c 'import axeyum._native' >/dev/null 2>&1 \
  || refuse "axeyum._native is not importable under $PY (run: uv run --no-sync maturin develop)"
"$PY" -c 'import cindergraph' >/dev/null 2>&1 \
  || refuse "cindergraph is not importable under $PY (run: uv sync --dev; it installs the pinned commit)"

# (2) The sanitizer toolchain.
if ! command -v "$CC" >/dev/null 2>&1; then
  if [ "${AXEYUM_REQUIRE_CINDERGRAPH_DEFECTS:-}" = "1" ]; then
    echo "$name: FAIL -- AXEYUM_REQUIRE_CINDERGRAPH_DEFECTS=1 and no \`$CC\` on PATH" >&2
    echo "CINDERGRAPH_DEFECTS|FAIL|no $CC"
    exit 1
  fi
  echo "$name: SKIPPED -- no \`$CC\` on PATH; the witnesses were NOT replayed on this run." >&2
  echo "$name: install clang (apt-get install clang), or set AXEYUM_CC to a clang binary," \
       "or AXEYUM_REQUIRE_CINDERGRAPH_DEFECTS=1 to make absence a failure." >&2
  echo "CINDERGRAPH_DEFECTS|SKIPPED|reason=no $CC on PATH"
  exit 0
fi

# (3) The sweep, into real disk: /tmp on this fleet is a RAM tmpfs.
scratch_root="${TMPDIR:-/data0/axeyum/scratch/tmp}"
mkdir -p "$scratch_root" 2>/dev/null || scratch_root=/tmp
out="$(mktemp -d "$scratch_root/cindergraph-defects.XXXXXX")" || exit 2
trap 'rm -rf "$out"' EXIT

TMPDIR="$scratch_root" "$PY" python/examples/cindergraph_defects/check.py \
  --samples "$SAMPLES" --cc "$CC" --out "$out/run" > "$out/stdout" 2> "$out/stderr"
driver_status=$?

if [ ! -s "$out/stdout" ]; then
  echo "$name: the driver printed nothing (exit $driver_status):" >&2
  tail -20 "$out/stderr" >&2
  echo "CINDERGRAPH_DEFECTS|rows=0|replayed=0|dead=0|clean=0|bounded=0|no_oracle=0|failures=1|FAIL"
  exit 1
fi

# What it ran against, on the record for the log.
sed -n '1p' "$out/stdout"

python3 scripts/check-cindergraph-defects.py \
  --results "$out/run/results.tsv" \
  --stdout "$out/stdout" \
  --samples "$SAMPLES" \
  --driver-status "$driver_status"
status=$?
if [ "$status" -ne 0 ]; then
  echo "$name: the driver's own summary and refusals, for the record:" >&2
  grep -v '^| ' "$out/stderr" | tail -20 >&2
fi
exit "$status"
