#!/usr/bin/env bash
# local-ci.sh — the heavy test gate, run on local hardware.
#
# Why local: the full-workspace suite (esp. the ~32 z3/cvc5 differential-fuzz
# binaries, 60s+ each) needs real cores. On GitHub's 4-core hosted runners it
# forced serialization + sharding + a 60-min timeout that still went red. On a
# multi-core box the whole problem evaporates: everything runs fully parallel,
# nothing starves, full coverage finishes in minutes. GitHub Actions now runs
# only the light checks (fmt/clippy/build/docs); this script is the real gate.
#
# Usage:
#   scripts/local-ci.sh            # test the current checkout (HEAD)
#   scripts/local-ci.sh --moment   # also run the #[ignore]d order-255 proofs
#   scripts/local-ci.sh --record   # ...and leave a COMMITTABLE run record
#   scripts/local-ci.sh --preflight-only   # can THIS host run the gate at all?
#
# WHY --record EXISTS. Hosted CI's own comment calls this script "the
# authoritative gate for main". Measured 2026-08-18, four independent ways, it
# has never run on this box: `artifacts/local-ci/` absent, the isolated target
# dir `~/.cache/axeyum-local-ci-target` absent, no crontab entry and no user
# systemd timer, and only four tracked files mention the script -- none of them
# an entry point (CLAUDE.md's Commands section does not name it). Worse, the log
# dir is GITIGNORED, so a passing run leaves no trace anyone else can see: the
# question "did the authoritative gate pass on this SHA?" was unanswerable by
# construction, not by accident. `--record` writes one small JSON per (sha,
# host) to `artifacts/local-ci-runs/`, which is tracked.
#
# The record carries TEST COUNTS per step, and a step that was supposed to run
# tests and ran ZERO is recorded as a failure however cleanly cargo exited. That
# is this repository's most-repeated defect -- a corpus gate exited 0 for 15 days
# while compiling an empty binary, and the documented form of the capability
# ratchet printed "running 0 tests ... ok" -- so a record that could not express
# it would be another green light meaning nothing.
#
# Env:
#   AXEYUM_LOCAL_CI_TARGET   cargo target dir (default: ~/.cache/axeyum-local-ci-target)
#                            kept separate so it never clobbers agent worktrees.
#   AXEYUM_LOCAL_CI_LOG      log dir (default: <repo>/artifacts/local-ci)
#   AXEYUM_LOCAL_CI_RECORDS  record dir (default: <repo>/artifacts/local-ci-runs)
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 2

WITH_MOMENT=0
RECORD=0
PREFLIGHT_ONLY=0
for a in "$@"; do case "$a" in
  --moment) WITH_MOMENT=1 ;;
  --record) RECORD=1 ;;
  --preflight-only) PREFLIGHT_ONLY=1 ;;
esac; done

# Isolated target dir: full --all-features build (incl. linked libz3) must not
# poison the agent worktrees' incremental caches.
export CARGO_TARGET_DIR="${AXEYUM_LOCAL_CI_TARGET:-$HOME/.cache/axeyum-local-ci-target}"
# Tests don't need debuginfo; saves disk + link time.
export CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0

SHA="$(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
LOG_DIR="${AXEYUM_LOCAL_CI_LOG:-$REPO_ROOT/artifacts/local-ci}"
mkdir -p "$LOG_DIR"
LOG="$LOG_DIR/${SHA}.log"

# PREFLIGHT. Every prerequisite this script uses, checked before anything runs.
#
# The z3 check below was the only one, and z3 was the only prerequisite this box
# had. Measured 2026-08-18 on the dev host: `rustup run 1.88.0 cargo --version`
# exits 1 ("toolchain not installed") and `cargo nextest --version` exits 101
# ("no such command") -- and `cargo nextest run --profile local --workspace
# --all-features` IS the test sweep. Each step is `run ... || rc=$?`, so the
# script would have carried on with the two central steps never executing and
# reported a specific nonzero rc that nobody was reading, because nobody was
# running it. `scripts/provision-fleet-host.sh` installs none of the three.
#
# So: refuse to start rather than produce a degraded run. A gate that limps is
# worse than one that stops, because its output still looks like a gate's.
missing=""
have() { command -v "$1" >/dev/null 2>&1; }
have z3 || missing="$missing
  z3 (and libz3-dev)      sudo apt-get install -y z3 libz3-dev
      --all-features links libz3 and the differential fuzzes exec /usr/bin/z3."
cargo nextest --version >/dev/null 2>&1 || missing="$missing
  cargo-nextest           cargo install cargo-nextest --locked
      the workspace test sweep is \`cargo nextest run --profile local\`; without
      it the ONLY steps that run tests are the doctests."
rustup run stable cargo --version >/dev/null 2>&1 || missing="$missing
  rust stable             rustup toolchain install stable --component clippy
      clippy is pinned to stable on purpose -- nightly does not flag some stable
      lints, so a nightly-clean change can still red hosted CI."
rustup run 1.88.0 cargo --version >/dev/null 2>&1 || missing="$missing
  rust 1.88.0 (MSRV)      rustup toolchain install 1.88.0
      the frontier builds on nightly, which accepts syntax stable 1.88 rejects."
if [ -n "$missing" ]; then
  {
    echo "ERROR: local-ci is the authoritative gate for main and this host cannot run it."
    echo "Missing:$missing"
    echo
    echo "Install the above, or run this on a host that has them. Do NOT read a"
    echo "nonzero exit from a degraded run as a test failure -- it is neither a"
    echo "pass nor a fail, it is an absence of coverage."
  } | tee "$LOG"
  exit 3
fi
if [ "$PREFLIGHT_ONLY" = 1 ]; then
  echo "LOCAL_CI_PREFLIGHT|host=$(uname -n)|verdict=runnable"
  exit 0
fi

JOBS="$(nproc)"
echo "== local-ci ${SHA} | $(date -u +%FT%TZ) | jobs=${JOBS} | target=${CARGO_TARGET_DIR} ==" | tee "$LOG"

RECORD_DIR="${AXEYUM_LOCAL_CI_RECORDS:-$REPO_ROOT/artifacts/local-ci-runs}"
STEP_SLICE="$LOG.step"
STEPS_JSON=""

# Test counts, read out of the step's own output rather than assumed:
#   libtest  "test result: ok. 47 passed; ..."   (one line per binary)
#   nextest  "Summary [   12.3s] 968 tests run: 968 passed, ..."
# Reported as a SUM across binaries. -1 means "this step reports no count",
# which is correct for fmt/clippy/check and is why the zero-test rule below
# only applies to steps that claim to run tests.
count_tests() {
  local slice="$1" n
  n=$(grep -oE '^Summary \[[^]]*\] +[0-9]+ tests run' "$slice" 2>/dev/null \
      | grep -oE '[0-9]+ tests run' | grep -oE '^[0-9]+' | paste -sd+ - | bc 2>/dev/null)
  if [ -z "$n" ]; then
    n=$(grep -oE '^test result: [a-zA-Z]+\. [0-9]+ passed' "$slice" 2>/dev/null \
        | grep -oE '[0-9]+ passed' | grep -oE '^[0-9]+' | paste -sd+ - | bc 2>/dev/null)
  fi
  [ -z "$n" ] && n=-1
  echo "$n"
}

run() {
  local start=$SECONDS status tests verdict
  echo "+ $*" | tee -a "$LOG"
  # TRUNCATE the slice first. `tee -a a b` appends to BOTH, so without this the
  # slice accumulates every earlier step and each step inherits the previous
  # step's count -- which is not a cosmetic bug: it makes the zero-test rule
  # below unable to fire, because a vacuous step reads the last real step's
  # total. Caught by a harness, not by reading the code: 5, 5, 9, 9 where the
  # answer was 5, 0, 9, -1.
  : > "$STEP_SLICE"
  "$@" 2>&1 | tee -a "$LOG" "$STEP_SLICE"
  status="${PIPESTATUS[0]}"
  tests="$(count_tests "$STEP_SLICE")"
  verdict=pass
  [ "$status" != 0 ] && verdict=fail
  # A step whose command names `test` or `nextest` MUST have run something. An
  # empty suite that exits 0 is the failure mode this repository keeps shipping.
  if [ "$verdict" = pass ] && [ "$tests" = 0 ]; then
    verdict=vacuous
    echo "local-ci: VACUOUS STEP — \`$*\` exited 0 having run ZERO tests" | tee -a "$LOG"
  fi
  STEPS_JSON="${STEPS_JSON:+$STEPS_JSON,}$(printf '{"cmd":%s,"status":%s,"tests":%s,"seconds":%s,"verdict":"%s"}' \
    "$(printf '%s' "$*" | python3 -c 'import json,sys; print(json.dumps(sys.stdin.read()))')" \
    "$status" "$tests" "$((SECONDS - start))" "$verdict")"
  [ "$verdict" = vacuous ] && return 90
  return "$status"
}

rc=0
# Lint + format gates FIRST — these mirror the hosted-CI light checks. Clippy is
# pinned to STABLE on purpose: the frontier is developed against nightly clippy,
# which does not flag some stable lints (e.g. needless_raw_string_hashes), so a
# lint-clean-on-nightly change can still red hosted CI. Running stable here makes
# the pre-merge gate match hosted CI exactly, closing that gap.
run cargo fmt --all --check || rc=$?
run rustup run stable cargo clippy --workspace --all-targets --all-features -- -D warnings || rc=$?
# MSRV build (default features) — the frontier's nightly toolchain accepts unstable
# syntax (e.g. `if let` guards) that stable 1.88 rejects, so a change can pass the
# stable clippy/test path above and still red the hosted MSRV job. Mirror it here.
run rustup run 1.88.0 cargo check --workspace || rc=$?
# Full parallel, full features, host-sensitive decide tests re-included (they
# only failed on slow hosted runners) — the `local` nextest profile does that.
run cargo nextest run --profile local --workspace --all-features --no-fail-fast || rc=$?
# nextest does not run doctests.
run cargo test --workspace --all-features --doc || rc=$?

if [ "$WITH_MOMENT" = 1 ]; then
  # The order-255 certified-moment proofs (~15 min each) are #[ignore]d.
  run cargo test -p axeyum-cas --lib -- --ignored || rc=$?
fi

VERDICT=$([ $rc -eq 0 ] && echo PASS || echo FAIL)
echo "== local-ci ${SHA}: $([ $rc -eq 0 ] && echo PASS || echo "FAIL(rc=$rc)") | log: $LOG ==" | tee -a "$LOG"

if [ "$RECORD" = 1 ]; then
  mkdir -p "$RECORD_DIR"
  REC="$RECORD_DIR/${SHA}-$(uname -n).json"
  printf '{\n  "sha": "%s",\n  "host": "%s",\n  "finished_utc": "%s",\n  "moment": %s,\n  "verdict": "%s",\n  "rc": %s,\n  "steps": [%s]\n}\n' \
    "$SHA" "$(uname -n)" "$(date -u +%FT%TZ)" "$WITH_MOMENT" "$VERDICT" "$rc" "$STEPS_JSON" > "$REC"
  python3 -c 'import json,sys; json.load(open(sys.argv[1]))' "$REC" \
    || { echo "local-ci: record is not valid JSON: $REC" >&2; exit 91; }
  echo "== local-ci record: $REC =="
fi
rm -f "$STEP_SLICE"
exit "$rc"
