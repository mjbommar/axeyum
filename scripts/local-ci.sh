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
#
# Env:
#   AXEYUM_LOCAL_CI_TARGET   cargo target dir (default: ~/.cache/axeyum-local-ci-target)
#                            kept separate so it never clobbers agent worktrees.
#   AXEYUM_LOCAL_CI_LOG      log dir (default: <repo>/artifacts/local-ci)
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 2

WITH_MOMENT=0
for a in "$@"; do case "$a" in --moment) WITH_MOMENT=1 ;; esac; done

# Isolated target dir: full --all-features build (incl. linked libz3) must not
# poison the agent worktrees' incremental caches.
export CARGO_TARGET_DIR="${AXEYUM_LOCAL_CI_TARGET:-$HOME/.cache/axeyum-local-ci-target}"
# Tests don't need debuginfo; saves disk + link time.
export CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0

SHA="$(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
LOG_DIR="${AXEYUM_LOCAL_CI_LOG:-$REPO_ROOT/artifacts/local-ci}"
mkdir -p "$LOG_DIR"
LOG="$LOG_DIR/${SHA}.log"

# The z3 feature links libz3 and the fuzzes exec /usr/bin/z3. Without a system
# z3 those tests can't run; fail loudly rather than silently skip coverage.
if ! command -v z3 >/dev/null 2>&1; then
  echo "ERROR: z3 not on PATH. Install it (sudo apt-get install -y z3 libz3-dev)"\
       "so --all-features links and the differential fuzzes can run." | tee "$LOG"
  exit 3
fi

JOBS="$(nproc)"
echo "== local-ci ${SHA} | $(date -u +%FT%TZ) | jobs=${JOBS} | target=${CARGO_TARGET_DIR} ==" | tee "$LOG"

run() { echo "+ $*" | tee -a "$LOG"; "$@" 2>&1 | tee -a "$LOG"; return "${PIPESTATUS[0]}"; }

rc=0
# Full parallel, full features, host-sensitive decide tests re-included (they
# only failed on slow hosted runners) — the `local` nextest profile does that.
run cargo nextest run --profile local --workspace --all-features || rc=$?
# nextest does not run doctests.
run cargo test --workspace --all-features --doc || rc=$?

if [ "$WITH_MOMENT" = 1 ]; then
  # The order-255 certified-moment proofs (~15 min each) are #[ignore]d.
  run cargo test -p axeyum-cas --lib -- --ignored || rc=$?
fi

echo "== local-ci ${SHA}: $([ $rc -eq 0 ] && echo PASS || echo "FAIL(rc=$rc)") | log: $LOG ==" | tee -a "$LOG"
exit "$rc"
