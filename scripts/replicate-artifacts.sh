#!/usr/bin/env bash
# End-to-end replication of the STANDALONE ARTIFACT REPOSITORY from clean
# clones. Companion to replicate.sh, which replicates the solver.
#
# Usage: replicate-artifacts.sh [tier] [axeyum-branch]
#
# Clones axeyum-rado-artifacts AND axeyum fresh into a scratch directory and
# runs the artifact repo's own verify.sh against them. This is the check a
# referee performs: nothing pre-existing, nothing on PATH from prior work.
set -u

TIER="${1:-standard}"
BRANCH="${2:-session/rado-claim-ledger-2026-08-12}"
HOST="$(hostname -s)"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
RUN="${REPL_ROOT:-$HOME/replication}/artifacts-$TIER-$STAMP"
mkdir -p "$RUN"
exec > >(tee -a "$RUN/console.log") 2>&1

echo "=== artifact replication tier=$TIER host=$HOST stamp=$STAMP ==="
echo "  cores=$(nproc)  mem=$(free -g | awk '/^Mem:/{print $2}')GiB"
[ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env"
export PATH="$HOME/.cargo/bin:$PATH"
command -v cargo >/dev/null || { echo "FATAL: no cargo"; exit 1; }
echo "  cargo:  $(cargo --version)"
echo "  python: $(python3 --version)"

# Keep every build artifact out of both clones, so "dirty checkout" stays
# meaningful and verify.sh's own cleanliness assertion is not defeated by us.
export CARGO_TARGET_DIR="$RUN/cargo-target"

echo; echo "=== clone artifact repo ==="
git clone --quiet https://github.com/mjbommar/axeyum-rado-artifacts.git "$RUN/artifacts" || {
  echo "FATAL: artifact clone failed"; exit 1; }
echo "  commit: $(git -C "$RUN/artifacts" rev-parse HEAD)"

echo; echo "=== clone axeyum ($BRANCH) ==="
if [ -n "${REPL_SEED:-}" ] && [ -f "$REPL_SEED" ]; then
  mkdir -p "$RUN/axeyum" && tar xzf "$REPL_SEED" -C "$RUN/axeyum" --strip-components=1
else
  git clone --quiet --branch "$BRANCH" https://github.com/mjbommar/axeyum.git "$RUN/axeyum" || {
    echo "FATAL: axeyum clone failed"; exit 1; }
fi
echo "  commit: $(git -C "$RUN/axeyum" rev-parse HEAD)"
echo "  dirty:  $(git -C "$RUN/axeyum" status --porcelain | wc -l) files (expect 0)"

echo; echo "=== verify.sh --tier $TIER ==="
t0=$(date +%s)
bash "$RUN/artifacts/verify.sh" --axeyum "$RUN/axeyum" --tier "$TIER"
RC=$?
echo
echo "=== verify.sh exit=$RC wall=$(( $(date +%s) - t0 ))s ==="
echo "  artifacts dirty after run: $(git -C "$RUN/artifacts" status --porcelain | wc -l)"
echo "  axeyum    dirty after run: $(git -C "$RUN/axeyum" status --porcelain | wc -l)"
exit $RC
