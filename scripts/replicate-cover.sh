#!/usr/bin/env bash
# Independently RE-RUN one headline cube cover from a clean clone and compare
# it cell-by-cell against the committed ledger.
#
# Usage: replicate-cover.sh <226|313> [axeyum-branch]
#
# This is the strongest single check of an upper bound that does not need a
# large-memory host: it re-refutes all 4096 cells from (a,b,k,n) with axeyum's
# own proof-producing core, re-checks every per-cell proof, and requires the
# result to agree with the ledger on colours, verdict, step count and check.
# Unlike the monolithic route it is memory-light, so it runs on ordinary boxes.
set -u
N="${1:?226 or 313}"
BRANCH="${2:-main}"
HOST="$(hostname -s)"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
RUN="${REPL_ROOT:-$HOME/replication}/cover-rerun-$N-$STAMP"
mkdir -p "$RUN"
exec > >(tee -a "$RUN/console.log") 2>&1

echo "=== cover re-run n=$N host=$HOST stamp=$STAMP ==="
echo "  cores=$(nproc)  mem=$(free -g | awk '/^Mem:/{print $2}')GiB"
[ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env"
export PATH="$HOME/.cargo/bin:$PATH"
command -v cargo >/dev/null || { echo "FATAL: no cargo"; exit 1; }
echo "  cargo: $(cargo --version)"
# Keep build output out of both clones so their cleanliness stays meaningful.
export CARGO_TARGET_DIR="$RUN/cargo-target"

if [ -n "${REPL_SEED_ARTIFACTS:-}" ] && [ -f "$REPL_SEED_ARTIFACTS" ]; then
  mkdir -p "$RUN/artifacts" && tar xzf "$REPL_SEED_ARTIFACTS" -C "$RUN/artifacts" --strip-components=1
else
  git clone --quiet https://github.com/mjbommar/axeyum-rado-artifacts.git "$RUN/artifacts" || {
    echo "FATAL: artifact clone failed"; exit 1; }
fi
if [ -n "${REPL_SEED:-}" ] && [ -f "$REPL_SEED" ]; then
  mkdir -p "$RUN/axeyum" && tar xzf "$REPL_SEED" -C "$RUN/axeyum" --strip-components=1
else
  git clone --quiet --branch "$BRANCH" https://github.com/mjbommar/axeyum.git "$RUN/axeyum" || {
    echo "FATAL: axeyum clone failed"; exit 1; }
fi
echo "  artifacts: $(git -C "$RUN/artifacts" rev-parse --short HEAD 2>/dev/null || echo seeded)"
echo "  axeyum:    $(git -C "$RUN/axeyum" rev-parse --short HEAD 2>/dev/null || echo seeded)"
echo "  axeyum dirty: $(git -C "$RUN/axeyum" status --porcelain 2>/dev/null | wc -l) (expect 0)"

t0=$(date +%s)
bash "$RUN/artifacts/verify.sh" --axeyum "$RUN/axeyum" --cover "$N" --jobs "$(nproc)"
RC=$?
echo
echo "=== cover re-run n=$N exit=$RC wall=$(( $(date +%s) - t0 ))s ==="
echo "  artifacts dirty after: $(git -C "$RUN/artifacts" status --porcelain 2>/dev/null | wc -l)"
echo "  axeyum    dirty after: $(git -C "$RUN/axeyum" status --porcelain 2>/dev/null | wc -l)"
exit $RC
