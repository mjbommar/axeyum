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
#   scripts/local-ci.sh --no-worktree      # gate the WORKING TREE (see below)
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
#   AXEYUM_LOCAL_CI_WORKTREE_ROOT  where the detached gate worktree lives
#                            (default: /data0/axeyum/local-ci, then
#                            <repo>/target/local-ci-worktree, then $TMPDIR)
#   AXEYUM_LOCAL_CI_LOCK_WAIT  seconds to wait for the gate lock (default 10800)
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 2

WITH_MOMENT=0
RECORD=0
PREFLIGHT_ONLY=0
WORKTREE=1
for a in "$@"; do case "$a" in
  --moment) WITH_MOMENT=1 ;;
  --record) RECORD=1 ;;
  --preflight-only) PREFLIGHT_ONLY=1 ;;
  --worktree) WORKTREE=1 ;;
  --no-worktree) WORKTREE=0 ;;
esac; done

# Isolated target dir: full --all-features build (incl. linked libz3) must not
# poison the agent worktrees' incremental caches.
# On /data0, not under $HOME. Measured 2026-08-19: the root filesystem was at
# **91% (81 GB free of 915 GB)** with `axeyum/target` alone at 404 GB and this
# script's own isolated dir a further 32 GB, while /data0 sat at 9% with 6.3 TB
# free. `scripts/lane-snapshot.sh --target` already puts per-lane target dirs
# under /data0/axeyum/target; this brings the heaviest single consumer that was
# still on the root disk in line with that convention. `$HOME` remains the
# fallback for a host with no /data0, so nothing breaks off this fleet.
if [ -z "${AXEYUM_LOCAL_CI_TARGET:-}" ] && [ -d /data0 ] && [ -w /data0 ]; then
  AXEYUM_LOCAL_CI_TARGET=/data0/axeyum/local-ci-target
fi
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

# WORKTREE ISOLATION. This script used to gate the WORKING TREE, and in a shared
# checkout -- which this one always is, several lanes editing at once -- that
# means another lane's uncommitted work decides whether the authoritative gate
# for `main` passes. It is not hypothetical: the FIRST run of this gate ever
# completed (2026-08-18, a6ee37c6a) had to be driven from a hand-built detached
# worktree, because `cargo fmt --all --check` and `clippy -D warnings` were
# otherwise about to be handed a sibling lane's half-finished edit to
# `crates/axeyum-solver/examples/front_door_carrier.rs`. Whatever verdict that
# produced would have been unattributable to the SHA the record names.
#
# `hooks/pre-push` already solved exactly this and this is the same solution,
# for the same reason its header gives: check the COMMIT out into a stable,
# on-disk, flock'd detached worktree and run the gate there. Never `git stash`
# (it destroys a sibling lane's WIP) and never `mktemp -d` (/tmp here is a tmpfs
# -- RAM -- and a fresh path per run rebakes every cargo fingerprint cold).
#
# A record names a SHA, so it must have measured that SHA and nothing else.
# `--no-worktree` restores the old behaviour for the one case that wants it: a
# lane pre-validating uncommitted work before it commits.
local_ci_gate_root() {
  if [ -n "${AXEYUM_LOCAL_CI_WORKTREE_ROOT:-}" ]; then
    printf '%s\n' "$AXEYUM_LOCAL_CI_WORKTREE_ROOT"; return
  fi
  local base
  for base in /data0/axeyum/local-ci "$1/target/local-ci-worktree"; do
    if mkdir -p "$base" 2>/dev/null && [ -w "$base" ]; then
      printf '%s\n' "$base"; return
    fi
  done
  printf '%s\n' "${TMPDIR:-/tmp}/axeyum-local-ci"
}

# Materialize commit $2 of the repo at $1 into a reusable detached worktree and
# print its path. `checkout --force` + `clean -xdf` make the tree byte-identical
# to the commit. `git checkout` stamps only the files it CHANGES, with the
# CURRENT time, so unchanged files keep a legitimately warm cargo cache while
# changed ones look new -- which is why this is safe where `git archive | tar -x`
# is not (tar restores COMMIT times and can leave content BEHIND a warm cache,
# letting a gate pass over code it never compiled; CLAUDE.md).
prepare_worktree() {
  local repo="$1" sha="$2" root wt
  root="$(local_ci_gate_root "$repo")" || return 1
  mkdir -p "$root" || return 1
  wt="$root/worktree"
  if ! { git -C "$wt" rev-parse --git-dir >/dev/null 2>&1 \
         && git -C "$wt" checkout --detach --force --quiet "$sha" 2>/dev/null; }; then
    rm -rf "$wt"
    git -C "$repo" worktree prune >/dev/null 2>&1
    git -C "$repo" worktree add --detach --quiet "$wt" "$sha" || return 1
  fi
  git -C "$wt" clean -xdfq || return 1
  printf '%s\n' "$wt"
}

if [ "$WORKTREE" = 1 ] && [ -z "${AXEYUM_LOCAL_CI_IN_WORKTREE:-}" ]; then
  GATE_SHA="$(git rev-parse HEAD 2>/dev/null)"
  if [ -z "$GATE_SHA" ]; then
    echo "local-ci: not a git checkout -- cannot isolate; gating this tree as-is." >&2
  else
    GATE_ROOT="$(local_ci_gate_root "$REPO_ROOT")"
    mkdir -p "$GATE_ROOT"
    # ONE root for every lane, serialized -- deliberately not per-lane, for the
    # reason hooks/pre-push gives: a per-lane root hands each lane its own COLD
    # ~15 GB cache, and this box's standing rule is one heavy cargo job at a
    # time (parallel cargo has crashed s1 AND s4). Exit 75 (EX_TEMPFAIL) rather
    # than 1 on lock timeout, so a queued gate is never read as a test failure
    # -- the same convention as scripts/cargo-serialized.sh.
    exec 9>"$GATE_ROOT/.lock"
    if command -v flock >/dev/null 2>&1; then
      flock -n 9 || echo "local-ci: another lane holds the gate lock; waiting..." >&2
      flock -w "${AXEYUM_LOCAL_CI_LOCK_WAIT:-10800}" 9 || {
        echo "local-ci: gate lock not acquired in time (exit 75 = queued, NOT a failure)" >&2
        exit 75
      }
    fi
    GATE_WT="$(prepare_worktree "$REPO_ROOT" "$GATE_SHA")" || {
      echo "local-ci: could not materialize a detached worktree for $GATE_SHA" >&2
      exit 4
    }
    GATE_DIRTY="$(git -C "$REPO_ROOT" status --porcelain 2>/dev/null | wc -l)"
    echo "== local-ci: gating COMMIT ${SHA} in ${GATE_WT} (checkout has ${GATE_DIRTY} uncommitted path(s), IGNORED) =="
    # Logs and the record belong to the real checkout, not the throwaway tree --
    # `artifacts/local-ci-runs/` is the tracked answer to "did the gate pass on
    # this SHA", so it must land where it can be committed.
    export AXEYUM_LOCAL_CI_IN_WORKTREE=1
    export AXEYUM_LOCAL_CI_LOG="$LOG_DIR"
    export AXEYUM_LOCAL_CI_RECORDS="${AXEYUM_LOCAL_CI_RECORDS:-$REPO_ROOT/artifacts/local-ci-runs}"
    # Re-exec the gate script AT THAT COMMIT: the gate that runs should be the
    # one the commit ships, not the one the dirty checkout happens to hold.
    exec "$GATE_WT/scripts/local-ci.sh" "$@" --no-worktree
  fi
fi

JOBS="$(nproc)"
echo "== local-ci ${SHA} | $(date -u +%FT%TZ) | jobs=${JOBS} | target=${CARGO_TARGET_DIR} ==" | tee "$LOG"

RECORD_DIR="${AXEYUM_LOCAL_CI_RECORDS:-$REPO_ROOT/artifacts/local-ci-runs}"
STEP_SLICE="$LOG.step"
STEPS_JSON=""

# Test counts, read out of the step's own output rather than assumed:
#   libtest  "test result: ok. 47 passed; ..."   (one line per binary, col 0)
#   nextest  "     Summary [6384.534s] 7511 tests run: 7507 passed, 4 failed, ..."
# Reported as a SUM across binaries. -1 means "this step printed no count I could
# read", which is correct for fmt/clippy/check and a FAILURE for anything that
# claims to run tests -- see `run` below.
#
# THE NEXTEST PATTERN WAS ANCHORED AT `^` AND NEXTEST INDENTS ITS SUMMARY BY
# FIVE SPACES, so it never matched, and the first real run of this gate recorded
# `tests: -1` for a step that ran 7511 tests. That is not cosmetic: -1 is the
# "no count" value, so the zero-test rule two functions down could not fire on
# the workspace test sweep -- the one step it exists for. A nextest run that
# compiled an empty suite and exited 0 would have been recorded `pass`.
#
# The control missed it because the control's fixture was TYPED FROM THE DOCS
# rather than captured from the tool, and so had no leading whitespace. The
# fixtures in scripts/tests/test-local-ci-record.sh are now verbatim lines from
# artifacts/local-ci-runs/a6ee37c6a-s4.json's own run log, including the shape
# nextest prints when the run FAILS, which differs from the passing one.
count_tests() {
  local slice="$1" n
  n=$(grep -oE '^ *Summary \[[^]]*\] +[0-9]+ tests run' "$slice" 2>/dev/null \
      | grep -oE '[0-9]+ tests run' | grep -oE '^[0-9]+' | paste -sd+ - | bc 2>/dev/null)
  if [ -z "$n" ]; then
    n=$(grep -oE '^test result: [a-zA-Z]+\. [0-9]+ passed' "$slice" 2>/dev/null \
        | grep -oE '[0-9]+ passed' | grep -oE '^[0-9]+' | paste -sd+ - | bc 2>/dev/null)
  fi
  [ -z "$n" ] && n=-1
  echo "$n"
}

# Does this step claim to run tests? Only such steps are held to the count
# rules; `cargo fmt`/`clippy`/`check` legitimately report nothing.
claims_tests() {
  case " $* " in
    *" test "*|*nextest*) return 0 ;;
    *) return 1 ;;
  esac
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
  # A step that reports a count of ZERO and exits 0 MUST have run something. An
  # empty suite that exits 0 is the failure mode this repository keeps shipping.
  # Deliberately NOT restricted to `claims_tests`: fmt/clippy/check print no
  # count at all, so they read -1 and are unaffected, and narrowing this rule to
  # a command-name match would only create a way for a renamed or wrapped test
  # step to slip past it.
  if [ "$verdict" = pass ] && [ "$tests" = 0 ]; then
    verdict=vacuous
    echo "local-ci: VACUOUS STEP — \`$*\` exited 0 having run ZERO tests" | tee -a "$LOG"
  fi
  # ...and a step that claims to run tests whose count could NOT BE READ is a
  # failure too, not a pass. Otherwise the guard above is only as durable as one
  # grep pattern matching one version of one tool's output format -- and that
  # pattern was already wrong once, silently, for the sweep that matters most.
  # `pass, tests=-1` on a test step means "it went green and we do not know
  # whether it ran anything", which is the exact statement this recorder exists
  # to make impossible.
  if [ "$verdict" = pass ] && [ "$tests" = -1 ] && claims_tests "$@"; then
    verdict=unreadable
    echo "local-ci: UNREADABLE COUNT — \`$*\` exited 0 and printed no test count this script can parse" | tee -a "$LOG"
  fi
  STEPS_JSON="${STEPS_JSON:+$STEPS_JSON,}$(printf '{"cmd":%s,"status":%s,"tests":%s,"seconds":%s,"verdict":"%s"}' \
    "$(printf '%s' "$*" | python3 -c 'import json,sys; print(json.dumps(sys.stdin.read()))')" \
    "$status" "$tests" "$((SECONDS - start))" "$verdict")"
  [ "$verdict" = vacuous ] && return 90
  [ "$verdict" = unreadable ] && return 89
  return "$status"
}

rc=0
# ---------------------------------------------------------------------------
# L0 trusted-library safety gates (ADR-1050), FIRST of all — cheaper than the
# preflight's own toolchain checks, and this file is what ci.yml, hooks/
# pre-push and CLAUDE.md all call "the authoritative gate for main". Until now
# these seven ran ONLY from `scripts/check.sh` and the `justfile` — that is,
# only when a human typed a command; `check-l0-gate-enforcement.py` measured
# ZERO references to any of them here, against positive controls of 10
# `scripts/` references in this same file. Nothing stopped a change that
# breaks statement identity, admits a circular trust closure, contaminates the
# blind-evaluation partition or silently drops a semantic control from
# reaching `main` through this route.
#
# Ordered cheapest-first (measured warm on s4, single run) so a fast violation
# is reported without paying for the slow ones: holdout-closed-evaluation
# 0.06s, settled-fact-statements 0.09s, semantic-control-fixtures 1.09s,
# credit-transaction-ledger 10.6s, kernel-differential 7-27s (hard-requires
# the pinned Lean toolchain — the script sets AXEYUM_REQUIRE_LEAN=1 itself, so
# a host without it FAILS this step rather than skipping it), trust-closure
# ~58s (shells out to `cargo run --release`), proposition-duplication 55-72s
# despite being pure Python.
#
# No `|| true`, no skip switch: these feed `rc` exactly like every other step
# below, so a failure here fails the whole gate.
run python3 scripts/check-holdout-closed-evaluation.py || rc=$?
run python3 scripts/check-settled-fact-statements.py || rc=$?
run python3 scripts/check-semantic-control-fixtures.py --check || rc=$?
run python3 scripts/check-credit-transaction-ledger.py || rc=$?
run python3 scripts/check-kernel-differential.py || rc=$?
run python3 scripts/check-trust-closure.py --quiet || rc=$?
run python3 scripts/check-proposition-duplication.py || rc=$?
# A GENERATED ARTIFACT WITH NO AUTOMATIC RE-DERIVATION DRIFTS SILENTLY.
# `artifacts/import-backlog.json` went stale at 147 rows while the fact ledger
# moved to 164, and nobody noticed, because `gen-import-backlog.py --check` was
# registered ONLY in `check.sh` and the `justfile` -- absent from ci.yml, from
# hooks/pre-push, and from this file, the one CI itself calls the authoritative
# gate for main. Pure Python, sub-second; there is no cost argument for leaving
# it out.
run python3 scripts/gen-import-backlog.py --check || rc=$?
# Assert the seven above stay wired -- in ci.yml, hooks/pre-push AND this
# script. The reason the block above exists at all: prose did not keep them
# wired, so a gate does.
run python3 scripts/check-l0-gate-enforcement.py || rc=$?
# ---------------------------------------------------------------------------

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

# THE CAPABILITY FRONTIER RATCHET, SERIALIZED. It moved here from
# `hooks/pre-push` on 2026-08-19, and moving it makes it stronger rather than
# weaker -- which is the only reason it was allowed to move.
#
# It measures "the largest N decided within a fixed WALL-CLOCK budget", so it is
# the one gate contention actively corrupts. Each family calibrates the machine
# before and after its sweep and marks a run NOT COMPARABLE (ratchet not
# enforced) or ADVISORY ONLY (do not raise a baseline from it) when the frame
# moved. In the pre-push hook, with eight lanes on the box, it cost **200 s of
# the 545 s baseline** and spent most of that being advisory -- paying full price
# for a verdict it then declined to enforce. The nextest sweep above would do the
# same thing, since `profile.local` is `default-filter = 'all()'` and runs it in
# parallel with everything else.
#
# So it runs HERE, after that sweep, with `--test-threads=1`, which is what
# `just frontier` does and what makes the numbers comparable. Read the
# `reference frame [family]: ...` line before believing a REGRESSION or
# committing a PROGRESS.
#
# It exists because a 17-point `nia_unsat` regression once shipped and needed an
# 829-commit bisect: it is the only gate that notices we got WEAKER without
# getting WRONG.
run cargo test -p axeyum-solver --test progress_frontier --features full \
    -- --test-threads=1 || rc=$?

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
