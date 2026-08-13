#!/usr/bin/env bash
# End-to-end replication from a CLEAN CHECKOUT.
#
# Usage: replicate.sh <role> <branch>
#
# Clones axeyum fresh into a scratch dir, builds it, and runs one role's
# replication steps. Records every step's exit code and does NOT fail fast --
# the point is a complete picture, not the first failure.
#
# Roles:
#   gate     full aggregate gate (heaviest)
#   cover226 regenerate + recertify the R_4(2(x-y)=3z)=226 upper bound
#   cover313 regenerate + recertify the R_4(4(x-y)=3z)=313 upper bound
#   ladder   small monolithic refutations + forward/backward checker agreement
#   ledger   claim validation, negative fixtures, witness replay, encoder parity
set -u

ROLE="${1:?role required}"
BRANCH="${2:-session/rado-claim-ledger-2026-08-12}"
HOST="$(hostname -s)"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
ROOT="${REPL_ROOT:-$HOME/replication}"
RUN="$ROOT/$ROLE-$STAMP"
SRC="$RUN/axeyum"
REPORT="$RUN/REPORT.md"

mkdir -p "$RUN"
exec > >(tee -a "$RUN/console.log") 2>&1

say() { printf '\n=== %s ===\n' "$*"; }
STEPS_OK=0; STEPS_FAIL=0
declare -a RESULTS

step() { # step <name> <timeout-seconds> <command...>
  local name="$1"; shift
  local t="$1"; shift
  local t0 rc out
  say "$name"
  t0=$(date +%s)
  out="$RUN/$(echo "$name" | tr ' /' '__').log"
  timeout "$t" "$@" > "$out" 2>&1
  rc=$?
  local dt=$(( $(date +%s) - t0 ))
  if [ $rc -eq 0 ]; then STEPS_OK=$((STEPS_OK+1)); else STEPS_FAIL=$((STEPS_FAIL+1)); fi
  RESULTS+=("$name|$rc|$dt|$(basename "$out")")
  printf '  rc=%s  %ss  -> %s\n' "$rc" "$dt" "$(basename "$out")"
  tail -3 "$out" | sed 's/^/    /'
  return 0
}

say "replication role=$ROLE host=$HOST branch=$BRANCH stamp=$STAMP"
echo "  cores=$(nproc)  mem=$(free -g | awk '/^Mem:/{print $2}')GiB  load=$(cut -d' ' -f1 /proc/loadavg)"

# ---- toolchain -------------------------------------------------------------
# A non-login ssh shell does not source the cargo env; without this every
# cargo step exits 127 (command not found), which is what happened on the
# first attempt.
[ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env"
export PATH="$HOME/.cargo/bin:$PATH"
if ! command -v cargo >/dev/null; then
  echo "FATAL: cargo not on PATH even after sourcing ~/.cargo/env"; exit 1
fi
echo "  cargo:  $(command -v cargo) $(cargo --version 2>&1 | head -1)"
echo "  python: $(command -v python3) $(python3 --version 2>&1)"

# ---- clean checkout --------------------------------------------------------
# GitHub connectivity has been flaky on some hosts; retry rather than lose the
# whole run to one timeout.
clone_with_retry() {
  local i
  # Hosts without outbound GitHub access can be pre-seeded with a pristine
  # clone (REPL_SEED=/path/to/axeyum-pristine.tar.gz). Still a clean checkout,
  # just transported rather than fetched.
  if [ -n "${REPL_SEED:-}" ] && [ -f "$REPL_SEED" ]; then
    mkdir -p "$SRC" && tar xzf "$REPL_SEED" -C "$SRC" --strip-components=1 && return 0
    return 1
  fi
  for i in 1 2 3 4 5; do
    rm -rf "$SRC"
    if git clone --quiet --branch "$BRANCH" \
         https://github.com/mjbommar/axeyum.git "$SRC"; then return 0; fi
    echo "  clone attempt $i failed; retrying in 60 s"
    sleep 60
  done
  return 1
}
export SRC BRANCH
export -f clone_with_retry
step "clone-axeyum" 3600 bash -c clone_with_retry
cd "$SRC" 2>/dev/null || { echo "FATAL: clone failed after retries"; exit 1; }
COMMIT="$(git rev-parse HEAD)"
echo "  commit: $COMMIT"
echo "  dirty:  $(git status --porcelain | wc -l) files (expect 0)"

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-$(( $(nproc) / 2 ))}"
export CARGO_TERM_COLOR=never

step "build-release" 3600 cargo build --release --workspace --features full

case "$ROLE" in

  gate)
    step "aggregate-gate" 21600 bash scripts/check.sh
    ;;

  ledger)
    step "validate-claims"        900 python3 scripts/validate-claims.py
    step "negative-fixtures"      900 python3 scripts/check-claim-negative-fixtures.py
    step "claim-certificates"    3600 python3 scripts/check-claim-certificates.py
    step "encoder-parity"        1800 cargo test -p axeyum-cnf --release --test colouring_encoding_parity
    step "cnf-lib"               1800 cargo test -p axeyum-cnf --release --lib
    ;;

  ladder)
    step "lean-kernel-lib"       1800 cargo test -p axeyum-lean-kernel --release --lib
    step "lean-rado-arith"        900 cargo test -p axeyum-lean-kernel --release --test rado_shell_arithmetic
    step "solver-lib-full"       5400 cargo test -p axeyum-solver --release --lib --features full
    step "cas-bridge-routes"      900 cargo test -p axeyum-solver --release --features full --test cas_bridge_routes
    step "corpus-regression"     3600 cargo test -p axeyum-solver --release --features full --test corpus_regression
    ;;

  cover226|cover313)
    if [ "$ROLE" = cover226 ]; then A=2; B=3; N=226; CLAIM=rado-r4-a2-b3
    else A=4; B=3; N=313; CLAIM=rado-r4-a4-b3; fi
    STORED="artifacts/claims/rado/$CLAIM/F_$N.cnf"

    # Measured 2026-08-13 on s5 (27 GiB): recertify_rado was OOM-killed at
    # 27,742,576 kB anon-rss after 1331 s, exiting 137. That is a resource
    # failure, NOT a failed recertification, and the bare 137 reads exactly
    # like a real one in the report. Say so up front instead.
    MEM_GIB="$(free -g | awk '/^Mem:/{print $2}')"
    if [ "${MEM_GIB:-0}" -lt 48 ]; then
      echo "  WARNING: ${MEM_GIB} GiB RAM. recertify_rado peaked at ~27 GiB on"
      echo "           n=313 and was OOM-killed on a 27 GiB host. Expect exit"
      echo "           137 here; that is memory, not a refuted claim. Re-run"
      echo "           this role on a host with >= 48 GiB before concluding"
      echo "           anything about the bound."
    fi

    # 1. regenerate the instance and require BYTE-IDENTITY with the committed
    #    artifact. This is the load-bearing check of the regeneration model:
    #    if the formula does not reproduce, nothing downstream means anything.
    step "gen-instance" 900 python3 scripts/gen-rado-instance.py "$A" "$B" 4 "$N" "$RUN/F_$N.cnf"
    if [ -f "$STORED" ]; then
      step "byte-identity-vs-committed" 300 cmp -s "$RUN/F_$N.cnf" "$STORED"
      echo "  regenerated sha256: $(sha256sum "$RUN/F_$N.cnf" | cut -d' ' -f1)"
      echo "  committed    sha256: $(sha256sum "$STORED" | cut -d' ' -f1)"
    else
      echo "  NOTE: no committed CNF at $STORED — byte-identity not checkable"
      RESULTS+=("byte-identity-vs-committed|SKIP|0|-")
    fi

    # 2. re-refute and re-check the cover from the regenerated formula.
    #    Exit codes (from the example's own docs): 0 success, 10 SAT (which
    #    would REFUTE the published claim), 2 usage.
    step "recertify-cover" 43200 cargo run --release -p axeyum-search \
        --example recertify_rado -- "$A" "$B" 4 "$N" "$RUN/F_$N.cnf" "$RUN/F_$N.drat" 10
    RC=$(printf '%s\n' "${RESULTS[@]}" | grep '^recertify-cover|' | cut -d'|' -f2)
    if [ "$RC" = "10" ]; then
      echo "  *** ALARM: recertify returned SAT (10). This REFUTES the claim R_4 = $N. ***"
    elif [ "$RC" = "137" ]; then
      echo "  NOTE: exit 137 is SIGKILL, almost always the OOM killer on this"
      echo "        workload. Confirm with: dmesg -T | grep -i 'killed process'."
      echo "        An OOM kill says nothing about the claim -- do not record"
      echo "        it as a failed recertification."
    fi
    ;;

  *) echo "FATAL: unknown role $ROLE"; exit 1 ;;
esac

# ---- report ----------------------------------------------------------------
{
  echo "# Replication report — $ROLE @ $HOST"
  echo
  echo "- UTC: $STAMP"
  echo "- host: $HOST ($(nproc) cores, $(free -g | awk '/^Mem:/{print $2}') GiB)"
  echo "- branch: \`$BRANCH\`"
  echo "- commit: \`$COMMIT\`"
  echo "- clean checkout: yes (fresh clone)"
  echo
  echo "| step | exit | seconds | log |"
  echo "|---|---|---|---|"
  for r in "${RESULTS[@]}"; do IFS='|' read -r n rc dt lg <<< "$r"; echo "| $n | $rc | $dt | \`$lg\` |"; done
  echo
  echo "**$STEPS_OK passed, $STEPS_FAIL failed.**"
  echo
  echo "Exit codes are recorded verbatim. A nonzero code is a real failure, not"
  echo "a formatting artifact; read the named log before drawing a conclusion."
} > "$REPORT"

say "DONE role=$ROLE ok=$STEPS_OK fail=$STEPS_FAIL"
cat "$REPORT"
exit 0
