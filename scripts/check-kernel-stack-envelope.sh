#!/usr/bin/env bash
# Re-derive how much stack the Lean kernel actually needs to build each prelude,
# and fail RED — with the number — when it outgrows the pinned budget.
#
# ## The failure this exists to convert
#
# The kernel's type checker is directly recursive over the term, so building a
# constructed carrier costs stack proportional to the deepest proof term in it.
# When it runs out, the process ABORTS: `fatal runtime error: stack overflow`,
# SIGABRT, exit 134. That symptom is indistinguishable from a broken tool or an
# absent declaration, and this repository has read it as both — a lane reported
# `prelude_theorem_inventory` as broken when it had only omitted `--release`,
# and `CReal.e` silently stopped the axiom-freedom guard from running at all.
#
# Nothing measured the margin. Measured 2026-08-26, the debug peak for `cpoint`
# was 1,681,616 B against a 2 MiB default stack — under 20% headroom. One deep
# declaration crosses it. This script makes that margin a number that a gate
# watches, so growth of the library produces an EXPLAINED failure.
#
# ## Why a subprocess and not a test
#
# A stack overflow aborts the whole process, so it cannot be caught, asserted
# on, or reported by the code that suffers it. It has to be observed from
# outside. `examples/kernel_stack_envelope` builds one prelude on a thread of an
# exact size and lets its exit status carry the answer; this script reads it.
#
# ## Modes
#
#   --check    (default) For each prelude: assert the build SUCCEEDS at its
#              pinned budget, then halve until it FAILS. A run that never
#              observed a failure has not shown that it can fail, so the
#              observed failure is required, not incidental.
#   --measure  Bisect over powers of two for the true minimum and print a
#              re-pinnable table. Slower; this is what produces the pin file.
#
#   --profile debug|release   Which build to probe. DEFAULT is release.
#   --prelude <name>          Only this one (repeatable).
#
# ## Why the default profile is release, when the aborts happen in debug
#
# Because a debug probe of `cpoint` takes 63 s against 8 s for release
# (measured), and a gate nobody can afford to run is not a gate. Debug frames
# cost ~3.1x release frames for the same term (measured: 1,681,616 / 538,544 =
# 3.12), so the release pin bounds the debug requirement, and the pin file
# carries a debug row for `cpoint` — the binding case — which `--profile debug`
# checks when you can pay for it.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

# Overridable so `scripts/tests/test-kernel-stack-envelope.sh` can drive this
# with deliberately wrong pins WITHOUT editing the tracked file -- mutating a
# tracked file to test a guard breaks every other lane compiling from it.
PIN_FILE="${AXEYUM_STACK_PIN_FILE:-artifacts/kernel-stack-envelope.tsv}"
MODE="check"
PROFILE="release"
SELECTED=()

while [ $# -gt 0 ]; do
  case "$1" in
    --check)   MODE="check";   shift ;;
    --measure) MODE="measure"; shift ;;
    --profile) PROFILE="${2:?--profile needs an argument}"; shift 2 ;;
    --prelude) SELECTED+=("${2:?--prelude needs an argument}"); shift 2 ;;
    -h|--help) sed -n '2,45p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

case "$PROFILE" in
  release) CARGO_PROFILE_FLAG="--release"; BIN="target/release/examples/kernel_stack_envelope" ;;
  debug)   CARGO_PROFILE_FLAG="";          BIN="target/debug/examples/kernel_stack_envelope" ;;
  *) echo "--profile must be debug or release, got '$PROFILE'" >&2; exit 2 ;;
esac

echo "== building the probe ($PROFILE) =="
# shellcheck disable=SC2086
if [ -x scripts/cargo-serialized.sh ]; then
  scripts/cargo-serialized.sh build $CARGO_PROFILE_FLAG -p axeyum-lean-kernel \
    --example kernel_stack_envelope >/dev/null
else
  cargo build $CARGO_PROFILE_FLAG -p axeyum-lean-kernel \
    --example kernel_stack_envelope >/dev/null
fi
[ -x "$BIN" ] || { echo "FAIL: probe binary $BIN was not built" >&2; exit 1; }

# One probe. 0 = that much stack was enough. 134 (or any signal) = it was not.
# Exit 2 is a USAGE error from the probe and must never be read as either, or a
# typo in this script would silently report "needs more stack" forever.
probe() {
  local prelude="$1" bytes="$2" status=0
  # The subshell matters: an overflowing probe dies on SIGABRT, and the SHELL --
  # not the probe -- prints `Aborted (core dumped)` to ITS stderr. Redirecting
  # only the probe leaves that noise on the gate's output, where it reads like
  # the gate itself crashed. `ulimit -c 0` stops each expected abort from
  # writing a core file; a bisection produces one per failing step.
  # The `bash -c` wrapper is load-bearing, not indirection for its own sake. An
  # overflowing probe dies on SIGABRT and the shell that WAITED on it prints
  # `Aborted (core dumped)` to ITS OWN stderr -- so if this script waits
  # directly, that notice lands on the gate's output and reads like the gate
  # crashed. Redirecting the probe does not help, and neither does a plain
  # subshell: bash execs a subshell whose last command is a simple command.
  # With `bash -c`, the inner shell prints the notice into the redirect and
  # exits 134 the ordinary way. `ulimit -c 0` stops each expected abort from
  # dumping core; a bisection produces one per failing step.
  AXEYUM_PRELUDE_CACHE=0 bash -c \
    'ulimit -c 0; "$0" --prelude "$1" --stack-bytes "$2"; rc=$?; exit "$rc"' \
    "$BIN" "$prelude" "$bytes" >/dev/null 2>&1 || status=$?
  if [ "$status" -eq 2 ]; then
    echo "FAIL: probe rejected its own arguments for $prelude at $bytes bytes" >&2
    echo "      (re-run without redirection to see why; this is NOT a stack result)" >&2
    exit 2
  fi
  return "$status"
}

if [ ! -f "$PIN_FILE" ]; then
  echo "FAIL: pin file $PIN_FILE is missing" >&2
  exit 1
fi

# profile<TAB>prelude<TAB>budget_bytes, '#' comments ignored.
mapfile -t PIN_ROWS < <(/usr/bin/grep -v '^[[:space:]]*#' "$PIN_FILE" | /usr/bin/grep '[^[:space:]]' || true)

wants() {
  [ "${#SELECTED[@]}" -eq 0 ] && return 0
  local p
  for p in "${SELECTED[@]}"; do [ "$p" = "$1" ] && return 0; done
  return 1
}

if [ "$MODE" = "measure" ]; then
  echo "== measuring the minimum power-of-two stack per prelude ($PROFILE) =="
  echo "# profile	prelude	min_bytes"
  mapfile -t ALL < <("$BIN" --list)
  for prelude in "${ALL[@]}"; do
    wants "$prelude" || continue
    lo=13; hi=28                       # 8 KiB .. 256 MiB
    if ! probe "$prelude" "$(( 1 << hi ))"; then
      echo "FAIL: $prelude does not build even on $(( 1 << hi )) bytes" >&2
      exit 1
    fi
    if probe "$prelude" "$(( 1 << lo ))"; then
      echo "$PROFILE	$prelude	$(( 1 << lo ))	(at floor)"
      continue
    fi
    while [ $(( hi - lo )) -gt 1 ]; do
      mid=$(( (lo + hi) / 2 ))
      if probe "$prelude" "$(( 1 << mid ))"; then hi=$mid; else lo=$mid; fi
    done
    echo "$PROFILE	$prelude	$(( 1 << hi ))"
  done
  exit 0
fi

echo "== checking each prelude against its pinned budget ($PROFILE) =="
checked=0
failures=0
for row in "${PIN_ROWS[@]}"; do
  row_profile=$(printf '%s' "$row" | cut -f1)
  prelude=$(printf '%s' "$row" | cut -f2)
  budget=$(printf '%s' "$row" | cut -f3)
  [ "$row_profile" = "$PROFILE" ] || continue
  wants "$prelude" || continue

  if ! probe "$prelude" "$budget"; then
    echo "FAIL: $prelude no longer builds on its pinned $budget-byte stack." >&2
    echo "      This is a RESOURCE limit, not a proof bug and not a broken tool:" >&2
    echo "      the kernel's type checker recursed deeper than $budget bytes of" >&2
    echo "      stack allowed and the process aborted (SIGABRT / exit 134)." >&2
    echo "      Re-derive the requirement with:" >&2
    echo "        scripts/check-kernel-stack-envelope.sh --measure --profile $PROFILE --prelude $prelude" >&2
    echo "      then raise the row in $PIN_FILE and say what grew." >&2
    failures=$(( failures + 1 ))
    continue
  fi

  # The pin passing proves nothing on its own -- a budget of 1 TiB would also
  # pass. Halve until the probe FAILS, so every green run has demonstrated that
  # this check can go red. Capped so a genuine improvement is a warning, never
  # a false red.
  observed_failure=0
  smaller=$budget
  for _ in 1 2 3; do
    smaller=$(( smaller / 2 ))
    [ "$smaller" -ge 4096 ] || break
    if ! probe "$prelude" "$smaller"; then
      observed_failure=1
      break
    fi
  done

  if [ "$observed_failure" -eq 1 ]; then
    echo "ok   $prelude: builds at $budget, aborts at $smaller (margin < 2x below pin)"
  else
    echo "WARN $prelude: builds at $budget AND at $smaller." >&2
    echo "     The pin is more than 8x the requirement, so this row is not" >&2
    echo "     measuring anything. Re-pin it with --measure." >&2
  fi
  checked=$(( checked + 1 ))
done

if [ "$checked" -eq 0 ] && [ "$failures" -eq 0 ]; then
  echo "FAIL: no pinned rows matched profile '$PROFILE'; this check ran nothing." >&2
  exit 1
fi

if [ "$failures" -gt 0 ]; then
  echo "FAIL: $failures prelude(s) outgrew their pinned stack budget." >&2
  exit 1
fi

echo "== $checked prelude(s) within budget on $PROFILE =="
