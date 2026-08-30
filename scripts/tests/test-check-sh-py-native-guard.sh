#!/usr/bin/env bash
# Controls for `scripts/check.sh`'s `py_native_installed` host guard.
#
# WHY THIS EXISTS. The guard's job is to let `scripts/check.sh` skip the two
# `autogenesis-binomial-arrow` steps on a host where the maturin-built
# `axeyum._native` extension is not installed, instead of running them and
# reporting a ModuleNotFoundError as a gate failure. A guard like that has
# exactly one interesting failure mode: saying "not installed" unconditionally,
# which makes two real steps disappear on every host and looks like a pass.
#
# The predecessor test -- `[ -d .venv ]`, still used by the py-check block --
# fails the other way. Measured 2026-08-30 in a lane worktree, `.venv/` existed
# with nothing in `site-packages` but `_virtualenv.pth`, so it answered
# "provisioned" for a venv that could not import anything.
#
# So both directions are pinned here, and the LISTING invariant with them:
# `AXEYUM_CHECK_LIST=1` must still enumerate all four binomial steps whatever
# the host looks like, because `scripts/check-aggregate-scope.sh` compares that
# listing against the justfile and a host-dependent listing makes that
# comparison non-reproducible across developers.
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CHECK="$ROOT/scripts/check.sh"
fail=0
cases=0

ok()   { cases=$((cases + 1)); echo "ok   [$1]"; }
bad()  { cases=$((cases + 1)); fail=$((fail + 1)); echo "FAIL [$1] $2"; }

# --- the guard itself, lifted from the shipped text so we test what ships ----
FN="$(sed -n '/^py_native_installed() {/,/^}/p' "$CHECK")"
if [ -z "$FN" ]; then
  echo "FAIL [guard-is-present] py_native_installed not found in scripts/check.sh"
  echo "check.sh py-native guard controls: 1 of 1 case(s) FAILED"
  exit 1
fi
ok "guard-is-present"

T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT

probe() {
  # $1 = subdir to run in; echoes the guard's exit status
  (
    cd "$T/$1" || exit 9
    eval "$FN"
    py_native_installed
    echo $?
  )
}

if ! command -v uv >/dev/null 2>&1; then
  # Without uv the guard is correctly negative everywhere and the two
  # installed/not-installed cases cannot be distinguished. Say so rather than
  # reporting a pass we did not earn.
  echo "SKIP [installed/absent] uv is not on PATH, the guard is unconditionally negative here"
else
  mkdir -p "$T/absent/.venv/lib/python3.13/site-packages"
  [ "$(probe absent)" = "1" ] \
    && ok "venv-present-package-absent-is-negative" \
    || bad "venv-present-package-absent-is-negative" "guard said installed for an empty site-packages"

  mkdir -p "$T/present/.venv/lib/python3.13/site-packages/axeyum"
  [ "$(probe present)" = "0" ] \
    && ok "package-installed-is-positive" \
    || bad "package-installed-is-positive" "guard said absent for an installed package -- it would skip two real steps on every host"

  mkdir -p "$T/novenv"
  [ "$(probe novenv)" = "1" ] \
    && ok "no-venv-is-negative" \
    || bad "no-venv-is-negative" "guard said installed with no .venv at all"
fi

# --- the listing invariant ---------------------------------------------------
listed="$(cd "$ROOT" && AXEYUM_CHECK_LIST=1 bash scripts/check.sh 2>/dev/null | grep -c 'binomial')"
if [ "$listed" = "4" ]; then
  ok "list-mode-enumerates-all-four-binomial-steps"
else
  bad "list-mode-enumerates-all-four-binomial-steps" "expected 4, got $listed -- check-aggregate-scope.sh compares this listing"
fi

optional="$(cd "$ROOT" && AXEYUM_CHECK_LIST=1 bash scripts/check.sh 2>/dev/null | grep -c '^optional:autogenesis-binomial-arrow')"
if [ "$optional" = "2" ]; then
  ok "the-two-extension-steps-are-marked-optional"
else
  bad "the-two-extension-steps-are-marked-optional" "expected 2 optional: binomial-arrow steps, got $optional -- check-fast.sh reads field 1 to defer them"
fi

# The two that do NOT import axeyum must stay unguarded: guarding them would
# make real steps unrunnable to hide a problem that is not theirs.
unguarded="$(cd "$ROOT" && AXEYUM_CHECK_LIST=1 bash scripts/check.sh 2>/dev/null | grep -c '^autogenesis-binomial-\(connective-ranking\|arrow-measurement\)')"
if [ "$unguarded" = "2" ]; then
  ok "the-two-stdlib-steps-stay-unguarded"
else
  bad "the-two-stdlib-steps-stay-unguarded" "expected 2 unprefixed, got $unguarded"
fi

echo "check.sh py-native guard controls: $cases case(s), $fail FAILED"
[ "$fail" -eq 0 ] || exit 1
