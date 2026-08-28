#!/usr/bin/env bash
# Provision the Lean side of the autogenesis import route on THIS host.
#
# Why this exists: the `nat.modeq` widening needed an axiom-free Lean contract
# compiled through `lean4export`, and the lane after it spent a third of its
# budget discovering that neither `lean4export` nor a Mathlib checkout exists
# here -- `command -v lean` says nothing about either, and
# `docs/contributor-guide/fleet-hosts.md` records Mathlib as an s5-only
# resource.  Measured 2026-08-28 on s4, all three pieces provision cleanly in
# about five minutes, so a lane should never size that work as impossible again.
#
# Everything is pinned to the commits the operation manifests already name, and
# the script REFUSES rather than proceeding on a mismatch: a silently different
# Mathlib produces exports that no manifest can reproduce.
#
#   scripts/provision-lean-import-toolchain.sh            # provision + verify
#   scripts/provision-lean-import-toolchain.sh --verify   # verify only, no network
#
# On success it prints the three paths a lane needs, as `KEY=VALUE` lines.
set -u

MATHLIB_COMMIT=c5ea00351c28e24afc9f0f84379aa41082b1188f
LEAN4EXPORT_COMMIT=a3e35a584f59b390667db7269cd37fca8575e4bf
LEAN_TOOLCHAIN=leanprover--lean4---v4.30.0
LEAN_GITHASH=d024af099ca4bf2c86f649261ebf59565dc8c622

ROOT="${AXEYUM_LEAN_ROOT:-/data0/axeyum/lean-import-toolchain}"
ELAN="${ELAN_HOME:-$HOME/.elan}"
LAKE="$ELAN/toolchains/$LEAN_TOOLCHAIN/bin/lake"
LEAN="$ELAN/toolchains/$LEAN_TOOLCHAIN/bin/lean"

verify_only=0
[ "${1:-}" = "--verify" ] && verify_only=1

fail() { echo "LEAN_IMPORT_TOOLCHAIN|verdict=FAIL|reason=$1" >&2; exit 1; }

# --- 1. the pinned Lean toolchain ------------------------------------------
# `command -v lean` is empty on a host that HAS Lean: elan does not put
# toolchains on PATH. Resolve the pinned one directly.
[ -x "$LEAN" ] || fail "no pinned lean at $LEAN (elan toolchain $LEAN_TOOLCHAIN absent)"
"$LEAN" --version | grep -qF "$LEAN_GITHASH" \
  || fail "lean at $LEAN is not commit $LEAN_GITHASH"

mkdir -p "$ROOT" || fail "cannot create $ROOT"

# --- 2. mathlib4 at the pinned commit --------------------------------------
if [ ! -d "$ROOT/mathlib4/.git" ]; then
  [ "$verify_only" -eq 1 ] && fail "mathlib4 absent at $ROOT/mathlib4"
  # blobless: the checkout is ~1 GB of history otherwise, and only one commit
  # is ever checked out.
  git clone --filter=blob:none --no-checkout \
    https://github.com/leanprover-community/mathlib4.git "$ROOT/mathlib4" \
    || fail "mathlib4 clone failed"
fi
observed="$(git -C "$ROOT/mathlib4" rev-parse HEAD 2>/dev/null || echo none)"
if [ "$observed" != "$MATHLIB_COMMIT" ]; then
  [ "$verify_only" -eq 1 ] && fail "mathlib4 HEAD=$observed expected=$MATHLIB_COMMIT"
  git -C "$ROOT/mathlib4" checkout --detach "$MATHLIB_COMMIT" >/dev/null 2>&1 \
    || fail "mathlib4 checkout of $MATHLIB_COMMIT failed"
  observed="$(git -C "$ROOT/mathlib4" rev-parse HEAD)"
  [ "$observed" = "$MATHLIB_COMMIT" ] || fail "mathlib4 HEAD=$observed after checkout"
fi

# --- 3. lean4export at the pinned commit -----------------------------------
if [ ! -d "$ROOT/lean4export/.git" ]; then
  [ "$verify_only" -eq 1 ] && fail "lean4export absent at $ROOT/lean4export"
  git clone https://github.com/leanprover/lean4export.git "$ROOT/lean4export" \
    || fail "lean4export clone failed"
fi
observed="$(git -C "$ROOT/lean4export" rev-parse HEAD 2>/dev/null || echo none)"
if [ "$observed" != "$LEAN4EXPORT_COMMIT" ]; then
  [ "$verify_only" -eq 1 ] && fail "lean4export HEAD=$observed expected=$LEAN4EXPORT_COMMIT"
  git -C "$ROOT/lean4export" checkout --detach "$LEAN4EXPORT_COMMIT" >/dev/null 2>&1 \
    || fail "lean4export checkout of $LEAN4EXPORT_COMMIT failed"
fi
if [ ! -x "$ROOT/lean4export/.lake/build/bin/lean4export" ]; then
  [ "$verify_only" -eq 1 ] && fail "lean4export binary not built"
  ( cd "$ROOT/lean4export" && PATH="$ELAN/bin:$PATH" "$LAKE" build ) >/dev/null 2>&1 \
    || fail "lean4export build failed"
fi
[ -x "$ROOT/lean4export/.lake/build/bin/lean4export" ] || fail "lean4export binary still absent"

# --- 4. the olean cache -----------------------------------------------------
# `lake exe cache get` with no module argument fetches all of Mathlib. A lane
# normally wants a handful of modules; pass them in AXEYUM_MATHLIB_MODULES.
if [ "$verify_only" -eq 0 ] && [ -n "${AXEYUM_MATHLIB_MODULES:-}" ]; then
  # shellcheck disable=SC2086
  ( cd "$ROOT/mathlib4" && PATH="$ELAN/bin:$PATH" "$LAKE" exe cache get $AXEYUM_MATHLIB_MODULES ) \
    >/dev/null 2>&1 || fail "lake exe cache get failed"
fi

echo "AXEYUM_MATHLIB=$ROOT/mathlib4"
echo "AXEYUM_LEAN4EXPORT=$ROOT/lean4export"
echo "AXEYUM_LAKE_BIN=$LAKE"
echo "LEAN_IMPORT_TOOLCHAIN|mathlib=$MATHLIB_COMMIT|lean4export=$LEAN4EXPORT_COMMIT|lean=$LEAN_GITHASH|verdict=PASS"
