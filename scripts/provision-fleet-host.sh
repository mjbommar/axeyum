#!/usr/bin/env bash
# Bring one axeyum fleet host up to the gate-capable baseline.
#
# Idempotent: safe to re-run. Every step reports what it found and what it did,
# because a provisioning script that prints nothing is indistinguishable from
# one that did nothing -- the exact failure class this repository keeps
# catching.
#
# Requirements it establishes are documented in
#   docs/contributor-guide/fleet-hosts.md
set -uo pipefail

NIGHTLY="${AXEYUM_NIGHTLY:-nightly-2026-07-12}"
REPO="${AXEYUM_REPO:-$HOME/projects/personal/axeyum}"
STAGE=/nas3/data/axeyum/bin
CARGO_BIN="$HOME/.cargo/bin"

say() { printf '[%s] %s\n' "$(hostname)" "$*"; }
fail=0

say "=== provisioning $(hostname) ==="

# --- 1. Rust toolchain, pinned -------------------------------------------
if [ ! -x "$CARGO_BIN/rustup" ]; then
  say "rustup: MISSING -- cannot pin toolchain"; fail=1
else
  have=$("$CARGO_BIN/rustc" -vV 2>/dev/null | awk -F': ' '/commit-date/{print $2}')
  say "rustc before: ${have:-none}"
  "$CARGO_BIN/rustup" toolchain install "$NIGHTLY" --profile minimal \
      -c clippy -c rustfmt -c rust-src >/dev/null 2>&1 \
    && say "toolchain $NIGHTLY installed" \
    || { say "toolchain $NIGHTLY install FAILED"; fail=1; }
  "$CARGO_BIN/rustup" default "$NIGHTLY" >/dev/null 2>&1 \
    && say "default set to $NIGHTLY" || { say "rustup default FAILED"; fail=1; }
  say "rustc after: $("$CARGO_BIN/rustc" -vV 2>/dev/null | awk -F': ' '/commit-date/{print $2}')"
fi

# --- 2. just and cargo-deny ----------------------------------------------
# Prefer a staged binary (works on network-isolated hosts); else build it.
for tool in just cargo-deny; do
  if [ -x "$CARGO_BIN/$tool" ]; then
    say "$tool: already present ($("$CARGO_BIN/$tool" --version 2>&1 | head -1))"
  elif [ -x "$STAGE/$tool" ]; then
    install -m 0755 "$STAGE/$tool" "$CARGO_BIN/$tool" \
      && say "$tool: installed from $STAGE" || { say "$tool: stage copy FAILED"; fail=1; }
  else
    say "$tool: building from crates.io (slow)..."
    "$CARGO_BIN/cargo" install "$tool" --locked >/dev/null 2>&1 \
      && say "$tool: built ($("$CARGO_BIN/$tool" --version 2>&1 | head -1))" \
      || { say "$tool: install FAILED"; fail=1; }
  fi
  # Publish back to the shared stage so isolated hosts can be served.
  if [ -x "$CARGO_BIN/$tool" ] && [ ! -x "$STAGE/$tool" ]; then
    mkdir -p "$STAGE" && cp -f "$CARGO_BIN/$tool" "$STAGE/$tool" 2>/dev/null \
      && say "$tool: staged to $STAGE for isolated hosts"
  fi
done

# --- 3. Pinned Lean ------------------------------------------------------
# TWO valid layouts, and knowing only one is how the first version of this
# script reported "lean: installed" over a host that had none:
#   $HOME/.elan/toolchains/*/bin/lean             elan's own default (s5)
#   $HOME/.elan/elan-home/toolchains/*/bin/lean   install-pinned-lean.sh's root
# The check below is on the ARTIFACT, executed -- never on the installer's exit
# status, which is 0 in both the installed and the not-where-you-looked case.
lean_bin() {
  ls "$HOME"/.elan/elan-home/toolchains/*/bin/lean \
     "$HOME"/.elan/toolchains/*/bin/lean 2>/dev/null | head -1
}
if [ -x "$(lean_bin)" ]; then
  say "lean: already present ($("$(lean_bin)" --version 2>&1 | head -1))"
elif [ -x "$REPO/scripts/install-pinned-lean.sh" ]; then
  say "lean: installing repo-pinned toolchain..."
  "$REPO/scripts/install-pinned-lean.sh" "$HOME/.elan" >/dev/null 2>&1 || true
  if [ -x "$(lean_bin)" ]; then
    say "lean: installed ($("$(lean_bin)" --version 2>&1 | head -1))"
  else
    say "lean: install FAILED -- no runnable binary under \$HOME/.elan"; fail=1
  fi
else
  say "lean: installer not found at $REPO/scripts/install-pinned-lean.sh"; fail=1
fi

# --- 4. Commit hooks in the checkout -------------------------------------
if [ -d "$REPO/.git" ]; then
  git -C "$REPO" config core.hooksPath hooks \
    && say "core.hooksPath=hooks set in $REPO" || { say "hooksPath FAILED"; fail=1; }
else
  say "no checkout at $REPO -- skipping hooksPath"
fi

# --- 5. Verify the ARTIFACTS, not the steps ------------------------------
# The first version of this script exited 0 over a host with no Lean, because
# every check was on an installer's exit status. Provisioning is not the claim;
# this block is.
say "--- verification ---"
v() { # name, command that must print something
  out=$(eval "$2" 2>/dev/null | head -1)
  if [ -n "$out" ]; then say "OK   $1: $out"; else say "FAIL $1: absent"; fail=1; fi
}
v rustc      "\"$CARGO_BIN/rustc\" -vV | awk -F': ' '/commit-date/{print \$2}'"
v clippy     "\"$CARGO_BIN/cargo\" clippy -V"
v rustfmt    "\"$CARGO_BIN/rustfmt\" --version"
v just       "\"$CARGO_BIN/just\" --version"
v cargo-deny "\"$CARGO_BIN/cargo-deny\" --version"
v lean       "\"\$(lean_bin)\" --version"
v hooksPath  "git -C \"$REPO\" config --get core.hooksPath"
v nas3       "[ -w /nas3/data ] && echo rw"

say "=== done (fail=$fail) ==="
exit $fail
