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

# scripts/check-lean-gate.sh discovers via "$ELAN_HOME|$HOME/.elan"/toolchains
# ONLY. install-pinned-lean.sh writes to $ROOT/elan-home/toolchains, so a host
# provisioned by it leaves the gate unable to find a Lean that is installed --
# measured on s7, where the gate reported "no Lean binary" beside a working
# 4.30.0. It fails closed rather than skipping, which is right, but the lane
# still cannot run it. Normalise the layout so discovery works either way.
if [ -d "$HOME/.elan/elan-home/toolchains" ] && [ ! -e "$HOME/.elan/toolchains" ]; then
  ln -sfn "$HOME/.elan/elan-home/toolchains" "$HOME/.elan/toolchains" \
    && say "lean: linked .elan/toolchains -> elan-home/toolchains (gate discovery)"
fi
if [ -d "$HOME/.elan/elan-home/bin" ] && [ ! -e "$HOME/.elan/bin" ]; then
  ln -sfn "$HOME/.elan/elan-home/bin" "$HOME/.elan/bin" \
    && say "lean: linked .elan/bin -> elan-home/bin (elan shim)"
fi

# --- 3b. cargo on PATH for NON-INTERACTIVE ssh ---------------------------
# `ssh host 'script'` runs a non-interactive bash. Ubuntu's stock ~/.bashrc
# returns early for those, so ~/.cargo/bin is absent and a gate dies with
# "cargo: command not found" -- then reports the suite as ZERO tests, which
# reads as a gate failure rather than an environment one. Measured on s5.
# bash DOES source ~/.bashrc for ssh-launched shells, so exporting ABOVE the
# interactivity guard fixes it.
# It must be PREPENDED, not appended: the stock guard is near the TOP of
# ~/.bashrc and returns before anything after it is read, so a line at the end
# of the file never executes in the case it exists to fix.
if ! grep -q 'AXEYUM_FLEET_PATH' "$HOME/.bashrc" 2>/dev/null; then
  tmp=$(mktemp)
  { printf '# AXEYUM_FLEET_PATH: cargo must be on PATH for non-interactive ssh\n'
    printf '# gates. Kept ABOVE the interactivity guard below, which returns early\n'
    printf '# for ssh-launched shells -- appending this would never run.\n'
    printf 'export PATH="$HOME/.cargo/bin:$PATH"\n\n'
    cat "$HOME/.bashrc" 2>/dev/null; } > "$tmp" \
    && cp "$tmp" "$HOME/.bashrc" && rm -f "$tmp" \
    && say "PATH: prepended ~/.cargo/bin to ~/.bashrc (non-interactive ssh)" \
    || { say "PATH: ~/.bashrc edit FAILED"; fail=1; }
else
  say "PATH: ~/.bashrc already exports ~/.cargo/bin"
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
# The two checks that matter for GATES rather than for tools: can
# check-lean-gate.sh discover Lean where it actually looks, and does a
# NON-INTERACTIVE ssh see cargo. Both were false on this fleet after the first
# provisioning pass while every tool above reported OK.
v lean-discoverable "ls \"\$HOME\"/.elan/toolchains/*/bin/lean 2>/dev/null | head -1"
# The PATH export is only useful if it sits ABOVE ~/.bashrc's early-return
# guard. Assert the ORDER, not the mere presence -- a check that only greps for
# the line would pass on the appended version, which never executes. (An
# `ssh localhost` probe would be worse still: it is unconfigured here, so it
# falls through to a local lookup that cannot fail.)
v bashrc-path-order "awk '/AXEYUM_FLEET_PATH/{e=NR} /^[[:space:]]*(case[[:space:]]+\\\$-|\\[ -z \"\\\$PS1\" \\])/{if(!g)g=NR} END{if(e && (!g || e<g)) print \"export@\" e \" guard@\" (g?g:\"none\")}' \"\$HOME/.bashrc\""

say "=== done (fail=$fail) ==="
exit $fail
