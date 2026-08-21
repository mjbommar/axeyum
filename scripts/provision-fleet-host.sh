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

# --- 2b. Bubblewrap proposer isolation ----------------------------------
# Autogenesis proposers must not see retained proof bodies, the checkout, or
# the network. A catalog without an OS boundary is only a convention. All five
# fleet hosts had bubblewrap 0.11.1 on 2026-08-18; retain installation here so
# a replacement host cannot silently run a weaker aggregate gate.
if ! command -v bwrap >/dev/null 2>&1; then
  say "bubblewrap: installing OS package..."
  if sudo -n apt-get update >/dev/null 2>&1 \
      && sudo -n apt-get install -y bubblewrap >/dev/null 2>&1; then
    say "bubblewrap: installed ($(bwrap --version 2>&1 | head -1))"
  else
    say "bubblewrap: install FAILED -- Autogenesis proposer isolation cannot run"
    fail=1
  fi
else
  say "bubblewrap: already present ($(bwrap --version 2>&1 | head -1))"
fi

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
# Exposing the SHIM is not the same as making it work. `~/.elan/bin/lean` is
# elan, which resolves a toolchain from ELAN_HOME's settings.toml -- and with
# ELAN_HOME defaulting to ~/.elan it found the symlinked toolchains but NO
# default, so it exited "no default toolchain configured". That is worse than
# not exposing it: check-lean-gate.sh prefers PATH over its own search, so a
# shim on PATH SHADOWS the working toolchain binary. Measured on s7, where it
# failed one suite and with it the fact F:ordered-ring-farkas-refutation.
# Probe from a directory with NO `lean-toolchain` file. The repo root HAS one,
# and elan reads it in preference to any default -- so probing there exercises
# the wrong path and reports a working shim that fails everywhere else. That is
# how this check passed on all five hosts while `real_lean_strict_positivity_
# crosscheck`, which runs Lean in a temp dir, still died with "no default
# toolchain configured".
if [ -x "$HOME/.elan/bin/elan" ] && ! (cd / && "$HOME/.elan/bin/lean" --version >/dev/null 2>&1); then
  ELAN_HOME="$HOME/.elan" "$HOME/.elan/bin/elan" default \
      "$(tr -d '[:space:]' < "$REPO/lean-toolchain" 2>/dev/null || echo leanprover/lean4:v4.30.0)" \
      >/dev/null 2>&1 \
    && say "lean: elan default toolchain configured (shim now resolves)" \
    || { say "lean: elan default FAILED -- shim on PATH would shadow a working lean"; fail=1; }
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

# --- 3b. What `scripts/local-ci.sh` needs --------------------------------
# Hosted CI's own comment calls local-ci.sh "the authoritative gate for main".
# Measured 2026-08-18 it could not run on ANY host in this fleet, and this
# script was why: it installs the pinned nightly, just, cargo-deny and Lean, and
# none of the three things local-ci.sh actually invokes. On the dev box,
# `cargo nextest --version` exited 101 (no such command) and
# `rustup run 1.88.0 cargo --version` exited 1 (toolchain not installed) --
# and `cargo nextest run --profile local --workspace --all-features` IS the
# test sweep. So the gate had never run anywhere, and nothing said so.
#
# `--profile minimal` is not tidiness: a plain `rustup toolchain install 1.88.0`
# FAILS on this fleet's rustup with "some components are unavailable for
# download for channel '1.88.0': 'miri', 'rustc-codegen-cranelift'", because it
# inherits the default profile's component set from the nightly channel.
"$CARGO_BIN/rustup" toolchain install stable --profile minimal -c clippy >/dev/null 2>&1 \
  && say "stable: present ($("$CARGO_BIN/rustup" run stable rustc --version 2>&1 | head -1))" \
  || { say "stable toolchain install FAILED"; fail=1; }
"$CARGO_BIN/rustup" toolchain install 1.88.0 --profile minimal >/dev/null 2>&1 \
  && say "MSRV 1.88.0: present ($("$CARGO_BIN/rustup" run 1.88.0 rustc --version 2>&1 | head -1))" \
  || { say "MSRV 1.88.0 install FAILED"; fail=1; }

if [ -x "$CARGO_BIN/cargo-nextest" ]; then
  say "cargo-nextest: already present ($("$CARGO_BIN/cargo-nextest" --version 2>&1 | head -1))"
elif [ -x "$STAGE/cargo-nextest" ]; then
  install -m 0755 "$STAGE/cargo-nextest" "$CARGO_BIN/cargo-nextest" \
    && say "cargo-nextest: installed from $STAGE" \
    || { say "cargo-nextest: stage copy FAILED"; fail=1; }
else
  say "cargo-nextest: building from crates.io (slow)..."
  "$CARGO_BIN/cargo" install cargo-nextest --locked >/dev/null 2>&1 \
    && say "cargo-nextest: built ($("$CARGO_BIN/cargo-nextest" --version 2>&1 | head -1))" \
    || { say "cargo-nextest: install FAILED"; fail=1; }
fi
if [ -x "$CARGO_BIN/cargo-nextest" ] && [ ! -x "$STAGE/cargo-nextest" ]; then
  mkdir -p "$STAGE" && cp -f "$CARGO_BIN/cargo-nextest" "$STAGE/cargo-nextest" 2>/dev/null \
    && say "cargo-nextest: staged to $STAGE for isolated hosts"
fi

if command -v z3 >/dev/null 2>&1; then
  say "z3: present ($(z3 --version 2>&1 | head -1))"
else
  say "z3: MISSING -- needs root: sudo apt-get install -y z3 libz3-dev"
  say "     (not installed here: this script does not assume sudo)"
  fail=1
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
v bubblewrap "bwrap --version"
v bwrap-sandbox "bwrap --ro-bind /usr /usr /usr/bin/true && echo runnable"
v lean       "\"\$(lean_bin)\" --version"
v hooksPath  "git -C \"$REPO\" config --get core.hooksPath"
v nas3       "[ -w /nas3/data ] && echo rw"
# The local-ci prerequisites, verified the way this block verifies everything
# else -- by making the tool speak, not by trusting the installer's exit status.
v msrv-1.88  "\"$CARGO_BIN/rustup\" run 1.88.0 rustc --version"
v stable     "\"$CARGO_BIN/rustup\" run stable rustc --version"
v nextest    "\"$CARGO_BIN/cargo-nextest\" --version"
v z3         "z3 --version"
# ...and then the claim that actually matters: does the authoritative gate agree
# it can run here? Its preflight is the authority, not this list.
v local-ci-preflight "scripts/local-ci.sh --preflight-only 2>&1 | head -1"
# The two checks that matter for GATES rather than for tools: can
# check-lean-gate.sh discover Lean where it actually looks, and does a
# NON-INTERACTIVE ssh see cargo. Both were false on this fleet after the first
# provisioning pass while every tool above reported OK.
v lean-discoverable "ls \"\$HOME\"/.elan/toolchains/*/bin/lean 2>/dev/null | head -1"
# If a shim exists it MUST resolve, because check-lean-gate.sh searches PATH
# first and a broken shim there shadows the working toolchain binary. Checking
# lean_bin() alone passed while exactly this was broken -- it resolves the
# toolchain directly and never exercises the shim. Hosts without an elan binary
# (s5) have no shim and correctly skip.
v lean-shim "[ -x \"\$HOME/.elan/bin/lean\" ] && (cd / && \"\$HOME/.elan/bin/lean\" --version) || echo 'n/a (no shim on this host)'"
# The PATH export is only useful if it sits ABOVE ~/.bashrc's early-return
# guard. Assert the ORDER, not the mere presence -- a check that only greps for
# the line would pass on the appended version, which never executes. (An
# `ssh localhost` probe would be worse still: it is unconfigured here, so it
# falls through to a local lookup that cannot fail.)
v bashrc-path-order "awk '/AXEYUM_FLEET_PATH/{e=NR} /^[[:space:]]*(case[[:space:]]+\\\$-|\\[ -z \"\\\$PS1\" \\])/{if(!g)g=NR} END{if(e && (!g || e<g)) print \"export@\" e \" guard@\" (g?g:\"none\")}' \"\$HOME/.bashrc\""

say "=== done (fail=$fail) ==="
exit $fail
