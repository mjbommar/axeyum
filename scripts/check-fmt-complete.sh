#!/usr/bin/env bash
# Formatting check over EVERY .rs file on disk, not the ones cargo can find.
#
# `cargo fmt --all` discovers files by walking `mod` declarations from each
# crate root. rustfmt does not expand macros, so any module declared inside one
# is invisible to it. `axeyum-solver` declares its module tree inside
# `macro_rules! full_modules`, which put **156 modules / 221,445 lines --
# including the entire trusted proof-reconstruction layer -- outside the gate**.
#
# Measured 2026-08-14: 886 `.rs` files under `crates/`, of which `cargo fmt
# --all` examined a strict subset; 14 source files had never been formatted and
# the workspace gate was green over all of them. Reproduced directly by
# appending `fn __fmt_probe(  ) ->    usize {   let    x=1  ;  x  }` to
# `crates/axeyum-solver/src/reconstruct/resolution.rs`:
#
#     cargo fmt --all --check     -> exit 0, file never mentioned
#     rustfmt --check <that file> -> the probe, twice
#
# This script enumerates from the filesystem instead, so a module hidden behind
# any macro is still checked. It is deliberately a *superset* of
# `cargo fmt --all --check`; keep both, because they fail for different reasons
# and a disagreement between them is itself a finding.
#
# Usage:  scripts/check-fmt-complete.sh [--fix]
set -euo pipefail

cd "$(dirname "$0")/.."

# Generated fixtures are checked in as bytes and asserted against; reformatting
# one would change what a test is pinned to. Excluded deliberately, by path, so
# the exclusion is visible rather than implicit.
EXCLUDE_RE='tests/fixtures/'

mode="check"
[[ "${1:-}" == "--fix" ]] && mode="fix"

mapfile -t files < <(find crates -name '*.rs' -not -path '*/target/*' \
    | grep -Ev "$EXCLUDE_RE" | sort)

if [[ ${#files[@]} -eq 0 ]]; then
    echo "check-fmt-complete: found no .rs files -- the enumeration is broken" >&2
    exit 2
fi

failed=()
for f in "${files[@]}"; do
    if [[ "$mode" == "fix" ]]; then
        rustfmt --edition 2024 "$f"
    elif ! rustfmt --edition 2024 --check "$f" >/dev/null 2>&1; then
        failed+=("$f")
    fi
done

if [[ "$mode" == "fix" ]]; then
    echo "check-fmt-complete: formatted ${#files[@]} files"
    exit 0
fi

echo "check-fmt-complete: checked ${#files[@]} files"

if [[ ${#failed[@]} -gt 0 ]]; then
    echo "check-fmt-complete: ${#failed[@]} file(s) not formatted:" >&2
    printf '  %s\n' "${failed[@]}" >&2
    echo "run: scripts/check-fmt-complete.sh --fix" >&2
    exit 1
fi
