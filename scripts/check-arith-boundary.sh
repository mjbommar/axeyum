#!/usr/bin/env bash
# The `axeyum-arith` boundary: no crate but `axeyum-arith` may name
# `num-bigint`, `num-rational`, `num-integer` or `num-traits` — in code or in a
# manifest.
#
# WHY THIS IS A GATE AND NOT A CONVENTION. ADR-1710's measurement is that eight
# modules grew their own `BigRational` path, five of them over the same type,
# because each one could name the upstream crate for itself. A crate that can
# write `use num_bigint::BigInt;` can also write its own gcd, its own
# `pow_mod`, and its own Sturm chain — and eight of them did. Prose did not
# stop that; the design note says so about `git archive --touch` in the same
# breath. So the boundary is a command whose exit status depends on the
# finding.
#
# WHAT IT CHECKS
#
#   1. No Rust source under `crates/` outside `crates/axeyum-arith` matches
#      `num_bigint|num_rational|num_integer|num_traits` (the `_` spelling: the
#      one a `use` or a qualified path takes).
#   2. No `Cargo.toml` under `crates/` outside `crates/axeyum-arith` declares
#      `num-bigint`, `num-rational`, `num-integer` or `num-traits` (the `-`
#      spelling: the one a manifest takes).
#   3. Every line of the allowlist still names a file that HAS a hit. A stale
#      allowlist entry is a hole nobody can see, so it fails the gate in the
#      other direction: the exit status depends on the finding both ways.
#
# WHAT IT DOES NOT CHECK, DELIBERATELY. The ROOT `Cargo.toml` is out of scope.
# Its `[workspace.dependencies]` block is what makes `num-bigint.workspace =
# true` resolve to one version for the whole tree (migration slice 0), so
# removing it would put the version pins back in the leaves — the opposite of
# the thing this gate is for. `Cargo.lock` is likewise out of scope: it is
# generated and every transitive dependency appears in it.
#
# The allowlist is `scripts/arith-boundary-allowlist.txt`: one path per line,
# `#` starts a comment, and every entry must carry a reason. An empty
# allowlist is the goal state.
#
# GREP SEMANTICS. This script runs under `#!/usr/bin/env bash`, so `grep` is
# GNU grep, not the `ugrep` an interactive shell here resolves. The patterns
# below use only POSIX basic classes for that reason.
#
# COST: ~1 second (a `find` plus one `grep -rlE` over `crates/`).

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

allowlist_file="scripts/arith-boundary-allowlist.txt"
exempt_crate="crates/axeyum-arith"

# --- read the allowlist ------------------------------------------------------
declare -A allowed=()
allowlist_paths=()
if [[ -f "$allowlist_file" ]]; then
  while IFS= read -r line; do
    line="${line%%#*}"
    line="$(printf '%s' "$line" | tr -d '[:space:]')"
    [[ -z "$line" ]] && continue
    allowed["$line"]=1
    allowlist_paths+=("$line")
  done <"$allowlist_file"
fi

# --- guard 1: Rust sources ---------------------------------------------------
code_hits=()
while IFS= read -r path; do
  [[ "$path" == "$exempt_crate"/* ]] && continue
  code_hits+=("$path")
done < <(grep -rlE 'num_bigint|num_rational|num_integer|num_traits' \
  --include='*.rs' crates 2>/dev/null | sort)

# --- guard 2: manifests ------------------------------------------------------
manifest_hits=()
while IFS= read -r path; do
  [[ "$path" == "$exempt_crate"/* ]] && continue
  if grep -qE '^[[:space:]]*num-(bigint|rational|integer|traits)[[:space:].]' "$path"; then
    manifest_hits+=("$path")
  fi
done < <(find crates -name Cargo.toml -type f | sort)

# --- report ------------------------------------------------------------------
status=0
violations=0

for path in "${code_hits[@]:-}" "${manifest_hits[@]:-}"; do
  [[ -z "$path" ]] && continue
  if [[ -n "${allowed[$path]:-}" ]]; then
    continue
  fi
  if [[ $violations -eq 0 ]]; then
    echo "FAIL: files outside $exempt_crate name num-bigint/num-rational/num-integer/num-traits:"
  fi
  violations=$((violations + 1))
  echo "  $path"
  grep -nE 'num_bigint|num_rational|num_integer|num_traits|^[[:space:]]*num-(bigint|rational|integer|traits)[[:space:].]' \
    "$path" | head -3 | sed 's/^/      /'
done

if [[ $violations -gt 0 ]]; then
  echo
  echo "Import these names from axeyum_arith::big instead, and drop the"
  echo "manifest entry. If a use genuinely cannot be removed, add the path to"
  echo "$allowlist_file with the reason on the same line."
  status=1
fi

# --- guard 3: no stale allowlist entries -------------------------------------
stale=0
for path in "${allowlist_paths[@]:-}"; do
  [[ -z "$path" ]] && continue
  if [[ ! -e "$path" ]]; then
    [[ $stale -eq 0 ]] && echo "FAIL: stale allowlist entries in $allowlist_file:"
    stale=$((stale + 1))
    echo "  $path (no such file)"
    continue
  fi
  if ! grep -qE 'num_bigint|num_rational|num_integer|num_traits|^[[:space:]]*num-(bigint|rational|integer|traits)[[:space:].]' "$path"; then
    [[ $stale -eq 0 ]] && echo "FAIL: stale allowlist entries in $allowlist_file:"
    stale=$((stale + 1))
    echo "  $path (no longer names any of the four crates — delete the line)"
  fi
done
if [[ $stale -gt 0 ]]; then
  status=1
fi

examined=$((${#code_hits[@]} + ${#manifest_hits[@]}))
allowed_count=${#allowlist_paths[@]}
if [[ $status -eq 0 ]]; then
  echo "OK: arith boundary holds."
fi
echo "arith-boundary: ${examined} file(s) outside $exempt_crate name the four crates," \
  "${allowed_count} allowlisted, ${violations} unallowed, ${stale} stale allowlist entr(ies)."

exit "$status"
