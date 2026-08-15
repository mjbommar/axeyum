#!/usr/bin/env bash
# Export a named corpus of official Lean `Init`/`Std` declarations with
# `lean4export` and census them through `axeyum-lean-import`.
#
# Why a script rather than a one-liner. The first measurement of this strand
# (docs/formalized-math-2026-08/diary-formalized-collect.md) reported "13 of 40
# admitted" over a corpus that was never written down, so the number could not be
# re-measured after a kernel change. The corpus below IS the corpus: it is
# committed, it is exported deterministically, and the census is fail-open at the
# kernel gate only (see `census_ndjson`), so a stream reports every blocker
# instead of its first one.
#
# `lean4export` is NOT vendored (it is a 200 MB build). Point AXEYUM_LEAN4EXPORT
# at a checkout whose `.lake/build/bin/lean4export` exists, or let the script
# find one under ~/.cache. With none present it exits 2 rather than reporting an
# empty census as a clean one.
#
# Usage:
#   scripts/lean-import-census.sh                    # full corpus
#   scripts/lean-import-census.sh Nat.add_comm ...   # named declarations only
#   AXEYUM_CENSUS_OUT=dir scripts/lean-import-census.sh
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2
repo="$PWD"

out="${AXEYUM_CENSUS_OUT:-$(mktemp -d)}"
mkdir -p "$out" || exit 2

# ---------------------------------------------------------------------------
# The corpus. Forty declarations from Lean 4.30.0 `Init`/`Std`, chosen to span
# the reduction behaviours an importer actually meets: `rfl`-proved equations of
# structurally recursive functions, recursor-encoded induction, `HEq`,
# `noConfusion`, decidability, and a few that need no computation at all.
# ---------------------------------------------------------------------------
CORPUS=(
  # --- Nat arithmetic: the brecOn/below core ---
  Nat.add_zero
  Nat.add_succ
  Nat.zero_add
  Nat.succ_add
  Nat.add_comm
  Nat.add_assoc
  Nat.mul_zero
  Nat.mul_succ
  Nat.mul_comm
  Nat.mul_one
  Nat.one_mul
  Nat.left_distrib
  Nat.pow_zero
  Nat.pow_succ
  Nat.sub_zero
  Nat.succ_sub_succ
  # --- Nat order ---
  Nat.le_refl
  Nat.le_succ
  Nat.lt_irrefl
  Nat.le_trans
  Nat.not_succ_le_zero
  Nat.succ_ne_zero
  # --- equality, HEq, and the propositional core ---
  eq_of_heq
  heq_of_eq
  congrArg
  congrFun
  Eq.symm
  Eq.trans
  id_eq
  # --- logic ---
  and_comm
  or_comm
  Classical.not_not
  Classical.em
  Classical.byContradiction
  # --- Bool / decidability ---
  Bool.and_comm
  Bool.not_not
  Bool.decide_and
  # --- List: a second recursive family ---
  List.nil_append
  List.append_assoc
  List.length_append
)

if [ "$#" -gt 0 ]; then
  CORPUS=("$@")
fi

# --- toolchain discovery (elan does not put lean/lake on PATH) --------------
lake_bin="${AXEYUM_LAKE_BIN:-}"
if [ -z "$lake_bin" ]; then
  if command -v lake >/dev/null 2>&1; then
    lake_bin="$(command -v lake)"
  else
    for candidate in "${ELAN_HOME:-$HOME/.elan}"/toolchains/*/bin/lake; do
      [ -x "$candidate" ] && lake_bin="$candidate" && break
    done
  fi
fi

export_dir="${AXEYUM_LEAN4EXPORT:-}"
if [ -z "$export_dir" ]; then
  for candidate in "$HOME"/.cache/*/lean4export; do
    [ -x "$candidate/.lake/build/bin/lean4export" ] && export_dir="$candidate" && break
  done
fi

if [ -z "$lake_bin" ] || [ -z "$export_dir" ]; then
  echo "CENSUS-UNAVAILABLE lake='${lake_bin:-none}' lean4export='${export_dir:-none}'" >&2
  echo "Set AXEYUM_LAKE_BIN and AXEYUM_LEAN4EXPORT. Refusing to report an empty census." >&2
  exit 2
fi
PATH="$(dirname "$lake_bin"):$PATH"
export PATH

echo "corpus=${#CORPUS[@]} lake=$lake_bin lean4export=$export_dir out=$out"

# --- export ----------------------------------------------------------------
exported=0
export_failed=()
for name in "${CORPUS[@]}"; do
  target="$out/$name.ndjson"
  if [ ! -s "$target" ]; then
    (cd "$export_dir" && "$lake_bin" env ./.lake/build/bin/lean4export Init Std \
      -- "$name" >"$target" 2>"$out/$name.err")
    # `lean4export` EXITS 0 on an unknown constant: it panics to stderr and
    # writes a metadata-only stream. Measured 2026-08-15 on `not_not` (which is
    # Mathlib, not core) -- one record, no declarations, and the census scored it
    # as a CLEAN stream. A tool that was never pointed at your subject returns
    # the same empty answer as a strong negative result, so both signals are
    # checked: the panic marker, and an export with no declaration record.
    if grep -q "^PANIC" "$out/$name.err" 2>/dev/null || [ "$(wc -l <"$target")" -lt 2 ]; then
      export_failed+=("$name")
      rm -f "$target"
      continue
    fi
  fi
  exported=$((exported + 1))
done

if [ "${#export_failed[@]}" -gt 0 ]; then
  echo "EXPORT-FAILED(${#export_failed[@]}): ${export_failed[*]}"
fi
if [ "$exported" -eq 0 ]; then
  echo "no declaration exported; refusing to report a census over nothing" >&2
  exit 2
fi
echo "EXPORTED=$exported of ${#CORPUS[@]}"

# --- census ----------------------------------------------------------------
cd "$repo" || exit 2
cargo build -q -p axeyum-lean-import --example lean4export_census || exit 2
bin="$repo/target/debug/examples/lean4export_census"
[ -x "$bin" ] || { echo "census example not built" >&2; exit 2; }

# One stream per declaration keeps a decline attributable to the declaration
# that was asked for, and keeps the per-stream admitted/declined counts that the
# strand reports as "N of 40".
streams=()
for name in "${CORPUS[@]}"; do
  [ -s "$out/$name.ndjson" ] && streams+=("$out/$name.ndjson")
done
"$bin" "${streams[@]}"
