#!/usr/bin/env bash
# Cross-check every `imported-kernel-lean` fact's axiom footprint against the
# SOURCE system, using a real `lean` binary.
#
# WHY THIS EXISTS. `cargo test -p axeyum-lean-import --test imported_fact_evidence`
# re-derives each imported fact from its pinned stream using OUR kernel. That is
# one checker. It cannot tell us whether our kernel and Lean's agree about what
# the theorem rests on -- and they do not always spell the answer the same way.
#
# Measured 2026-08-15 on `Classical.em`: Lean reports three names
# (`propext`, `Classical.choice`, `Quot.sound`); `Kernel::axiom_footprint`
# reports six, adding `Quot`, `Quot.mk` and `Quot.lift`, because our kernel
# classifies the whole quotient package as trusted `Quotient` declarations. Both
# are correct within their own vocabulary and ours is the more conservative one.
# So this script pins LEAN's answer, not ours, and the disagreement is recorded
# rather than reconciled.
#
# On the four axiom-free imports the two kernels agree exactly, and that
# agreement is the cross-oracle signal a fact's `checkers` list is for.
#
# NO TOOLCHAIN IS A FAILURE BY DEFAULT, following `scripts/check-lean-gate.sh`:
# a machine that genuinely has no Lean sets `AXEYUM_ALLOW_NO_LEAN=1` and gets a
# banner saying, in words, that zero Lean checks ran. An absent binary that
# quietly passes is this repository's signature defect.
#
# Usage:
#   scripts/check-imported-fact-lean-axioms.sh              # all facts
#   scripts/check-imported-fact-lean-axioms.sh Classical.em # one declaration
#   AXEYUM_LEAN_BIN=/path/to/lean  …                        # explicit override
#   AXEYUM_ALLOW_NO_LEAN=1         …                        # loud SKIP, exit 0
set -uo pipefail
cd "$(dirname "$0")/.."

FILTER="${1:-}"

# Each row: <declaration>|<expected `#print axioms` payload>
# The payload is compared as a SET of names, because Lean's ordering is not a
# documented guarantee.
ROWS=(
  "Nat.le_refl|"
  "Nat.le_succ|"
  "List.nil_append|"
  "Bool.and_comm|"
  "Classical.em|propext,Classical.choice,Quot.sound"
)

# Mathlib-sourced rows (ADR-0603 row 4 for IVT/EVT). Each row:
# <declaration>|<expected payload>|<Mathlib import module>
# These need `lake env lean` run FROM WITHIN a mathlib4 checkout, because a
# bare `lean A.lean` has no idea `intermediate_value_Icc` exists -- it is not
# in Init/Std. See scripts/provision-lean-import-toolchain.sh.
MATHLIB_ROWS=(
  "intermediate_value_Icc|propext,Classical.choice,Quot.sound|Mathlib.Topology.Order.IntermediateValue"
  "IsCompact.exists_isMaxOn|propext,Classical.choice,Quot.sound|Mathlib.Topology.Order.Compact"
)

# Toolchain discovery, in the same order as scripts/check-lean-gate.sh: elan
# installs under ~/.elan/toolchains/*/bin/lean and does NOT put them on PATH, so
# `which lean` printing nothing is not evidence that Lean is absent.
discover_lean() {
  if [ -n "${AXEYUM_LEAN_BIN:-}" ] && [ -x "${AXEYUM_LEAN_BIN}" ]; then
    printf '%s' "${AXEYUM_LEAN_BIN}"
    return 0
  fi
  if command -v lean >/dev/null 2>&1; then
    command -v lean
    return 0
  fi
  local home="${ELAN_HOME:-$HOME/.elan}"
  local candidate
  for candidate in "$home"/toolchains/*/bin/lean; do
    if [ -x "$candidate" ]; then
      printf '%s' "$candidate"
      return 0
    fi
  done
  return 1
}

LEAN="$(discover_lean)" || LEAN=""
if [ -z "$LEAN" ]; then
  if [ -n "${AXEYUM_ALLOW_NO_LEAN:-}" ]; then
    echo "imported-fact-lean-axioms: SKIPPED -- no lean binary found."
    echo "imported-fact-lean-axioms: ZERO Lean checks ran. This is not a pass."
    exit 0
  fi
  echo "imported-fact-lean-axioms: no lean binary found (tried AXEYUM_LEAN_BIN, PATH," >&2
  echo "  \${ELAN_HOME:-~/.elan}/toolchains/*/bin/lean). Set AXEYUM_ALLOW_NO_LEAN=1" >&2
  echo "  to skip loudly on a machine that genuinely has none." >&2
  exit 1
fi

# Mathlib checkout discovery, matching scripts/provision-lean-import-toolchain.sh.
MATHLIB_ROOT="${AXEYUM_LEAN_ROOT:-/data0/axeyum/lean-import-toolchain}"
MATHLIB_DIR="$MATHLIB_ROOT/mathlib4"
LAKE_BIN="$(dirname "$LEAN")/lake"

WORK="$(mktemp -d)"
trap 'rm -f "$WORK"/A.lean "$WORK"/out.txt; rmdir "$WORK" 2>/dev/null || true' EXIT

checked=0
failed=0
for row in "${ROWS[@]}"; do
  decl="${row%%|*}"
  want="${row#*|}"
  if [ -n "$FILTER" ] && [ "$decl" != "$FILTER" ]; then
    continue
  fi
  printf '#print axioms %s\n' "$decl" > "$WORK/A.lean"
  if ! "$LEAN" "$WORK/A.lean" > "$WORK/out.txt" 2>&1; then
    echo "  FAIL  $decl: lean exited non-zero" >&2
    sed 's/^/    /' "$WORK/out.txt" >&2
    failed=$((failed + 1))
    continue
  fi
  line="$(tr -d '\n' < "$WORK/out.txt")"
  if [ "$line" = "'$decl' does not depend on any axioms" ]; then
    got=""
  else
    got="$(printf '%s' "$line" | sed -n "s/^'$decl' depends on axioms: \[\(.*\)\]$/\1/p" | tr -d ' ')"
    if [ -z "$got" ]; then
      echo "  FAIL  $decl: unrecognised lean output: $line" >&2
      failed=$((failed + 1))
      continue
    fi
  fi
  got_sorted="$(printf '%s' "$got" | tr ',' '\n' | sort | paste -sd, -)"
  want_sorted="$(printf '%s' "$want" | tr ',' '\n' | sort | paste -sd, -)"
  checked=$((checked + 1))
  if [ "$got_sorted" = "$want_sorted" ]; then
    echo "AXEYUM-LEAN-AXIOMS|$decl|lean=${got_sorted:-none}|ok"
  else
    echo "  FAIL  $decl: lean says [${got_sorted}], fact pins [${want_sorted}]" >&2
    failed=$((failed + 1))
  fi
done

# --- Mathlib-sourced rows: need `lake env lean` from within the mathlib4
# checkout, with the target's own module imported first. ---
mathlib_wanted=0
for row in "${MATHLIB_ROWS[@]}"; do
  decl="${row%%|*}"
  if [ -z "$FILTER" ] || [ "$decl" = "$FILTER" ]; then
    mathlib_wanted=$((mathlib_wanted + 1))
  fi
done

if [ "$mathlib_wanted" -gt 0 ]; then
  if [ ! -x "$LAKE_BIN" ] || [ ! -d "$MATHLIB_DIR/.git" ]; then
    if [ -n "${AXEYUM_ALLOW_NO_LEAN:-}" ]; then
      echo "imported-fact-lean-axioms: SKIPPED $mathlib_wanted Mathlib row(s) -- no mathlib4 checkout at $MATHLIB_DIR (run scripts/provision-lean-import-toolchain.sh)."
    else
      echo "imported-fact-lean-axioms: no mathlib4 checkout at $MATHLIB_DIR (or no lake at $LAKE_BIN)." >&2
      echo "  Run scripts/provision-lean-import-toolchain.sh --verify, or set AXEYUM_ALLOW_NO_LEAN=1" >&2
      echo "  to skip loudly on a machine that genuinely has none." >&2
      failed=$((failed + mathlib_wanted))
    fi
  else
    for row in "${MATHLIB_ROWS[@]}"; do
      decl="${row%%|*}"
      rest="${row#*|}"
      want="${rest%%|*}"
      module="${rest#*|}"
      if [ -n "$FILTER" ] && [ "$decl" != "$FILTER" ]; then
        continue
      fi
      printf 'import %s\n#print axioms %s\n' "$module" "$decl" > "$WORK/A.lean"
      if ! ( cd "$MATHLIB_DIR" && "$LAKE_BIN" env "$LEAN" "$WORK/A.lean" > "$WORK/out.txt" 2>&1 ); then
        echo "  FAIL  $decl: lake env lean exited non-zero" >&2
        sed 's/^/    /' "$WORK/out.txt" >&2
        failed=$((failed + 1))
        continue
      fi
      line="$(tr -d '\n' < "$WORK/out.txt")"
      if [ "$line" = "'$decl' does not depend on any axioms" ]; then
        got=""
      else
        got="$(printf '%s' "$line" | sed -n "s/^'$decl' depends on axioms: \[\(.*\)\]$/\1/p" | tr -d ' ')"
        if [ -z "$got" ]; then
          echo "  FAIL  $decl: unrecognised lean output: $line" >&2
          failed=$((failed + 1))
          continue
        fi
      fi
      got_sorted="$(printf '%s' "$got" | tr ',' '\n' | sort | paste -sd, -)"
      want_sorted="$(printf '%s' "$want" | tr ',' '\n' | sort | paste -sd, -)"
      checked=$((checked + 1))
      if [ "$got_sorted" = "$want_sorted" ]; then
        echo "AXEYUM-LEAN-AXIOMS|$decl|lean=${got_sorted:-none}|ok|mathlib=$module"
      else
        echo "  FAIL  $decl: lean says [${got_sorted}], fact pins [${want_sorted}]" >&2
        failed=$((failed + 1))
      fi
    done
  fi
fi

echo "imported-fact-lean-axioms: $checked declaration(s) cross-checked against $LEAN, $failed failed"
# A gate that examined nothing is a failure, not a pass.
if [ "$checked" -eq 0 ]; then
  echo "imported-fact-lean-axioms: examined ZERO declarations" >&2
  exit 1
fi
exit $((failed == 0 ? 0 : 1))
