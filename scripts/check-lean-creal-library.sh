#!/usr/bin/env bash
# The `lean/axeyum-creal` gate: regenerate the published Lean library from the
# live kernel, fail on drift, build it with the PINNED toolchain, and enforce
# floors on what the run actually did.
#
# Why each step, rather than just `lake build && echo ok`:
#
#   1. DRIFT. The package is generated from `Kernel::add_declaration`'s
#      environment. If the committed `.lean` is not what the kernel renders
#      today, then the library is a claim ABOUT the kernel rather than a
#      projection OF it, and a green `lake build` says nothing about the
#      mathematics this repository proved. So the generator runs in `--check`
#      mode first and a byte difference is a failure.
#   2. THE PIN. Resolved by delegating to `scripts/check-lean-gate.sh
#      --print-toolchain` -- one implementation of that policy -- and the
#      binary is PRINTED (`AXEYUM-LEAN-TOOLCHAIN`), because "Lean accepted it"
#      is not a claim until you can say which Lean.
#   3. COUNTS, with floors. `lake build` exiting 0 cannot distinguish "Lean's
#      kernel checked 3,617 declarations" from "the library target has no
#      roots" from "everything was cached". This repository has shipped all
#      three shapes of green-looking gate. So the counts are read back from the
#      ARTEFACT (declaration heads in the committed source) and from Lean's own
#      output, and each carries a floor.
#   4. THE AXIOM AUDIT, with a positive control. `Axeyum/Creal/Axioms.lean`
#      prints one `#print axioms` line per result the fact ledger credits; all
#      of them must read `does not depend on any axioms`. That assertion alone
#      is consistent with `#print axioms` having stopped traversing, so
#      `Tests/AxiomControl.lean` rests on a declared axiom and its line MUST
#      name that axiom. Without the control the audit could not fail.
#
# `#guard_msgs` is deliberately not used and cannot be: it lives in
# `Lean.Elab`, unreachable from a `prelude` module, and `prelude` is forced by
# the development declaring its own `Eq`/`And`/`Or`/`Exists`. Measured on the
# pin: `#guard_msgs` in a `prelude` module is a parse error. The assertion it
# would have made is made here instead, over Lean's own output, with a control.
#
# Usage:
#   scripts/check-lean-creal-library.sh            # everything (minutes)
#   scripts/check-lean-creal-library.sh --slice    # no `lake build`; the
#                                                  # push-hook path
#   AXEYUM_ALLOW_NO_LEAN=1 scripts/check-lean-creal-library.sh  # loud SKIP
#   AXEYUM_LEAN_ALLOW_UNPINNED=1 ...                            # stated deviation
#
# ADR-1675.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

PACKAGE_DIR="lean/axeyum-creal"
CARRIER="$PACKAGE_DIR/Axeyum/Creal/Carrier.lean"
MANIFEST="$PACKAGE_DIR/MANIFEST.json"
EXCLUSIONS="$PACKAGE_DIR/EXCLUSIONS.json"

# Floors and ceilings, measured 2026-09-05 on leanprover/lean4:v4.34.0-rc1.
#
# COMMAND_FLOOR is the independent-replay census's own number (ADR-1661,
# `artifacts/measurements/lean-replay-census-2026-09-05.md`): pinned Lean's
# KERNEL accepts 3,542 of `creal`'s 3,617 declarations over the `lean4export`
# wire. The source route must carry at least that many, and in fact carries
# more, because a `Type`-valued proof that the wire format cannot describe as a
# theorem is an ordinary `def` in Lean source.
#
# EXCLUSION_CEILING is today's measured value. Raising it needs a reason in the
# commit message; a declaration that stops being published is a regression.
COMMAND_FLOOR=3542
EXCLUSION_CEILING=0
AUDIT_FLOOR=400
CONTROL_FLOOR=1

SLICE=0
for arg in "$@"; do
  case "$arg" in
    --slice) SLICE=1 ;;
    *) echo "check-lean-creal-library: unknown argument $arg" >&2; exit 2 ;;
  esac
done

fail() { echo "check-lean-creal-library: FAILED -- $*" >&2; exit 1; }

# ---------------------------------------------------------------------------
# 1. The package must exist before anything is claimed about it.
# ---------------------------------------------------------------------------
[ -f "$CARRIER" ] || fail "no $CARRIER. The package is generated; run
  cargo run --release -p axeyum-lean-kernel --example render_creal_library"
[ -f "$MANIFEST" ] || fail "no $MANIFEST"
[ -f "$EXCLUSIONS" ] || fail "no $EXCLUSIONS"

# ---------------------------------------------------------------------------
# 2. Counts read back from the ARTEFACT, not from the manifest that asserts
#    them. A declaration head is a top-level `def`/`theorem`/`opaque`/`axiom`/
#    `inductive` at column zero; the module writer indents everything else.
# ---------------------------------------------------------------------------
commands=$(grep -c -E '^(def|theorem|opaque|axiom|inductive) ' "$CARRIER")
if [ "$commands" -lt "$COMMAND_FLOOR" ]; then
  fail "$CARRIER carries $commands Lean commands, floor is $COMMAND_FLOOR
  (the replay census's kernel-accepted count over the same carrier)."
fi

manifest_commands=$(sed -n 's/.*"lean_commands": \([0-9]*\).*/\1/p' "$MANIFEST")
if [ "$manifest_commands" != "$commands" ]; then
  fail "the manifest says $manifest_commands Lean commands but the source carries $commands.
  One of them is stale; regenerate the package."
fi

exclusions=$(sed -n 's/.*"count": \([0-9]*\).*/\1/p' "$EXCLUSIONS")
if [ -z "$exclusions" ]; then
  fail "$EXCLUSIONS has no \"count\" field"
fi
if [ "$exclusions" -gt "$EXCLUSION_CEILING" ]; then
  fail "$exclusions declarations are excluded from the published package, ceiling is
  $EXCLUSION_CEILING. Every exclusion is named in $EXCLUSIONS. A declaration that
  stops being published is a regression, not a rounding."
fi

audit=$(grep -c '^#print axioms ' "$PACKAGE_DIR/Axeyum/Creal/Axioms.lean")
if [ "$audit" -lt "$AUDIT_FLOOR" ]; then
  fail "the axiom audit runs $audit \`#print axioms\` commands, floor is $AUDIT_FLOOR.
  An audit over nothing passes over nothing."
fi

echo "check-lean-creal-library: artefact commands=$commands exclusions=$exclusions audit=$audit"

# ---------------------------------------------------------------------------
# 3. Drift. The generator is the authority; the committed package is a cache.
# ---------------------------------------------------------------------------
if [ -x scripts/cargo-serialized.sh ]; then
  cargo_runner="scripts/cargo-serialized.sh"
else
  cargo_runner="cargo"
fi
echo "check-lean-creal-library: regenerating and diffing ($cargo_runner)"
if ! "$cargo_runner" run --release -q -p axeyum-lean-kernel \
    --example render_creal_library -- --check; then
  fail "the committed package is not what the kernel renders today (see above)."
fi

# ---------------------------------------------------------------------------
# 4. The toolchain.
# ---------------------------------------------------------------------------
toolchain_report=$(scripts/check-lean-gate.sh --print-toolchain 2>&1)
toolchain_status=$?
lean_bin=$(printf '%s\n' "$toolchain_report" | sed -n 's/^bin=//p')
lean_version=$(printf '%s\n' "$toolchain_report" | sed -n 's/^version=//p')
lean_pin=$(printf '%s\n' "$toolchain_report" | sed -n 's/^pin=//p')
if [ "$toolchain_status" -ne 0 ] || [ -z "$lean_bin" ] || [ ! -x "$lean_bin" ]; then
  if [ "${AXEYUM_ALLOW_NO_LEAN:-}" = "1" ]; then
    echo "check-lean-creal-library: SKIPPED -- 0 declarations were checked by Lean." \
         "This is NOT a pass; AXEYUM_ALLOW_NO_LEAN=1 was set." >&2
    exit 0
  fi
  echo "check-lean-creal-library: FAILED -- could not resolve the pinned Lean:" >&2
  printf '%s\n' "$toolchain_report" >&2
  exit 1
fi

package_pin=$(tr -d '[:space:]' <"$PACKAGE_DIR/lean-toolchain" 2>/dev/null)
if [ "$package_pin" != "$lean_pin" ]; then
  fail "$PACKAGE_DIR/lean-toolchain says '$package_pin' but the repository pin is
  '$lean_pin'. A green run under a different Lean says nothing about the one
  everything else uses."
fi
echo "AXEYUM-LEAN-TOOLCHAIN lean-creal-library bin=$lean_bin version=$lean_version"

if [ "$SLICE" -eq 1 ]; then
  echo "check-lean-creal-library: --slice -- drift, pin and counts checked;" \
       "\`lake build\` NOT run. That is the full gate (\`just check\`)."
  exit 0
fi

lake_bin="$(dirname "$lean_bin")/lake"
[ -x "$lake_bin" ] || fail "no \`lake\` beside the resolved Lean ($lake_bin)."

# ---------------------------------------------------------------------------
# 5. Build, and read Lean's own output. `.lake` is deleted for the audit
#    targets so the `#print axioms` lines come from THIS run: Lake is correct
#    about staleness but silent about it, and a cached module prints nothing.
# ---------------------------------------------------------------------------
rm -rf "$PACKAGE_DIR/.lake/build/lib/lean/Axeyum/Creal/Axioms.olean" \
       "$PACKAGE_DIR/.lake/build/lib/lean/Tests" \
       "$PACKAGE_DIR/.lake/build/ir/Tests"
build_log=$(mktemp "${TMPDIR:-/tmp}/axeyum-creal-lake.XXXXXX")
trap 'rm -f "$build_log"' EXIT
started=$(date +%s)
( cd "$PACKAGE_DIR" && "$lake_bin" build Axeyum Audit Tests ) >"$build_log" 2>&1
build_status=$?
elapsed=$(( $(date +%s) - started ))
if [ "$build_status" -ne 0 ]; then
  echo "check-lean-creal-library: FAILED -- \`lake build\` exited $build_status after ${elapsed}s:" >&2
  tail -80 "$build_log" >&2
  exit 1
fi
echo "check-lean-creal-library: lake build OK in ${elapsed}s"

# ---------------------------------------------------------------------------
# 6. The axiom audit, over Lean's own output.
# ---------------------------------------------------------------------------
clean=$(grep -c "does not depend on any axioms" "$build_log")
dirty=$(grep -c "depends on axioms" "$build_log")

if [ "$clean" -lt "$AUDIT_FLOOR" ]; then
  echo "check-lean-creal-library: FAILED -- Lean reported $clean axiom-free results," \
       "floor is $AUDIT_FLOOR. The build printed:" >&2
  tail -40 "$build_log" >&2
  exit 1
fi

# The positive control is the ONLY line allowed to name an axiom, and it must
# be there: without it, a `#print axioms` that had stopped traversing would
# report every result clean and this gate would pass on nothing.
control=$(grep -c "axeyumCrealAudit_control.*depends on axioms.*axeyumCrealAudit_controlAxiom" "$build_log")
if [ "$control" -lt "$CONTROL_FLOOR" ]; then
  echo "check-lean-creal-library: FAILED -- the positive control did not report its axiom." \
       "\`#print axioms\` may not be traversing imported proofs, in which case the" \
       "$clean clean results above mean nothing." >&2
  grep -n "axeyumCrealAudit" "$build_log" >&2 || echo "  (no control line at all)" >&2
  exit 1
fi

if [ "$dirty" -ne "$control" ]; then
  echo "check-lean-creal-library: FAILED -- $dirty results depend on axioms but only" \
       "$control of them is the positive control. The published library is not axiom-free:" >&2
  grep -n "depends on axioms" "$build_log" | grep -v axeyumCrealAudit_control >&2
  exit 1
fi

echo "check-lean-creal-library: PASSED -- $commands declarations published as Lean" \
     "commands and accepted by $lean_pin; $exclusions exclusions; $clean results" \
     "axiom-free by \`#print axioms\` with $control positive control(s); ${elapsed}s."
