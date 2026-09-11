#!/usr/bin/env bash
# Positive control for the admission-limit basis check.
#
# `check-admission-limit-basis.py` normally exits 0, and exit 0 is exactly what
# a checker that CANNOT FIRE prints. The sibling staleness checker shipped with
# two defects of precisely that kind — a regex without `re.MULTILINE` that made
# the parser return zero entries, and a `sym(...)` pattern that did not survive
# rustfmt's trailing comma so every dated entry parsed with an EMPTY dependency
# list. Both printed a clean bill of health. Its control is what caught them,
# so this check ships with one too.
#
# Two independent things are controlled here:
#
#   A. THE REGISTRY DIRECTION — a deliberately broken registry must be caught,
#      once per `Basis` variant, so a single shared code path cannot be the only
#      reason any of them fires (steps 1-5).
#   B. THE CHECKER DIRECTION — each variant's guard is deleted from a scratch
#      copy of the checker in turn, and EXACTLY ONE of the four registry
#      mutants must stop being caught (step 6). A guard that can be removed with
#      every step still red is decoration; a deletion that kills more than one
#      step means the four variants are not independently tested.
#
# Step 2 is the real failure this check was built for, reproduced exactly:
# `MAX_PRE_SAT_ARITH_ATOMS`'s justification named BatSat's allocator, ADR-1703
# took BatSat off every shipping path, and nothing noticed for 28 days.
#
# Nothing here writes to the repository: every copy lives in a throwaway
# directory. Usage: scripts/tests/test-admission-limit-basis-control.sh
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CHECK="$ROOT/scripts/check-admission-limit-basis.py"
REGISTRY="$ROOT/crates/axeyum-solver/src/config_registry.rs"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/axeyum-admission-basis-control.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

fails=0
step() { printf '\n== %s\n' "$1"; }
ok()   { printf '   PASS: %s\n' "$1"; }
bad()  { printf '   FAIL: %s\n' "$1"; fails=$((fails + 1)); }

for f in "$CHECK" "$REGISTRY"; do
  if [ ! -f "$f" ]; then
    printf 'FAIL: missing %s\n' "$f"
    exit 2
  fi
done

# ---------------------------------------------------------------------------
# Build the four broken registries. Each replaces ONE basis declaration with a
# claim that is false about today's tree, and each exercises a DIFFERENT
# `Basis` variant.
#
# The anchors are the exact text of a live declaration, and the builder exits
# non-zero when an anchor is absent — so a registry edit that outdates this
# control is a loud failure and not a silently weaker control.
build_mutant() {  # $1 = out file, $2 = anchor, $3 = replacement
  python3 - "$REGISTRY" "$1" "$2" "$3" <<'PY'
import sys
src = open(sys.argv[1], encoding="utf-8").read()
anchor, repl = sys.argv[3], sys.argv[4]
if src.count(anchor) != 1:
    sys.exit(f"control could not be built: {anchor!r} occurs "
             f"{src.count(anchor)} time(s), expected exactly 1")
open(sys.argv[2], "w", encoding="utf-8").write(src.replace(anchor, repl, 1))
PY
}

# A `LiveSymbol` naming the type the warm SAT solver USED to hold. Until
# ADR-1703, `IncrementalSat` was `{ solver: IncrementalBatSat, .. }` — that
# field IS the allocator `MAX_PRE_SAT_ARITH_ATOMS`'s justification blamed for
# an 8 GiB abort. `IncrementalBatSat` now occurs nowhere in `crates/`.
#
# The identifier matters: a mutant naming the bare string `batsat` would NOT
# fire, because `crates/axeyum-cnf/src/lib.rs` still said "batsat" in prose even
# after the engine was gone. (The `#[cfg(feature = "batsat-reference")]`
# re-export that made this vivid was removed by ADR-1910; the prose mentions
# remain, which is exactly the point.) A basis has to name the thing whose
# disappearance IS the claim becoming false, not a word that happens to appear
# near it — and this control is what demonstrates the difference.
build_mutant "$WORK/live.rs" \
  'adr("ADR-1730")' \
  'live("IncrementalBatSat", "crates/axeyum-cnf/src/lib.rs")' \
  || { bad "could not build the LiveSymbol mutant"; }

# A `CommitSubject` whose cited commit no longer says what it was cited for.
build_mutant "$WORK/commit.rs" \
  'adr("ADR-1730")' \
  'commit("96ff85930", "a subject this commit has never had")' \
  || { bad "could not build the CommitSubject mutant"; }

# An `AdrLive` naming an ADR number that does not exist.
build_mutant "$WORK/adr.rs" \
  'adr("ADR-1730")' \
  'adr("ADR-9999")' \
  || { bad "could not build the AdrLive mutant"; }

# A `DocPath` naming a document that does not exist.
build_mutant "$WORK/doc.rs" \
  'adr("ADR-1730")' \
  'doc("docs/research/12-performance/no-such-note.md")' \
  || { bad "could not build the DocPath mutant"; }

# A control for the control: the same entry with its basis simply DELETED. It
# must exit 0 — which proves steps 2-5 fire because of the declaration's
# content and not merely because that entry is present.
build_mutant "$WORK/empty.rs" \
  '            &[adr("ADR-1730")],' \
  '            &[],' \
  || { bad "could not build the empty-basis mutant"; }

run() {  # $1 = registry, $2 = extra args...; echoes "<rc>|<output file>"
  local reg="$1"; shift
  local out="$WORK/out.$(basename "$reg").$$"
  python3 "$CHECK" --registry "$reg" "$@" >"$out" 2>&1
  echo "$?|$out"
}

# ---------------------------------------------------------------------------
step "1. the in-tree registry: every declared basis resolves"
r=$(run "$REGISTRY"); rc=${r%%|*}; out=${r#*|}
if [ "$rc" -eq 0 ]; then ok "exit 0"; else bad "expected exit 0, got $rc"; sed 's/^/     /' "$out"; fi

step "2. LiveSymbol — the retired IncrementalBatSat, the real 2026-09-05 failure"
r=$(run "$WORK/live.rs"); rc=${r%%|*}; out=${r#*|}
if [ "$rc" -eq 1 ]; then ok "exit 1"; else bad "expected exit 1, got $rc"; sed 's/^/     /' "$out"; fi
if grep -q 'IncrementalBatSat' "$out"; then ok "names the mechanism that is gone"; else bad "fired without naming IncrementalBatSat"; fi

step "3. CommitSubject — a cited commit whose subject no longer matches"
r=$(run "$WORK/commit.rs"); rc=${r%%|*}; out=${r#*|}
if [ "$rc" -eq 1 ]; then ok "exit 1"; else bad "expected exit 1, got $rc"; sed 's/^/     /' "$out"; fi

step "4. AdrLive — a bound resting on an ADR that does not exist"
r=$(run "$WORK/adr.rs"); rc=${r%%|*}; out=${r#*|}
if [ "$rc" -eq 1 ]; then ok "exit 1"; else bad "expected exit 1, got $rc"; sed 's/^/     /' "$out"; fi

step "5. DocPath — a measurement written up in a document that is gone"
r=$(run "$WORK/doc.rs"); rc=${r%%|*}; out=${r#*|}
if [ "$rc" -eq 1 ]; then ok "exit 1"; else bad "expected exit 1, got $rc"; sed 's/^/     /' "$out"; fi

step "5b. with the basis DELETED the same entry passes again"
r=$(run "$WORK/empty.rs"); rc=${r%%|*}; out=${r#*|}
if [ "$rc" -eq 0 ]; then
  ok "exit 0 — the declaration's CONTENT is what makes steps 2-5 fire"
else
  bad "expected exit 0 with no basis, got $rc"; sed 's/^/     /' "$out"
fi

# ---------------------------------------------------------------------------
# Delete one guard from the CHECKER and require that exactly one mutant stops
# being caught. Four guards, four mutants, one diagonal.
step "6. deleting one checker guard must un-catch EXACTLY ONE mutant"

declare -a GUARD_NAME=(AdrLive DocPath LiveSymbol CommitSubject)
# Defang one WHOLE branch of `check_basis` at a time by returning `None` as its
# first statement. Branch granularity, not statement granularity: an `AdrLive`
# mutant naming a MISSING ADR is reported by a different `return` from one
# naming a SUPERSEDED ADR, so deleting a single `return` would leave the branch
# still able to catch its own mutant and the diagonal would say nothing.
declare -a GUARD_FIND=(
  '    if kind == "AdrLive":'
  '    if kind == "DocPath":'
  '    if kind == "LiveSymbol":'
  '    if kind == "CommitSubject":'
)
declare -a MUTANT=("$WORK/adr.rs" "$WORK/doc.rs" "$WORK/live.rs" "$WORK/commit.rs")

for gi in 0 1 2 3; do
  defanged="$WORK/checker-${GUARD_NAME[$gi]}.py"
  python3 "$ROOT/scripts/tests/_defang_basis_branch.py" \
      "$CHECK" "$defanged" "${GUARD_FIND[$gi]}"
  if [ $? -ne 0 ]; then
    bad "could not defang the ${GUARD_NAME[$gi]} branch (anchor is stale)"
    continue
  fi
  uncaught=""
  n_uncaught=0
  for mi in 0 1 2 3; do
    python3 "$defanged" --repo "$ROOT" --registry "${MUTANT[$mi]}" >"$WORK/m.$gi.$mi" 2>&1
    mrc=$?
    if [ "$mrc" -eq 2 ]; then
      bad "defanged ${GUARD_NAME[$gi]} checker self-check-failed on the ${GUARD_NAME[$mi]} mutant"
      sed 's/^/     /' "$WORK/m.$gi.$mi"
      continue
    fi
    if [ "$mrc" -eq 0 ]; then
      n_uncaught=$((n_uncaught + 1))
      uncaught="$uncaught ${GUARD_NAME[$mi]}"
    fi
  done
  if [ "$n_uncaught" -eq 1 ] && [ "$uncaught" = " ${GUARD_NAME[$gi]}" ]; then
    ok "removing the ${GUARD_NAME[$gi]} branch un-catches exactly its own mutant"
  else
    bad "removing the ${GUARD_NAME[$gi]} branch un-catches $n_uncaught mutant(s):$uncaught (expected exactly ${GUARD_NAME[$gi]})"
  fi
done

# ---------------------------------------------------------------------------
step "7. the audit mode examines a nonzero population"
python3 "$CHECK" --audit >"$WORK/audit.out" 2>&1
arc=$?
if [ "$arc" -eq 2 ]; then
  bad "audit self-check failed (it examined nothing)"
  sed 's/^/     /' "$WORK/audit.out"
elif grep -qE 'audit: read the definition-site doc comment of [1-9][0-9]* of' "$WORK/audit.out"; then
  ok "audit reports a nonzero examined population (exit $arc)"
else
  bad "audit did not report how many doc comments it read"
  sed 's/^/     /' "$WORK/audit.out"
fi

printf '\n'
if [ "$fails" -eq 0 ]; then
  echo "ADMISSION_BASIS_CONTROL|PASSED"
  exit 0
fi
echo "ADMISSION_BASIS_CONTROL|FAILED|checks_failed=$fails"
exit 1
