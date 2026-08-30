#!/usr/bin/env bash
# Mutation table for scripts/credit-transaction-ledger.py (ADR-0810, the real
# ledger wiring of ADR-0785's two-phase-commit engine).
#
# CLAUDE.md's standing rule: "when you touch a checker, delete one guard and
# require that EXACTLY ONE test dies." This deletes nine guards THIS WRAPPER
# OWNS, one at a time, in a SCRATCH COPY (never the shared checkout -- see
# CLAUDE.md's "mutation testing in the shared worktree breaks other lanes'
# builds"), and requires each mutation to kill exactly one CANARY test from a
# fixed, disjoint set -- one canary per guard.
#
# This table does NOT re-verify guards already mutation-verified by
# scripts/tests/test-credit-transaction-mutations.sh for credit-transaction.py
# itself (fresh-read, and the four staleness checks' EXCEPTION CLASSES) --
# those are reused unmodified here. What IS new and owned by this wrapper:
# the four staleness CHECKS against the real dimensions (receipt/source/
# graph/checker), the two transaction-state preconditions, the corrupt-
# staging call site, the idempotent-replay short-circuit, and the
# content-rejection guard around validate-facts.py's validate_one.
#
# Two further defensive checks exist in credit-transaction-ledger.py
# (check-settled-fact-statements.py's rewrite() refusal, and
# gen-safety-matrix.py's run_controls() failure) but are NOT in this table:
# they guard THIRD-PARTY logic this wrapper reuses rather than reimplements,
# and constructing a fixture that makes those specific third-party checks
# fail (rather than validate_one, which is easy to trigger via a dangling
# depends_on) was judged not worth the scope for this lane. Named here
# rather than silently omitted.
#
# `__pycache__` is cleared before every run for the same reason the original
# table does (CLAUDE.md, "stale .pyc in mutation loops").
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/credit-txn-ledger-mutation-XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

mkdir -p "$SCRATCH/scripts/tests" "$SCRATCH/artifacts"
cp -r "$REPO_ROOT/scripts/." "$SCRATCH/scripts/"
cp -r "$REPO_ROOT/artifacts/facts" "$SCRATCH/artifacts/facts"
cp -r "$REPO_ROOT/artifacts/ontology" "$SCRATCH/artifacts/ontology"
cp -r "$REPO_ROOT/artifacts/safety-matrix" "$SCRATCH/artifacts/safety-matrix"

ENGINE="$SCRATCH/scripts/credit-transaction-ledger.py"
TESTFILE="$SCRATCH/scripts/tests/test-credit-transaction-ledger.py"

CANARIES=(
  "StalenessFixtureTests.test_stale_receipt_raises_only_stale_receipt_error"
  "StalenessFixtureTests.test_stale_source_raises_only_stale_source_error"
  "StalenessFixtureTests.test_stale_graph_raises_only_stale_graph_error"
  "StalenessFixtureTests.test_stale_checker_raises_only_stale_checker_error"
  "GuardBehaviorTests.test_commit_rejects_a_non_prepared_transaction"
  "GuardBehaviorTests.test_apply_rejects_an_uncommitted_transaction"
  "GuardBehaviorTests.test_apply_refuses_corrupted_staged_content"
  "GuardBehaviorTests.test_invalid_fact_content_is_rejected_before_any_txn_dir_exists"
  "IdempotenceTests.test_replay_is_idempotent"
)

clear_pycache() {
  find "$SCRATCH" -name '__pycache__' -exec rm -rf {} + 2>/dev/null || true
}

run_canaries() {
  clear_pycache
  ( cd "$SCRATCH" && python3 "$TESTFILE" -v "${CANARIES[@]}" ) > "$SCRATCH/run.log" 2>&1 || true
  return 0
}

failed_canaries_from_log() {
  local log="$1"
  local name
  for name in "${CANARIES[@]}"; do
    local method="${name##*.}"
    local line
    line="$(grep -E "^${method} \(" "$log" || true)"
    if [ -z "$line" ]; then
      echo "MISSING:${name}"
    elif echo "$line" | grep -qE '\.\.\. (FAIL|ERROR)$'; then
      echo "$name"
    fi
  done
}

echo "=== baseline (unmutated) ==="
run_canaries
baseline_failed="$(failed_canaries_from_log "$SCRATCH/run.log")"
if [ -n "$baseline_failed" ]; then
  echo "FATAL: baseline has failing canaries before any mutation:" >&2
  echo "$baseline_failed" >&2
  cat "$SCRATCH/run.log" >&2
  exit 1
fi
echo "baseline: all ${#CANARIES[@]} canaries pass"
echo

declare -a MUTATION_NAMES
declare -a MUTATION_OLD
declare -a MUTATION_NEW
declare -a MUTATION_EXPECT

add_mutation() {
  MUTATION_NAMES+=("$1")
  MUTATION_OLD+=("$2")
  MUTATION_NEW+=("$3")
  MUTATION_EXPECT+=("$4")
}

add_mutation "stale-receipt check removed" \
  '    if current_receipt_ptr != journal.inputs.receipt_pointer_sha256:  # GUARD: stale receipt' \
  '    if False:  # MUTATED: stale-receipt guard removed' \
  "StalenessFixtureTests.test_stale_receipt_raises_only_stale_receipt_error"

add_mutation "stale-source check removed" \
  '    if current_source != journal.inputs.source_sha256:  # GUARD: stale source' \
  '    if False:  # MUTATED: stale-source guard removed' \
  "StalenessFixtureTests.test_stale_source_raises_only_stale_source_error"

add_mutation "stale-graph check removed" \
  '    if current_graph != journal.inputs.graph_sha256:  # GUARD: stale graph' \
  '    if False:  # MUTATED: stale-graph guard removed' \
  "StalenessFixtureTests.test_stale_graph_raises_only_stale_graph_error"

add_mutation "stale-checker check removed" \
  '    if current_checker != journal.inputs.checker_version:  # GUARD: stale checker' \
  '    if False:  # MUTATED: stale-checker guard removed' \
  "StalenessFixtureTests.test_stale_checker_raises_only_stale_checker_error"

add_mutation "commit status precondition removed" \
  '    if journal.status != "prepared":  # GUARD: commit status precondition' \
  '    if False:  # MUTATED: commit status precondition removed' \
  "GuardBehaviorTests.test_commit_rejects_a_non_prepared_transaction"

add_mutation "apply status precondition removed" \
  '    if journal.status not in ("committed", "applied"):  # GUARD: apply status precondition' \
  '    if False:  # MUTATED: apply status precondition removed' \
  "GuardBehaviorTests.test_apply_rejects_an_uncommitted_transaction"

add_mutation "corrupt-staging integrity check removed" \
  '    ct._verify_staged_integrity(txn_dir, pending)  # GUARD: corrupt staging (reused from credit_transaction)' \
  '    pass  # MUTATED: corrupt-staging guard removed' \
  "GuardBehaviorTests.test_apply_refuses_corrupted_staged_content"

add_mutation "content-rejection guard removed (validate_one ignored)" \
  '    if errors:
        raise LedgerCascadeError(
            "validate-facts.py rejects the proposed fact: " + "; ".join(errors)
        )' \
  '    if False:  # MUTATED: content-rejection guard removed
        raise LedgerCascadeError(
            "validate-facts.py rejects the proposed fact: " + "; ".join(errors)
        )' \
  "GuardBehaviorTests.test_invalid_fact_content_is_rejected_before_any_txn_dir_exists"

add_mutation "idempotent-replay short-circuit removed" \
  '    if registry.get(fact_id) == receipt_sha:  # GUARD: idempotent replay' \
  '    if False:  # MUTATED: idempotent-replay guard removed' \
  "IdempotenceTests.test_replay_is_idempotent"

fail=0
n="${#MUTATION_NAMES[@]}"
for ((i = 0; i < n; i++)); do
  name="${MUTATION_NAMES[$i]}"
  old="${MUTATION_OLD[$i]}"
  new="${MUTATION_NEW[$i]}"
  expect="${MUTATION_EXPECT[$i]}"

  cp "$REPO_ROOT/scripts/credit-transaction-ledger.py" "$ENGINE"
  count_before="$(python3 - "$ENGINE" "$old" <<'PYEOF'
import sys
path, old = sys.argv[1], sys.argv[2]
text = open(path).read()
print(text.count(old))
PYEOF
)"
  if [ "$count_before" -ne 1 ]; then
    echo "FATAL: mutation anchor for '$name' matched $count_before times (need exactly 1)" >&2
    exit 1
  fi
  python3 - "$ENGINE" "$old" "$new" <<'PYEOF'
import sys
path, old, new = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(path).read()
assert text.count(old) == 1, (path, old)
open(path, "w").write(text.replace(old, new, 1))
PYEOF

  run_canaries
  failed="$(failed_canaries_from_log "$SCRATCH/run.log")"
  failed_count=0
  [ -n "$failed" ] && failed_count="$(echo "$failed" | grep -c . || true)"

  if [ "$failed_count" -eq 1 ] && [ "$failed" = "$expect" ]; then
    echo "OK   $name -> killed exactly: $expect"
  else
    fail=1
    echo "FAIL $name -> expected exactly [$expect], got:" >&2
    if [ -z "$failed" ]; then
      echo "  (nothing died -- guard is unreachable/decorative)" >&2
    else
      printf '  %s\n' "$failed" >&2
    fi
  fi

  cp "$REPO_ROOT/scripts/credit-transaction-ledger.py" "$ENGINE"
done

echo
if [ "$fail" -ne 0 ]; then
  echo "MUTATION TABLE: FAILED -- see above" >&2
  exit 1
fi
echo "MUTATION TABLE: all ${n} guards each killed exactly their own canary"
