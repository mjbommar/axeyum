#!/usr/bin/env bash
# Exercise the first fresh-candidate admission contract and its leakage controls.
set -euo pipefail

cd "$(dirname "$0")/.."

audit=(cargo run -q -p axeyum-lean-kernel --example theorem_knowledge_audit --)
common=(
  Autogenesis.Control.consequent
  --same-type-as Nat.mul_one
  --require Autogenesis.Control.premise
  --deny Nat.zero_add
  --deny Nat.mul_one
  --expect-axiom-free
)

positive="$("${audit[@]}" "${common[@]}" --fixture chain-clean)"
grep -qE \
  '^KNOWLEDGE_AUDIT\|root=Autogenesis.Control.consequent\|closure=[0-9]+\|required=1\|denied=2\|trusted=0\|same_type=true\|canonical_type=true$' \
  <<<"$positive"

expect_rejection() {
  local fixture="$1" output
  if output="$("${audit[@]}" "${common[@]}" --fixture "$fixture" 2>&1)"; then
    echo "knowledge control unexpectedly passed: $fixture" >&2
    echo "$output" >&2
    return 1
  fi
  grep -qF \
    'KNOWLEDGE_AUDIT_ERROR|forbidden dependencies reached transitively: Nat.mul_one' \
    <<<"$output"
}

expect_rejection chain-direct-leak
expect_rejection chain-indirect-leak

if premise_leak="$("${audit[@]}" "${common[@]}" --fixture chain-premise-leak 2>&1)"; then
  echo "knowledge control unexpectedly passed: chain-premise-leak" >&2
  echo "$premise_leak" >&2
  exit 1
fi
grep -qF \
  'KNOWLEDGE_AUDIT_ERROR|forbidden dependencies reached transitively: Nat.zero_add' \
  <<<"$premise_leak"

echo "AUTOGENESIS_KNOWLEDGE_CONTROLS|chain=pass|premise_leak=reject|direct_leak=reject|indirect_leak=reject"
