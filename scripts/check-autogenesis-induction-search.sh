#!/usr/bin/env bash
# Produce B from a catalog-only structural-plan search and a fresh kernel check.
set -euo pipefail

cd "$(dirname "$0")/.."
scratch=$(mktemp -d /tmp/axeyum-autogenesis-induction.XXXXXX)
trap 'rm -r "$scratch"' EXIT
budget=2

cargo test -q -p axeyum-lean-kernel --example autogenesis_induction_plan_check

python3 scripts/create-autogenesis-snapshot.py \
  --premise F:nat-zero-add \
  --consequent F:nat-mul-one \
  --output "$scratch/snapshot.json" >/dev/null
python3 scripts/create-autogenesis-proposer-catalog.py \
  --snapshot "$scratch/snapshot.json" \
  --phase pre_b \
  --output "$scratch/catalog.json" >/dev/null
mkdir "$scratch/output"
scripts/run-autogenesis-python-proposer.sh \
  --snapshot "$scratch/snapshot.json" \
  --catalog "$scratch/catalog.json" \
  --output-dir "$scratch/output" \
  --program scripts/autogenesis-induction-proposer.py >/dev/null
python3 scripts/verify-autogenesis-induction-proposals.py \
  --catalog "$scratch/catalog.json" \
  --bundle "$scratch/output/induction-plans.json" \
  --tsv "$scratch/output/induction-plans.tsv" >/dev/null

read -r bundle catalog candidate < <(
  python3 - "$scratch" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
catalog = json.load(open(root / "catalog.json"))
bundle = json.load(open(root / "output/induction-plans.json"))
print(bundle["bundle_sha256"], catalog["catalog_sha256"], catalog["target"]["name"])
PY
)

result=$(cargo run -q -p axeyum-lean-kernel \
  --example autogenesis_induction_plan_check -- \
  --plans "$scratch/output/induction-plans.tsv" \
  --candidate "$candidate" \
  --budget "$budget" \
  --expect proved \
  --bundle-sha256 "$bundle" \
  --catalog-sha256 "$catalog" \
  --evidence-output "$scratch/kernel-evidence.tsv")
grep -qxF \
  "AUTOGENESIS_INDUCTION_RESULT|phase=pre_b|attempted=2|budget=$budget|outcome=proved|plan_rank=2" \
  <<<"$result"
python3 scripts/create-autogenesis-premise-evidence.py \
  --snapshot "$scratch/snapshot.json" \
  --catalog "$scratch/catalog.json" \
  --bundle "$scratch/output/induction-plans.json" \
  --plans "$scratch/output/induction-plans.tsv" \
  --kernel-evidence "$scratch/kernel-evidence.tsv" \
  --output "$scratch/premise-evidence.json" >/dev/null
python3 scripts/create-autogenesis-premise-evidence.py \
  --snapshot "$scratch/snapshot.json" \
  --catalog "$scratch/catalog.json" \
  --bundle "$scratch/output/induction-plans.json" \
  --plans "$scratch/output/induction-plans.tsv" \
  --kernel-evidence "$scratch/kernel-evidence.tsv" \
  --verify "$scratch/premise-evidence.json" >/dev/null

first_result=$(cargo run -q -p axeyum-lean-kernel \
  --example autogenesis_induction_plan_check -- \
  --plans "$scratch/output/induction-plans.tsv" \
  --candidate "$candidate" \
  --budget 1 \
  --expect no-proof \
  --bundle-sha256 "$bundle" \
  --catalog-sha256 "$catalog")
grep -qxF \
  'AUTOGENESIS_INDUCTION_RESULT|phase=pre_b|attempted=1|budget=1|outcome=no-proof|plan_rank=-' \
  <<<"$first_result"

if cargo run -q -p axeyum-lean-kernel \
  --example autogenesis_induction_plan_check -- \
  --plans "$scratch/output/induction-plans.tsv" \
  --candidate "$candidate" \
  --budget 1 \
  --expect proved \
  --bundle-sha256 "$bundle" \
  --catalog-sha256 "$catalog" \
  >"$scratch/wrong-expect.stdout" 2>"$scratch/wrong-expect.stderr"; then
  echo "the invalid first induction plan unexpectedly satisfied --expect proved" >&2
  exit 1
fi
grep -qF 'AUTOGENESIS_INDUCTION_ERROR|observed outcome differs from --expect' \
  "$scratch/wrong-expect.stderr"

echo "AUTOGENESIS_INDUCTION_SEARCH|target=B|budget=$budget|plan_rank=2|outcome=proved|typed_evidence=verified|axioms=0|retained_answers=0"
