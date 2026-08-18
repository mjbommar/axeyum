#!/usr/bin/env bash
# Fixed-budget pre-A failure / post-B success through a catalog-only proposer.
set -euo pipefail

cd "$(dirname "$0")/.."
retain=
if [ "$#" -gt 0 ]; then
  [ "$#" -eq 2 ] && [ "$1" = "--retain" ] || {
    echo "usage: $0 [--retain NEW-DIRECTORY]" >&2
    exit 2
  }
  retain=$(realpath -m "$2")
fi
if [ -n "$retain" ]; then
  repo=$(git rev-parse --show-toplevel)
  case "$retain/" in
    "$repo/"*)
      echo "retained experiments belong outside the repository: $retain" >&2
      exit 1
      ;;
  esac
  [ ! -e "$retain" ] || {
    echo "refusing to overwrite retained experiment: $retain" >&2
    exit 1
  }
  [ -z "$(git status --porcelain)" ] || {
    echo "retained experiments require a clean Git checkout" >&2
    exit 1
  }
  mkdir -p "$(dirname "$retain")"
  scratch=$(mktemp -d "$(dirname "$retain")/.axeyum-autogenesis-apply.XXXXXX")
  trap 'rm -r "$scratch"' EXIT
  python3 scripts/gen-autogenesis-baseline.py \
    --capture "$scratch/baseline-execution.json" >/dev/null
else
  scratch=$(mktemp -d /tmp/axeyum-autogenesis-apply.XXXXXX)
  trap 'rm -r "$scratch"' EXIT
fi
budget=20
premise_budget=2

python3 scripts/create-autogenesis-snapshot.py \
  --premise F:nat-zero-add \
  --consequent F:nat-mul-one \
  --output "$scratch/snapshot.json" >/dev/null

mkdir "$scratch/pre_a-output"
python3 scripts/create-autogenesis-proposer-catalog.py \
  --snapshot "$scratch/snapshot.json" \
  --phase pre_a \
  --output "$scratch/pre_a-catalog.json" >/dev/null
scripts/run-autogenesis-python-proposer.sh \
  --snapshot "$scratch/snapshot.json" \
  --catalog "$scratch/pre_a-catalog.json" \
  --output-dir "$scratch/pre_a-output" \
  --program scripts/autogenesis-apply-proposer.py >/dev/null
python3 scripts/verify-autogenesis-apply-proposals.py \
  --catalog "$scratch/pre_a-catalog.json" \
  --bundle "$scratch/pre_a-output/apply-plans.json" \
  --tsv "$scratch/pre_a-output/apply-plans.tsv" >/dev/null

scripts/stage-autogenesis-premise.sh \
  --snapshot "$scratch/snapshot.json" \
  --output-dir "$scratch" \
  --budget "$premise_budget" >/dev/null
python3 scripts/prepare-autogenesis-fact-transaction.py \
  --fact scripts/tests/fixtures/F-nat-zero-add-open.json \
  --bundle "$scratch" \
  --output "$scratch/fact-transaction-proposal.json" >/dev/null
python3 scripts/prepare-autogenesis-fact-transaction.py \
  --fact scripts/tests/fixtures/F-nat-zero-add-open.json \
  --bundle "$scratch" \
  --verify "$scratch/fact-transaction-proposal.json" >/dev/null
if python3 scripts/prepare-autogenesis-fact-transaction.py \
  --fact artifacts/facts/F-nat-zero-add.json \
  --bundle "$scratch" \
  --output "$scratch/invalid-settled-transaction.json" \
  >"$scratch/invalid-settled-transaction.stdout" \
  2>"$scratch/invalid-settled-transaction.stderr"; then
  echo "transaction proposal unexpectedly accepted a settled fact" >&2
  exit 1
fi
grep -qF 'fact precondition is not open' \
  "$scratch/invalid-settled-transaction.stderr"
if python3 scripts/prepare-autogenesis-fact-transaction.py \
  --fact artifacts/facts/F-no-integer-square-is-minus-one.json \
  --bundle "$scratch" \
  --output "$scratch/invalid-wrong-fact-transaction.json" \
  >"$scratch/invalid-wrong-fact-transaction.stdout" \
  2>"$scratch/invalid-wrong-fact-transaction.stderr"; then
  echo "transaction proposal unexpectedly applied B evidence to another open fact" >&2
  exit 1
fi
grep -qF 'typed evidence names a different fact' \
  "$scratch/invalid-wrong-fact-transaction.stderr"

transition_chain=(
  --premise-evidence "$scratch/premise-evidence.json"
  --premise-transition "$scratch/premise-transition.json"
  --accepted-transition-event "$scratch/premise-accepted-event.json"
)
if python3 scripts/create-autogenesis-proposer-catalog.py \
  --snapshot "$scratch/snapshot.json" \
  --phase post_b \
  --output "$scratch/unauthorized-post_b-catalog.json" \
  >"$scratch/unauthorized-post_b.stdout" \
  2>"$scratch/unauthorized-post_b.stderr"; then
  echo "post-B catalog unexpectedly opened without an accepted event" >&2
  exit 1
fi
grep -qF 'post_b requires premise evidence, transition, and accepted event' \
  "$scratch/unauthorized-post_b.stderr"
mkdir "$scratch/post_b-output"
python3 scripts/create-autogenesis-proposer-catalog.py \
  --snapshot "$scratch/snapshot.json" \
  --phase post_b \
  "${transition_chain[@]}" \
  --output "$scratch/post_b-catalog.json" >/dev/null
scripts/run-autogenesis-python-proposer.sh \
  --snapshot "$scratch/snapshot.json" \
  --catalog "$scratch/post_b-catalog.json" \
  --output-dir "$scratch/post_b-output" \
  --program scripts/autogenesis-apply-proposer.py \
  "${transition_chain[@]}" >/dev/null
python3 scripts/verify-autogenesis-apply-proposals.py \
  --catalog "$scratch/post_b-catalog.json" \
  --bundle "$scratch/post_b-output/apply-plans.json" \
  --tsv "$scratch/post_b-output/apply-plans.tsv" >/dev/null

read -r pre_bundle pre_catalog pre_candidate < <(
  python3 - "$scratch" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
catalog = json.load(open(root / "pre_a-catalog.json"))
bundle = json.load(open(root / "pre_a-output/apply-plans.json"))
print(bundle["bundle_sha256"], catalog["catalog_sha256"], catalog["target"]["name"])
PY
)
read -r post_bundle post_catalog post_candidate premise_candidate < <(
  python3 - "$scratch" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
catalog = json.load(open(root / "post_b-catalog.json"))
bundle = json.load(open(root / "post_b-output/apply-plans.json"))
premise = next(entry["name"] for entry in catalog["entries"] if entry["origin"] == "accepted-episode")
print(bundle["bundle_sha256"], catalog["catalog_sha256"], catalog["target"]["name"], premise)
PY
)
read -r premise_bundle premise_catalog premise_target < <(
  python3 - "$scratch" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
catalog = json.load(open(root / "pre_b-catalog.json"))
bundle = json.load(open(root / "pre_b-induction-output/induction-plans.json"))
print(bundle["bundle_sha256"], catalog["catalog_sha256"], catalog["target"]["name"])
PY
)
[ "$premise_target" = "$premise_candidate" ] || {
  echo "post-B catalog premise identity disagrees with the pre-B target" >&2
  exit 1
}

premise_result=$(<"$scratch/premise-result.txt")
grep -qxF \
  "AUTOGENESIS_INDUCTION_RESULT|phase=pre_b|attempted=2|budget=$premise_budget|outcome=proved|plan_rank=2" \
  <<<"$premise_result"

pre_result=$(cargo run -q -p axeyum-lean-kernel \
  --example autogenesis_apply_plan_check -- \
  --plans "$scratch/pre_a-output/apply-plans.tsv" \
  --phase pre_a \
  --candidate "$pre_candidate" \
  --budget "$budget" \
  --expect no-proof \
  --bundle-sha256 "$pre_bundle" \
  --catalog-sha256 "$pre_catalog")
grep -qxF \
  "AUTOGENESIS_APPLY_RESULT|phase=pre_a|premise_attempted=0|premise_plan_rank=-|attempted=20|budget=$budget|outcome=no-proof|theorem=-" \
  <<<"$pre_result"

post_result=$(cargo run -q -p axeyum-lean-kernel \
  --example autogenesis_apply_plan_check -- \
  --plans "$scratch/post_b-output/apply-plans.tsv" \
  --phase post_b \
  --candidate "$post_candidate" \
  --premise-candidate "$premise_candidate" \
  --premise-plans "$scratch/pre_b-induction-output/induction-plans.tsv" \
  --premise-budget "$premise_budget" \
  --premise-bundle-sha256 "$premise_bundle" \
  --premise-catalog-sha256 "$premise_catalog" \
  --budget "$budget" \
  --expect proved \
  --bundle-sha256 "$post_bundle" \
  --catalog-sha256 "$post_catalog")
grep -qxF \
  "AUTOGENESIS_APPLY_RESULT|phase=post_b|premise_attempted=2|premise_plan_rank=2|attempted=1|budget=$budget|outcome=proved|theorem=$premise_candidate" \
  <<<"$post_result"

if cargo run -q -p axeyum-lean-kernel \
  --example autogenesis_apply_plan_check -- \
  --plans "$scratch/pre_a-output/apply-plans.tsv" \
  --phase pre_a \
  --candidate "$pre_candidate" \
  --budget "$budget" \
  --expect proved \
  --bundle-sha256 "$pre_bundle" \
  --catalog-sha256 "$pre_catalog" \
  >"$scratch/wrong-expect.stdout" 2>"$scratch/wrong-expect.stderr"; then
  echo "pre-A no-proof result unexpectedly satisfied --expect proved" >&2
  exit 1
fi
grep -qF 'AUTOGENESIS_APPLY_ERROR|observed outcome differs from --expect' \
  "$scratch/wrong-expect.stderr"

if [ -n "$retain" ]; then
  python3 - "$scratch" "$budget" "$premise_budget" "$premise_result" "$pre_result" "$post_result" <<'PY'
import hashlib
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
budget = int(sys.argv[2])
premise_budget = int(sys.argv[3])
baseline = json.load(open(root / "baseline-execution.json"))
snapshot = json.load(open(root / "snapshot.json"))
pre_catalog = json.load(open(root / "pre_a-catalog.json"))
post_catalog = json.load(open(root / "post_b-catalog.json"))
pre_bundle = json.load(open(root / "pre_a-output/apply-plans.json"))
post_bundle = json.load(open(root / "post_b-output/apply-plans.json"))
premise_catalog = json.load(open(root / "pre_b-catalog.json"))
premise_bundle = json.load(open(root / "pre_b-induction-output/induction-plans.json"))
premise_evidence = json.load(open(root / "premise-evidence.json"))
premise_transition = json.load(open(root / "premise-transition.json"))
premise_event = json.load(open(root / "premise-accepted-event.json"))
fact_transaction = json.load(open(root / "fact-transaction-proposal.json"))
report = {
    "schema_version": 6,
    "kind": "axeyum-autogenesis-apply-experiment",
    "git_commit": baseline["git_commit"],
    "baseline_source_sha256": baseline["baseline_source_sha256"],
    "snapshot_sha256": snapshot["snapshot_sha256"],
    "episode_id": snapshot["episode_id"],
    "target_fact_id": snapshot["chain"]["consequent"]["fact_id"],
    "premise_fact_id": snapshot["chain"]["premise"]["fact_id"],
    "budget": budget,
    "premise": {
        "budget": premise_budget,
        "catalog_sha256": premise_catalog["catalog_sha256"],
        "bundle_sha256": premise_bundle["bundle_sha256"],
        "accepted_plan_rank": 2,
        "evidence_sha256": premise_evidence["evidence_sha256"],
        "transition_sha256": premise_transition["transition_sha256"],
        "accepted_event_sha256": premise_event["event_sha256"],
        "fact_transaction_sha256": fact_transaction["transaction_sha256"],
        "fact_transaction_source_authoritative": fact_transaction["precondition"]["source_is_authoritative"],
        "result": sys.argv[4],
    },
    "pre_a": {
        "catalog_sha256": pre_catalog["catalog_sha256"],
        "bundle_sha256": pre_bundle["bundle_sha256"],
        "result": sys.argv[5],
    },
    "post_b": {
        "catalog_sha256": post_catalog["catalog_sha256"],
        "bundle_sha256": post_bundle["bundle_sha256"],
        "result": sys.argv[6],
    },
    "same_target": pre_catalog["target"] == post_catalog["target"],
    "controls": {
        "denied_retained_answers": snapshot["withheld"]["retained_theorems"],
        "expected_outcome_mismatch_rejected": True,
        "proposer_isolated": True,
    },
}
payload = json.dumps(report, sort_keys=True, separators=(",", ":")).encode()
report["experiment_sha256"] = hashlib.sha256(payload).hexdigest()
(root / "experiment.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
PY
  mv "$scratch" "$retain"
  trap - EXIT
fi

echo "AUTOGENESIS_APPLY_SEARCH|premise=B:proved+accepted-event|transaction=prepared-fixture|target=A|budget=$budget|pre_a=no-proof|post_b=proved|readiness=event-driven|dependency=episode-premise|ledger_writes=0"
