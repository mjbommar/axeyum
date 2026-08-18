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

python3 scripts/create-autogenesis-snapshot.py \
  --premise F:nat-zero-add \
  --consequent F:nat-mul-one \
  --output "$scratch/snapshot.json" >/dev/null

for phase in pre_a post_b; do
  mkdir "$scratch/$phase-output"
  python3 scripts/create-autogenesis-proposer-catalog.py \
    --snapshot "$scratch/snapshot.json" \
    --phase "$phase" \
    --output "$scratch/$phase-catalog.json" >/dev/null
  scripts/run-autogenesis-python-proposer.sh \
    --snapshot "$scratch/snapshot.json" \
    --catalog "$scratch/$phase-catalog.json" \
    --output-dir "$scratch/$phase-output" \
    --program scripts/autogenesis-apply-proposer.py >/dev/null
  python3 scripts/verify-autogenesis-apply-proposals.py \
    --catalog "$scratch/$phase-catalog.json" \
    --bundle "$scratch/$phase-output/apply-plans.json" \
    --tsv "$scratch/$phase-output/apply-plans.tsv" >/dev/null
done

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
  "AUTOGENESIS_APPLY_RESULT|phase=pre_a|attempted=20|budget=$budget|outcome=no-proof|theorem=-" \
  <<<"$pre_result"

post_result=$(cargo run -q -p axeyum-lean-kernel \
  --example autogenesis_apply_plan_check -- \
  --plans "$scratch/post_b-output/apply-plans.tsv" \
  --phase post_b \
  --candidate "$post_candidate" \
  --premise-candidate "$premise_candidate" \
  --budget "$budget" \
  --expect proved \
  --bundle-sha256 "$post_bundle" \
  --catalog-sha256 "$post_catalog")
grep -qxF \
  "AUTOGENESIS_APPLY_RESULT|phase=post_b|attempted=1|budget=$budget|outcome=proved|theorem=$premise_candidate" \
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
  python3 - "$scratch" "$budget" "$pre_result" "$post_result" <<'PY'
import hashlib
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
budget = int(sys.argv[2])
baseline = json.load(open(root / "baseline-execution.json"))
snapshot = json.load(open(root / "snapshot.json"))
pre_catalog = json.load(open(root / "pre_a-catalog.json"))
post_catalog = json.load(open(root / "post_b-catalog.json"))
pre_bundle = json.load(open(root / "pre_a-output/apply-plans.json"))
post_bundle = json.load(open(root / "post_b-output/apply-plans.json"))
report = {
    "schema_version": 1,
    "kind": "axeyum-autogenesis-apply-experiment",
    "git_commit": baseline["git_commit"],
    "baseline_source_sha256": baseline["baseline_source_sha256"],
    "snapshot_sha256": snapshot["snapshot_sha256"],
    "episode_id": snapshot["episode_id"],
    "target_fact_id": snapshot["chain"]["consequent"]["fact_id"],
    "premise_fact_id": snapshot["chain"]["premise"]["fact_id"],
    "budget": budget,
    "pre_a": {
        "catalog_sha256": pre_catalog["catalog_sha256"],
        "bundle_sha256": pre_bundle["bundle_sha256"],
        "result": sys.argv[3],
    },
    "post_b": {
        "catalog_sha256": post_catalog["catalog_sha256"],
        "bundle_sha256": post_bundle["bundle_sha256"],
        "result": sys.argv[4],
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

echo "AUTOGENESIS_APPLY_SEARCH|target=A|budget=$budget|pre_a=no-proof|post_b=proved|dependency=episode-premise"
