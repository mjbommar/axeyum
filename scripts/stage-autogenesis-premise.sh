#!/usr/bin/env bash
# Produce and independently check the complete episode-local premise handoff.
set -euo pipefail

cd "$(dirname "$0")/.."

usage() {
  echo "usage: $0 --snapshot PATH --output-dir DIR [--budget N]" >&2
  exit 2
}

snapshot=
output_dir=
budget=2
while [ "$#" -gt 0 ]; do
  case "$1" in
    --snapshot) snapshot="${2:-}"; shift 2 ;;
    --output-dir) output_dir="${2:-}"; shift 2 ;;
    --budget) budget="${2:-}"; shift 2 ;;
    *) usage ;;
  esac
done
[ -n "$snapshot" ] && [ -n "$output_dir" ] || usage
[[ "$budget" =~ ^[1-9][0-9]*$ ]] || usage
[ -f "$snapshot" ] && [ -d "$output_dir" ] || {
  echo "AUTOGENESIS_PREMISE_STAGE_ERROR|snapshot and output directory must exist" >&2
  exit 1
}
snapshot=$(realpath "$snapshot")
output_dir=$(realpath "$output_dir")
for relative in \
  pre_b-catalog.json \
  pre_b-induction-output \
  premise-kernel-evidence.tsv \
  premise-result.txt \
  premise-evidence.json \
  premise-transition.json \
  premise-accepted-event.json; do
  [ ! -e "$output_dir/$relative" ] || {
    echo "AUTOGENESIS_PREMISE_STAGE_ERROR|refusing to overwrite $output_dir/$relative" >&2
    exit 1
  }
done

python3 scripts/create-autogenesis-proposer-catalog.py \
  --snapshot "$snapshot" \
  --phase pre_b \
  --output "$output_dir/pre_b-catalog.json" >/dev/null
mkdir "$output_dir/pre_b-induction-output"
scripts/run-autogenesis-python-proposer.sh \
  --snapshot "$snapshot" \
  --catalog "$output_dir/pre_b-catalog.json" \
  --output-dir "$output_dir/pre_b-induction-output" \
  --program scripts/autogenesis-induction-proposer.py >/dev/null
python3 scripts/verify-autogenesis-induction-proposals.py \
  --catalog "$output_dir/pre_b-catalog.json" \
  --bundle "$output_dir/pre_b-induction-output/induction-plans.json" \
  --tsv "$output_dir/pre_b-induction-output/induction-plans.tsv" >/dev/null

read -r bundle_sha catalog_sha candidate < <(
  python3 - "$output_dir" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
catalog = json.load(open(root / "pre_b-catalog.json"))
bundle = json.load(open(root / "pre_b-induction-output/induction-plans.json"))
print(bundle["bundle_sha256"], catalog["catalog_sha256"], catalog["target"]["name"])
PY
)
result=$(cargo run -q -p axeyum-lean-kernel \
  --example autogenesis_induction_plan_check -- \
  --plans "$output_dir/pre_b-induction-output/induction-plans.tsv" \
  --candidate "$candidate" \
  --budget "$budget" \
  --expect proved \
  --bundle-sha256 "$bundle_sha" \
  --catalog-sha256 "$catalog_sha" \
  --evidence-output "$output_dir/premise-kernel-evidence.tsv")
grep -qxF \
  "AUTOGENESIS_INDUCTION_RESULT|phase=pre_b|attempted=2|budget=$budget|outcome=proved|plan_rank=2" \
  <<<"$result"
printf '%s\n' "$result" >"$output_dir/premise-result.txt"

evidence_args=(
  --snapshot "$snapshot"
  --catalog "$output_dir/pre_b-catalog.json"
  --bundle "$output_dir/pre_b-induction-output/induction-plans.json"
  --plans "$output_dir/pre_b-induction-output/induction-plans.tsv"
  --kernel-evidence "$output_dir/premise-kernel-evidence.tsv"
)
python3 scripts/create-autogenesis-premise-evidence.py \
  "${evidence_args[@]}" --output "$output_dir/premise-evidence.json" >/dev/null
python3 scripts/create-autogenesis-premise-evidence.py \
  "${evidence_args[@]}" --verify "$output_dir/premise-evidence.json" >/dev/null

transition_args=(
  --snapshot "$snapshot"
  --premise-evidence "$output_dir/premise-evidence.json"
)
python3 scripts/create-autogenesis-premise-transition.py \
  "${transition_args[@]}" --output "$output_dir/premise-transition.json" >/dev/null
python3 scripts/create-autogenesis-premise-transition.py \
  "${transition_args[@]}" --verify "$output_dir/premise-transition.json" >/dev/null

event_args=(
  --snapshot "$snapshot"
  --premise-evidence "$output_dir/premise-evidence.json"
  --premise-transition "$output_dir/premise-transition.json"
)
python3 scripts/create-autogenesis-accepted-event.py \
  "${event_args[@]}" --output "$output_dir/premise-accepted-event.json" >/dev/null
python3 scripts/create-autogenesis-accepted-event.py \
  "${event_args[@]}" --verify "$output_dir/premise-accepted-event.json" >/dev/null

read -r evidence_sha transition_sha event_sha < <(
  python3 - "$output_dir" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
evidence = json.load(open(root / "premise-evidence.json"))
transition = json.load(open(root / "premise-transition.json"))
event = json.load(open(root / "premise-accepted-event.json"))
print(evidence["evidence_sha256"], transition["transition_sha256"], event["event_sha256"])
PY
)
echo "AUTOGENESIS_PREMISE_STAGE|candidate=$candidate|evidence=$evidence_sha|transition=$transition_sha|event=$event_sha|ledger_writes=0"
