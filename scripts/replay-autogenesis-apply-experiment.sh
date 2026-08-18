#!/usr/bin/env bash
# Replay a retained Autogenesis apply experiment from its immutable inputs.
set -euo pipefail

cd "$(dirname "$0")/.."
[ "$#" -eq 1 ] || {
  echo "usage: $0 RETAINED-EXPERIMENT-DIRECTORY" >&2
  exit 2
}
experiment_dir=$(realpath "$1")
[ -d "$experiment_dir" ] || {
  echo "AUTOGENESIS_REPLAY_ERROR|experiment directory does not exist" >&2
  exit 1
}
required=(
  baseline-execution.json experiment.json snapshot.json
  pre_b-catalog.json pre_b-induction-output/induction-plans.json
  pre_b-induction-output/induction-plans.tsv premise-kernel-evidence.tsv
  premise-evidence.json premise-transition.json premise-accepted-event.json
  fact-transaction-proposal.json
  pre_a-catalog.json pre_a-output/apply-plans.json pre_a-output/apply-plans.tsv
  post_b-catalog.json post_b-output/apply-plans.json post_b-output/apply-plans.tsv
)
for relative in "${required[@]}"; do
  [ -f "$experiment_dir/$relative" ] || {
    echo "AUTOGENESIS_REPLAY_ERROR|missing retained input: $relative" >&2
    exit 1
  }
done
retained_transaction_sha=$(python3 - "$experiment_dir/fact-transaction-proposal.json" <<'PY'
import json, sys
print(json.load(open(sys.argv[1]))["transaction_sha256"])
PY
)
for relative in \
  "fixture-journal/$retained_transaction_sha/intent.json" \
  "fixture-journal/$retained_transaction_sha/admission-event.json" \
  fixture-facts/F-nat-zero-add.json; do
  [ -f "$experiment_dir/$relative" ] || {
    echo "AUTOGENESIS_REPLAY_ERROR|missing retained admission artifact: $relative" >&2
    exit 1
  }
done
[ -z "$(git status --porcelain --untracked-files=normal)" ] || {
  echo "AUTOGENESIS_REPLAY_ERROR|replay requires a clean checkout" >&2
  exit 1
}
head_commit=$(git rev-parse HEAD)

python3 - "$experiment_dir" "$head_commit" <<'PY'
import hashlib
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
head = sys.argv[2]

def load(relative):
    return json.load(open(root / relative))

def digest(value):
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()

report = load("experiment.json")
capture = load("baseline-execution.json")
snapshot = load("snapshot.json")
premise_catalog = load("pre_b-catalog.json")
premise_bundle = load("pre_b-induction-output/induction-plans.json")
evidence = load("premise-evidence.json")
transition = load("premise-transition.json")
event = load("premise-accepted-event.json")
transaction = load("fact-transaction-proposal.json")
durable_event = load(f"fixture-journal/{transaction['transaction_sha256']}/admission-event.json")
pre_catalog = load("pre_a-catalog.json")
pre_bundle = load("pre_a-output/apply-plans.json")
post_catalog = load("post_b-catalog.json")
post_bundle = load("post_b-output/apply-plans.json")

if report.get("schema_version") != 7 or report.get("kind") != "axeyum-autogenesis-apply-experiment":
    raise SystemExit("AUTOGENESIS_REPLAY_ERROR|unsupported experiment schema")
unsigned = dict(report)
claimed = unsigned.pop("experiment_sha256", None)
if claimed != digest(unsigned):
    raise SystemExit("AUTOGENESIS_REPLAY_ERROR|experiment digest is invalid")
if report.get("git_commit") != head or capture.get("git_commit") != head:
    raise SystemExit("AUTOGENESIS_REPLAY_ERROR|checkout does not match retained exact commit")
checks = {
    "snapshot": (report.get("snapshot_sha256"), snapshot.get("snapshot_sha256")),
    "premise catalog": (report["premise"].get("catalog_sha256"), premise_catalog.get("catalog_sha256")),
    "premise bundle": (report["premise"].get("bundle_sha256"), premise_bundle.get("bundle_sha256")),
    "premise evidence": (report["premise"].get("evidence_sha256"), evidence.get("evidence_sha256")),
    "premise transition": (report["premise"].get("transition_sha256"), transition.get("transition_sha256")),
    "accepted event": (report["premise"].get("accepted_event_sha256"), event.get("event_sha256")),
    "fact transaction": (report["premise"].get("fact_transaction_sha256"), transaction.get("transaction_sha256")),
    "durable admission event": (report["premise"].get("durable_admission_event_sha256"), durable_event.get("event_sha256")),
    "pre-A catalog": (report["pre_a"].get("catalog_sha256"), pre_catalog.get("catalog_sha256")),
    "pre-A bundle": (report["pre_a"].get("bundle_sha256"), pre_bundle.get("bundle_sha256")),
    "post-B catalog": (report["post_b"].get("catalog_sha256"), post_catalog.get("catalog_sha256")),
    "post-B bundle": (report["post_b"].get("bundle_sha256"), post_bundle.get("bundle_sha256")),
}
for label, (claimed_value, observed_value) in checks.items():
    if claimed_value != observed_value:
        raise SystemExit(f"AUTOGENESIS_REPLAY_ERROR|{label} identity mismatch")
if report.get("same_target") is not True or pre_catalog.get("target") != post_catalog.get("target"):
    raise SystemExit("AUTOGENESIS_REPLAY_ERROR|pre/post target identity changed")
if event.get("authoritative_ledger_writes") != [] or transition.get("authoritative_ledger", {}).get("writes") != []:
    raise SystemExit("AUTOGENESIS_REPLAY_ERROR|bootstrap artifacts contain ledger writes")
if transaction.get("state") != "prepared" or transaction.get("admission_event") is not None:
    raise SystemExit("AUTOGENESIS_REPLAY_ERROR|transaction proposal overclaims admission")
if report["premise"].get("fact_transaction_source_authoritative") is not False:
    raise SystemExit("AUTOGENESIS_REPLAY_ERROR|fixture transaction misreports its source")
if report["premise"].get("durable_admission_source") != "fixture":
    raise SystemExit("AUTOGENESIS_REPLAY_ERROR|durable admission source is not the fixture")
if durable_event.get("publication") != {"artifact_archived": False, "git_published": False}:
    raise SystemExit("AUTOGENESIS_REPLAY_ERROR|fixture event overclaims publication")
PY

python3 scripts/gen-autogenesis-baseline.py --check
read -r expected_source expected_artifact < <(
  python3 - <<'PY'
import hashlib, json
from pathlib import Path
baseline = Path("docs/plan/generated/autogenesis-baseline.json")
report = json.load(open(baseline))
print(report["source_identity"]["digest"], hashlib.sha256(baseline.read_bytes()).hexdigest())
PY
)
read -r captured_source captured_artifact < <(
  python3 - "$experiment_dir/baseline-execution.json" <<'PY'
import json, sys
capture = json.load(open(sys.argv[1]))
print(capture["baseline_source_sha256"], capture["baseline_artifact_sha256"])
PY
)
[ "$expected_source" = "$captured_source" ] && [ "$expected_artifact" = "$captured_artifact" ] || {
  echo "AUTOGENESIS_REPLAY_ERROR|retained baseline capture is stale" >&2
  exit 1
}

transition_chain=(
  --premise-evidence "$experiment_dir/premise-evidence.json"
  --premise-transition "$experiment_dir/premise-transition.json"
  --accepted-transition-event "$experiment_dir/premise-accepted-event.json"
)
python3 scripts/create-autogenesis-proposer-catalog.py \
  --snapshot "$experiment_dir/snapshot.json" --phase pre_b \
  --verify "$experiment_dir/pre_b-catalog.json" >/dev/null
python3 scripts/create-autogenesis-proposer-catalog.py \
  --snapshot "$experiment_dir/snapshot.json" --phase pre_a \
  --verify "$experiment_dir/pre_a-catalog.json" >/dev/null
python3 scripts/create-autogenesis-proposer-catalog.py \
  --snapshot "$experiment_dir/snapshot.json" --phase post_b \
  "${transition_chain[@]}" --verify "$experiment_dir/post_b-catalog.json" >/dev/null
python3 scripts/verify-autogenesis-induction-proposals.py \
  --catalog "$experiment_dir/pre_b-catalog.json" \
  --bundle "$experiment_dir/pre_b-induction-output/induction-plans.json" \
  --tsv "$experiment_dir/pre_b-induction-output/induction-plans.tsv" >/dev/null
for phase in pre_a post_b; do
  python3 scripts/verify-autogenesis-apply-proposals.py \
    --catalog "$experiment_dir/$phase-catalog.json" \
    --bundle "$experiment_dir/$phase-output/apply-plans.json" \
    --tsv "$experiment_dir/$phase-output/apply-plans.tsv" >/dev/null
done

scratch=$(mktemp -d /tmp/axeyum-autogenesis-replay.XXXXXX)
trap 'rm -r "$scratch"' EXIT
read -r premise_bundle premise_catalog premise_candidate premise_budget apply_budget < <(
  python3 - "$experiment_dir" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
report = json.load(open(root / "experiment.json"))
catalog = json.load(open(root / "pre_b-catalog.json"))
print(report["premise"]["bundle_sha256"], report["premise"]["catalog_sha256"], catalog["target"]["name"], report["premise"]["budget"], report["budget"])
PY
)
premise_result=$(cargo run -q -p axeyum-lean-kernel \
  --example autogenesis_induction_plan_check -- \
  --plans "$experiment_dir/pre_b-induction-output/induction-plans.tsv" \
  --candidate "$premise_candidate" --budget "$premise_budget" --expect proved \
  --bundle-sha256 "$premise_bundle" --catalog-sha256 "$premise_catalog" \
  --evidence-output "$scratch/premise-kernel-evidence.tsv")
cmp -s "$scratch/premise-kernel-evidence.tsv" "$experiment_dir/premise-kernel-evidence.tsv" || {
  echo "AUTOGENESIS_REPLAY_ERROR|fresh kernel evidence differs" >&2
  exit 1
}

evidence_args=(
  --snapshot "$experiment_dir/snapshot.json"
  --catalog "$experiment_dir/pre_b-catalog.json"
  --bundle "$experiment_dir/pre_b-induction-output/induction-plans.json"
  --plans "$experiment_dir/pre_b-induction-output/induction-plans.tsv"
  --kernel-evidence "$scratch/premise-kernel-evidence.tsv"
)
python3 scripts/create-autogenesis-premise-evidence.py \
  "${evidence_args[@]}" --output "$scratch/premise-evidence.json" >/dev/null
cmp -s "$scratch/premise-evidence.json" "$experiment_dir/premise-evidence.json" || {
  echo "AUTOGENESIS_REPLAY_ERROR|fresh premise evidence differs" >&2
  exit 1
}
python3 scripts/create-autogenesis-premise-transition.py \
  --snapshot "$experiment_dir/snapshot.json" \
  --premise-evidence "$scratch/premise-evidence.json" \
  --output "$scratch/premise-transition.json" >/dev/null
cmp -s "$scratch/premise-transition.json" "$experiment_dir/premise-transition.json" || {
  echo "AUTOGENESIS_REPLAY_ERROR|fresh premise transition differs" >&2
  exit 1
}
python3 scripts/create-autogenesis-accepted-event.py \
  --snapshot "$experiment_dir/snapshot.json" \
  --premise-evidence "$scratch/premise-evidence.json" \
  --premise-transition "$scratch/premise-transition.json" \
  --output "$scratch/premise-accepted-event.json" >/dev/null
cmp -s "$scratch/premise-accepted-event.json" "$experiment_dir/premise-accepted-event.json" || {
  echo "AUTOGENESIS_REPLAY_ERROR|fresh accepted event differs" >&2
  exit 1
}
python3 scripts/prepare-autogenesis-fact-transaction.py \
  --fact scripts/tests/fixtures/F-nat-zero-add-open.json \
  --bundle "$experiment_dir" \
  --output "$scratch/fact-transaction-proposal.json" >/dev/null
cmp -s "$scratch/fact-transaction-proposal.json" "$experiment_dir/fact-transaction-proposal.json" || {
  echo "AUTOGENESIS_REPLAY_ERROR|fresh fact transaction proposal differs" >&2
  exit 1
}
mkdir "$scratch/fixture-facts" "$scratch/fixture-journal"
install -m 0644 scripts/tests/fixtures/F-nat-zero-add-open.json \
  "$scratch/fixture-facts/F-nat-zero-add.json"
replay_admission_args=(
  --transaction "$scratch/fact-transaction-proposal.json"
  --bundle "$experiment_dir"
  --before-fact scripts/tests/fixtures/F-nat-zero-add-open.json
  --journal-dir "$scratch/fixture-journal"
  --fixture-fact-root "$scratch/fixture-facts"
)
set +e
python3 scripts/apply-autogenesis-fact-transaction.py \
  "${replay_admission_args[@]}" --fault-after fact \
  >"$scratch/admission-fault.stdout" 2>"$scratch/admission-fault.stderr"
replay_fault_status=$?
set -e
[ "$replay_fault_status" -eq 75 ] || {
  echo "AUTOGENESIS_REPLAY_ERROR|after-fact fault did not stop at recovery boundary" >&2
  exit 1
}
python3 scripts/apply-autogenesis-fact-transaction.py \
  "${replay_admission_args[@]}" >/dev/null
cmp -s \
  "$scratch/fixture-journal/$retained_transaction_sha/admission-event.json" \
  "$experiment_dir/fixture-journal/$retained_transaction_sha/admission-event.json" || {
  echo "AUTOGENESIS_REPLAY_ERROR|fresh durable admission event differs" >&2
  exit 1
}

read -r pre_bundle pre_catalog pre_candidate post_bundle post_catalog post_candidate < <(
  python3 - "$experiment_dir" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
pre = json.load(open(root / "pre_a-catalog.json"))
post = json.load(open(root / "post_b-catalog.json"))
pre_bundle = json.load(open(root / "pre_a-output/apply-plans.json"))
post_bundle = json.load(open(root / "post_b-output/apply-plans.json"))
print(pre_bundle["bundle_sha256"], pre["catalog_sha256"], pre["target"]["name"], post_bundle["bundle_sha256"], post["catalog_sha256"], post["target"]["name"])
PY
)
pre_result=$(cargo run -q -p axeyum-lean-kernel \
  --example autogenesis_apply_plan_check -- \
  --plans "$experiment_dir/pre_a-output/apply-plans.tsv" --phase pre_a \
  --candidate "$pre_candidate" --budget "$apply_budget" --expect no-proof \
  --bundle-sha256 "$pre_bundle" --catalog-sha256 "$pre_catalog")
post_result=$(cargo run -q -p axeyum-lean-kernel \
  --example autogenesis_apply_plan_check -- \
  --plans "$experiment_dir/post_b-output/apply-plans.tsv" --phase post_b \
  --candidate "$post_candidate" --premise-candidate "$premise_candidate" \
  --premise-plans "$experiment_dir/pre_b-induction-output/induction-plans.tsv" \
  --premise-budget "$premise_budget" --premise-bundle-sha256 "$premise_bundle" \
  --premise-catalog-sha256 "$premise_catalog" --budget "$apply_budget" \
  --expect proved --bundle-sha256 "$post_bundle" --catalog-sha256 "$post_catalog")
python3 - "$experiment_dir/experiment.json" "$premise_result" "$pre_result" "$post_result" <<'PY'
import json, sys
report = json.load(open(sys.argv[1]))
observed = (sys.argv[2], sys.argv[3], sys.argv[4])
expected = (report["premise"]["result"], report["pre_a"]["result"], report["post_b"]["result"])
if observed != expected:
    raise SystemExit("AUTOGENESIS_REPLAY_ERROR|fresh kernel outcomes differ")
PY
[ -z "$(git status --porcelain --untracked-files=normal)" ] || {
  echo "AUTOGENESIS_REPLAY_ERROR|replay mutated the checkout" >&2
  exit 1
}
echo "AUTOGENESIS_APPLY_REPLAY|commit=$head_commit|experiment=$(basename "$experiment_dir")|premise=proved|event=reproduced|transaction=committed-fixture+fault-recovered|pre_a=no-proof|post_b=proved|authoritative_writes=0|fixture_writes=1"
