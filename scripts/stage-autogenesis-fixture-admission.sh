#!/usr/bin/env bash
# Commit the counterfactual B proposal in a temporary fact root and derive readiness.
set -euo pipefail

cd "$(dirname "$0")/.."
usage() {
  echo "usage: $0 --snapshot PATH --bundle-root DIR [--evidence-bundle DIR] [--fault-after intent|fact|event]" >&2
  exit 2
}
snapshot=
bundle_root=
evidence_bundle=
fault_after=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --snapshot) snapshot="${2:-}"; shift 2 ;;
    --bundle-root) bundle_root="${2:-}"; shift 2 ;;
    --evidence-bundle) evidence_bundle="${2:-}"; shift 2 ;;
    --fault-after) fault_after="${2:-}"; shift 2 ;;
    *) usage ;;
  esac
done
[ -n "$snapshot" ] && [ -n "$bundle_root" ] || usage
case "$fault_after" in ""|intent|fact|event) ;; *) usage ;; esac
snapshot=$(realpath "$snapshot")
bundle_root=$(realpath "$bundle_root")
[ -n "$evidence_bundle" ] || evidence_bundle="$bundle_root"
evidence_bundle=$(realpath "$evidence_bundle")
for relative in fact-transaction-proposal.json fixture-facts fixture-journal readiness-delta.json; do
  [ ! -e "$bundle_root/$relative" ] || {
    echo "AUTOGENESIS_FIXTURE_ADMISSION_ERROR|refusing to overwrite $bundle_root/$relative" >&2
    exit 1
  }
done

python3 scripts/prepare-autogenesis-fact-transaction.py \
  --fact scripts/tests/fixtures/F-nat-zero-add-open.json \
  --bundle "$evidence_bundle" \
  --output "$bundle_root/fact-transaction-proposal.json" >/dev/null
python3 scripts/prepare-autogenesis-fact-transaction.py \
  --fact scripts/tests/fixtures/F-nat-zero-add-open.json \
  --bundle "$evidence_bundle" \
  --verify "$bundle_root/fact-transaction-proposal.json" >/dev/null
mkdir "$bundle_root/fixture-facts" "$bundle_root/fixture-journal"
install -m 0644 scripts/tests/fixtures/F-nat-zero-add-open.json \
  "$bundle_root/fixture-facts/F-nat-zero-add.json"
admission_args=(
  --transaction "$bundle_root/fact-transaction-proposal.json"
  --bundle "$evidence_bundle"
  --before-fact scripts/tests/fixtures/F-nat-zero-add-open.json
  --journal-dir "$bundle_root/fixture-journal"
  --fixture-fact-root "$bundle_root/fixture-facts"
)
if [ -n "$fault_after" ]; then
  set +e
  python3 scripts/apply-autogenesis-fact-transaction.py \
    "${admission_args[@]}" --fault-after "$fault_after" \
    >"$bundle_root/admission-fault.stdout" \
    2>"$bundle_root/admission-fault.stderr"
  fault_status=$?
  set -e
  [ "$fault_status" -eq 75 ] || {
    echo "AUTOGENESIS_FIXTURE_ADMISSION_ERROR|fault returned $fault_status, expected 75" >&2
    exit 1
  }
  grep -qF "AUTOGENESIS_FACT_ADMISSION_FAULT|after-$fault_after" \
    "$bundle_root/admission-fault.stderr"
fi
admission_result=$(python3 scripts/apply-autogenesis-fact-transaction.py \
  "${admission_args[@]}")
grep -qE '^AUTOGENESIS_FACT_ADMISSION\|.*\|state=committed\|artifact_archived=false\|git_published=false$' \
  <<<"$admission_result"

transaction_sha=$(python3 -c \
  'import json,sys; print(json.load(open(sys.argv[1]))["transaction_sha256"])' \
  "$bundle_root/fact-transaction-proposal.json")
durable_event="$bundle_root/fixture-journal/$transaction_sha/admission-event.json"
readiness_args=(
  --snapshot "$snapshot"
  --transaction "$bundle_root/fact-transaction-proposal.json"
  --durable-admission-event "$durable_event"
)
python3 scripts/create-autogenesis-readiness-delta.py \
  "${readiness_args[@]}" --output "$bundle_root/readiness-delta.json" >/dev/null
python3 scripts/create-autogenesis-readiness-delta.py \
  "${readiness_args[@]}" --verify "$bundle_root/readiness-delta.json" >/dev/null
read -r event_sha readiness_sha < <(
  python3 - "$durable_event" "$bundle_root/readiness-delta.json" <<'PY'
import json, sys
event = json.load(open(sys.argv[1]))
readiness = json.load(open(sys.argv[2]))
print(event["event_sha256"], readiness["readiness_delta_sha256"])
PY
)
echo "AUTOGENESIS_FIXTURE_ADMISSION|transaction=$transaction_sha|event=$event_sha|readiness=$readiness_sha|authoritative_writes=0|fixture_writes=1"
