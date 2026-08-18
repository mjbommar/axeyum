#!/usr/bin/env bash
# End-to-end proof-body and host-visibility control for a post-B proposer.
set -euo pipefail

cd "$(dirname "$0")/.."
scratch=$(mktemp -d /tmp/axeyum-autogenesis-proposer.XXXXXX)
trap 'rm -r "$scratch"' EXIT
mkdir "$scratch/output"

python3 scripts/create-autogenesis-snapshot.py \
  --premise F:nat-zero-add \
  --consequent F:nat-mul-one \
  --output "$scratch/snapshot.json" >/dev/null
scripts/stage-autogenesis-premise.sh \
  --snapshot "$scratch/snapshot.json" \
  --output-dir "$scratch" >/dev/null
scripts/stage-autogenesis-fixture-admission.sh \
  --snapshot "$scratch/snapshot.json" \
  --bundle-root "$scratch" >/dev/null
fact_transaction_sha=$(python3 -c \
  'import json,sys; print(json.load(open(sys.argv[1]))["transaction_sha256"])' \
  "$scratch/fact-transaction-proposal.json")
transition_chain=(
  --premise-evidence "$scratch/premise-evidence.json"
  --premise-transition "$scratch/premise-transition.json"
  --accepted-transition-event "$scratch/premise-accepted-event.json"
  --fact-transaction "$scratch/fact-transaction-proposal.json"
  --durable-admission-event "$scratch/fixture-journal/$fact_transaction_sha/admission-event.json"
  --readiness-delta "$scratch/readiness-delta.json"
)
python3 scripts/create-autogenesis-proposer-catalog.py \
  --snapshot "$scratch/snapshot.json" \
  --phase post_b \
  "${transition_chain[@]}" \
  --output "$scratch/catalog.json" >/dev/null
scripts/run-autogenesis-python-proposer.sh \
  --snapshot "$scratch/snapshot.json" \
  --catalog "$scratch/catalog.json" \
  --output-dir "$scratch/output" \
  --program scripts/tests/fixtures/autogenesis-proposer-probe.py \
  "${transition_chain[@]}" >/dev/null

python3 - "$scratch/catalog.json" "$scratch/output/probe-result.json" <<'PY'
import json
import sys

catalog = json.load(open(sys.argv[1]))
result = json.load(open(sys.argv[2]))
assert result == {
    "catalog_sha256": catalog["catalog_sha256"],
    "environment_sanitized": True,
    "network_reachable": False,
    "repository_visible": False,
    "visible_entries": len(catalog["entries"]),
}
accepted = [entry for entry in catalog["entries"] if entry["origin"] == "accepted-episode"]
assert len(accepted) == 1
assert accepted[0]["name"] == catalog["target"]["name"].replace(".consequent", ".premise")
assert "Nat.zero_add" not in {entry["name"] for entry in catalog["entries"]}
assert "Nat.mul_one" not in {entry["name"] for entry in catalog["entries"]}
PY

if scripts/run-autogenesis-python-proposer.sh \
  --snapshot "$scratch/snapshot.json" \
  --catalog "$scratch/catalog.json" \
  --output-dir "$scratch/output" \
  --program scripts/tests/fixtures/autogenesis-proposer-probe.py \
  "${transition_chain[@]}" \
  >"$scratch/nonempty.stdout" 2>"$scratch/nonempty.stderr"; then
  echo "proposer isolation unexpectedly reused a nonempty output directory" >&2
  exit 1
fi
grep -qF 'AUTOGENESIS_PROPOSER_ERROR|output directory must start empty' \
  "$scratch/nonempty.stderr"

echo "AUTOGENESIS_PROPOSER_ISOLATION|catalog=verified|repository=hidden|network=hidden|environment=clean|proof_bodies=absent"
