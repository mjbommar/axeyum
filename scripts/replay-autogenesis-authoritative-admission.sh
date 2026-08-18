#!/usr/bin/env bash
# Reproduce one authoritative Autogenesis admission in an isolated clean worktree.
set -euo pipefail

cd "$(dirname "$0")/.."
[ "$#" -eq 2 ] || {
  echo "usage: $0 RETAINED-ADMISSION-DIRECTORY OUTPUT-DIRECTORY" >&2
  exit 2
}

source_root=$(git rev-parse --show-toplevel)
retained=$(realpath "$1")
output=$(realpath -m "$2")
[ -d "$retained" ] || {
  echo "AUTOGENESIS_AUTHORITATIVE_REPLAY_ERROR|retained admission does not exist" >&2
  exit 1
}
[ ! -e "$output" ] || {
  echo "AUTOGENESIS_AUTHORITATIVE_REPLAY_ERROR|refusing to overwrite output directory" >&2
  exit 1
}
case "$output" in
  "$source_root"/*)
    echo "AUTOGENESIS_AUTHORITATIVE_REPLAY_ERROR|output must be outside the source checkout" >&2
    exit 1
    ;;
esac
[ -z "$(git status --porcelain --untracked-files=all)" ] || {
  echo "AUTOGENESIS_AUTHORITATIVE_REPLAY_ERROR|source checkout must be clean" >&2
  exit 1
}

required=(frontier-before.json execution.json transaction.json frontier-after.json readiness.json)
for relative in "${required[@]}"; do
  [ -f "$retained/$relative" ] || {
    echo "AUTOGENESIS_AUTHORITATIVE_REPLAY_ERROR|missing retained artifact: $relative" >&2
    exit 1
  }
done

read -r retained_event_relative prestate_commit fact_id < <(
  python3 - "$retained" <<'PY'
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
transaction = json.load(open(root / "transaction.json"))
execution = json.load(open(root / "execution.json"))
transaction_sha = transaction["transaction_sha256"]
print(
    f"journal/{transaction_sha}/admission-event.json",
    execution["identity"]["git_commit"],
    execution["identity"]["fact_id"],
)
PY
)
[ -f "$retained/$retained_event_relative" ] || {
  echo "AUTOGENESIS_AUTHORITATIVE_REPLAY_ERROR|missing retained durable event" >&2
  exit 1
}

# First prove that the retained historical acquisition still closes under the
# current checker. The fresh run below does not reuse any of these receipts.
python3 scripts/create-autogenesis-readiness-delta.py \
  --transaction "$retained/transaction.json" \
  --durable-admission-event "$retained/$retained_event_relative" \
  --execution "$retained/execution.json" \
  --frontier-before "$retained/frontier-before.json" \
  --frontier-after "$retained/frontier-after.json" \
  --verify "$retained/readiness.json" >/dev/null

scratch=$(mktemp -d /tmp/axeyum-authoritative-replay.XXXXXX)
checkout="$scratch/checkout"
fresh="$scratch/fresh"
mkdir -p "$fresh"
cleanup() {
  if [ -d "$checkout" ]; then
    git -C "$source_root" worktree remove --force "$checkout" >/dev/null 2>&1 || true
  fi
  case "$scratch" in
    /tmp/axeyum-authoritative-replay.*) rm -rf "$scratch" ;;
  esac
}
trap cleanup EXIT

source_head=$(git rev-parse HEAD)
git worktree add --detach "$checkout" "$source_head" >/dev/null
fact_relative="artifacts/facts/${fact_id/F:/F-}.json"
git -C "$source_root" show "$prestate_commit:$fact_relative" >"$checkout/$fact_relative"
git -C "$checkout" add "$fact_relative"
GIT_AUTHOR_NAME=axeyum-autogenesis-replay \
GIT_AUTHOR_EMAIL=autogenesis-replay@invalid \
GIT_AUTHOR_DATE=2000-01-01T00:00:00Z \
GIT_COMMITTER_NAME=axeyum-autogenesis-replay \
GIT_COMMITTER_EMAIL=autogenesis-replay@invalid \
GIT_COMMITTER_DATE=2000-01-01T00:00:00Z \
  git -C "$checkout" commit --no-verify -m "test(autogenesis): reconstruct admission pre-state" >/dev/null
replay_commit=$(git -C "$checkout" rev-parse HEAD)
[ -z "$(git -C "$checkout" status --porcelain --untracked-files=all)" ] || {
  echo "AUTOGENESIS_AUTHORITATIVE_REPLAY_ERROR|reconstructed checkout is not clean" >&2
  exit 1
}

(
  cd "$checkout"
  python3 scripts/validate-facts.py >/dev/null
  python3 scripts/fact-frontier.py --output "$fresh/frontier-before.json" >/dev/null
  CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/target}" \
    python3 scripts/execute-autogenesis-operation.py \
      --frontier "$fresh/frontier-before.json" \
      --output "$fresh/execution.json" >/dev/null
  cp "$fact_relative" "$fresh/before-fact.json"
  CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/target}" \
    python3 scripts/prepare-autogenesis-fact-transaction.py \
      --fact "$fact_relative" \
      --frontier "$fresh/frontier-before.json" \
      --execution "$fresh/execution.json" \
      --output "$fresh/transaction.json" >/dev/null

  set +e
  CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/target}" \
    python3 scripts/apply-autogenesis-fact-transaction.py \
      --transaction "$fresh/transaction.json" \
      --frontier "$fresh/frontier-before.json" \
      --execution "$fresh/execution.json" \
      --before-fact "$fact_relative" \
      --journal-dir "$fresh/journal" \
      --fault-after intent >/dev/null 2>&1
  fault_status=$?
  set -e
  [ "$fault_status" -eq 75 ] || {
    echo "AUTOGENESIS_AUTHORITATIVE_REPLAY_ERROR|intent fault did not stop at exit 75" >&2
    exit 1
  }
  cmp -s "$fresh/before-fact.json" "$fact_relative" || {
    echo "AUTOGENESIS_AUTHORITATIVE_REPLAY_ERROR|intent fault changed the fact" >&2
    exit 1
  }
  python3 scripts/apply-autogenesis-fact-transaction.py \
    --transaction "$fresh/transaction.json" \
    --journal-dir "$fresh/journal" \
    --recover >/dev/null

  fresh_transaction=$(python3 - "$fresh/transaction.json" <<'PY'
import json, sys
print(json.load(open(sys.argv[1]))["transaction_sha256"])
PY
)
  cp "$fresh/journal/$fresh_transaction/admission-event.json" "$fresh/admission-event.json"
  python3 scripts/fact-frontier.py --output "$fresh/frontier-after.json" >/dev/null
  python3 scripts/create-autogenesis-readiness-delta.py \
    --transaction "$fresh/transaction.json" \
    --durable-admission-event "$fresh/admission-event.json" \
    --execution "$fresh/execution.json" \
    --frontier-before "$fresh/frontier-before.json" \
    --frontier-after "$fresh/frontier-after.json" \
    --output "$fresh/readiness.json" >/dev/null
  CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/target}" \
    python3 scripts/check-autogenesis-fact-operation.py --fact "$fact_relative" >/dev/null
  python3 scripts/validate-facts.py >/dev/null
)

mkdir -p "$output"
cp -a "$fresh/." "$output/"
python3 - \
  "$retained" "$output" "$source_head" "$prestate_commit" "$replay_commit" "$output/replay.json" <<'PY'
import hashlib
import json
import pathlib
import sys

retained_root = pathlib.Path(sys.argv[1])
fresh_root = pathlib.Path(sys.argv[2])
source_head, prestate_commit, replay_commit = sys.argv[3:6]
output = pathlib.Path(sys.argv[6])

def load(root, name):
    return json.load(open(root / name))

def digest(value):
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()

retained = {
    name: load(retained_root, name)
    for name in ("frontier-before.json", "execution.json", "transaction.json", "frontier-after.json", "readiness.json")
}
fresh = {
    name: load(fresh_root, name)
    for name in ("frontier-before.json", "execution.json", "transaction.json", "frontier-after.json", "readiness.json")
}
retained_event = load(
    retained_root,
    f"journal/{retained['transaction.json']['transaction_sha256']}/admission-event.json",
)
fresh_event = load(fresh_root, "admission-event.json")

fact_id = retained["execution.json"]["identity"]["fact_id"]
operation_id = retained["execution.json"]["identity"]["operation_id"]
checks = {
    "same_fact": fresh["execution.json"]["identity"]["fact_id"] == fact_id,
    "same_registered_operation": fresh["execution.json"]["identity"]["operation_id"] == operation_id,
    "same_certified_result": fresh["execution.json"]["result"] == retained["execution.json"]["result"],
    "same_acceptance_policy": fresh["execution.json"]["acceptance"] == retained["execution.json"]["acceptance"],
    "selected_before": fresh["frontier-before.json"]["selection"]["selected_fact_id"] == fact_id,
    "admitted_event": fresh_event["event_type"] == "fact-admitted",
    "removed_from_ready": fresh["readiness.json"]["frontier_change"]["no_longer_ready"] == [fact_id],
    "honest_leaf_unlock": fresh["readiness.json"]["newly_ready"] == [],
    "one_authoritative_write": fresh["readiness.json"]["authoritative_ledger_writes"] == 1,
    "zero_fixture_writes": fresh["readiness.json"]["fixture_writes"] == 0,
}
if not all(checks.values()):
    failed = sorted(name for name, passed in checks.items() if not passed)
    raise SystemExit(f"AUTOGENESIS_AUTHORITATIVE_REPLAY_ERROR|semantic checks failed: {failed}")

report = {
    "schema_version": 1,
    "kind": "axeyum-autogenesis-authoritative-admission-replay",
    "mode": "isolated-clean-worktree-semantic-reproduction",
    "source_head": source_head,
    "historical_prestate_commit": prestate_commit,
    "reconstructed_replay_commit": replay_commit,
    "identity": {"fact_id": fact_id, "operation_id": operation_id},
    "fault_injection": {
        "boundary": "after-intent",
        "exit_status": 75,
        "fact_unchanged_before_recovery": True,
    },
    "checks": checks,
    "retained": {
        "execution_sha256": retained["execution.json"]["execution_sha256"],
        "transaction_sha256": retained["transaction.json"]["transaction_sha256"],
        "event_sha256": retained_event["event_sha256"],
        "readiness_delta_sha256": retained["readiness.json"]["readiness_delta_sha256"],
    },
    "fresh": {
        "frontier_before_sha256": fresh["frontier-before.json"]["frontier_sha256"],
        "execution_sha256": fresh["execution.json"]["execution_sha256"],
        "transaction_sha256": fresh["transaction.json"]["transaction_sha256"],
        "event_sha256": fresh_event["event_sha256"],
        "frontier_after_sha256": fresh["frontier-after.json"]["frontier_sha256"],
        "readiness_delta_sha256": fresh["readiness.json"]["readiness_delta_sha256"],
    },
}
report["replay_sha256"] = digest(report)
output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
print(
    f"AUTOGENESIS_AUTHORITATIVE_REPLAY_OK|{report['replay_sha256']}|"
    f"fact={fact_id}|operation={operation_id}|output={output}"
)
PY

[ -z "$(git status --porcelain --untracked-files=all)" ] || {
  echo "AUTOGENESIS_AUTHORITATIVE_REPLAY_ERROR|source checkout was mutated" >&2
  exit 1
}
