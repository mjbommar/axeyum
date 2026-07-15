#!/usr/bin/env bash
# Availability-aware semantic regression gate for the access-controlled
# Glaurung QF_BV representative corpus. Performance acceptance remains in the
# clean-revision repeated/full recipes; this regular gate is safe to run while
# developing with a dirty worktree.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PINNED_DEFAULT="/nas4/data/workspace-infosec/glaurung-captures/2026-07-14-axeyum-v2/representative-producer"
EXPLICIT_CORPUS="${AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_DIR:-}"
EXPLICIT_MANIFEST="${AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_MANIFEST:-}"
AUTO_DISCOVER="${AXEYUM_GLAURUNG_QFBV_AUTO_DISCOVER:-1}"

case "$AUTO_DISCOVER" in
    0|1) ;;
    *)
        echo "glaurung-qfbv-regular: AXEYUM_GLAURUNG_QFBV_AUTO_DISCOVER must be 0 or 1" >&2
        exit 2
        ;;
esac

if [[ -n "$EXPLICIT_MANIFEST" && -z "$EXPLICIT_CORPUS" ]]; then
    echo "glaurung-qfbv-regular: AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_MANIFEST requires AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_DIR" >&2
    exit 2
fi

if [[ -n "$EXPLICIT_CORPUS" ]]; then
    CORPUS_DIR="$EXPLICIT_CORPUS"
    SOURCE="explicit AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_DIR"
elif [[ "$AUTO_DISCOVER" == 1 && -d "$PINNED_DEFAULT" ]]; then
    CORPUS_DIR="$PINNED_DEFAULT"
    SOURCE="pinned 2026-07-14 NAS capture"
else
    echo "glaurung-qfbv-regular: SKIP access-controlled representative corpus unavailable"
    echo "glaurung-qfbv-regular: set AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_DIR to enable the real-lifter gate"
    exit 0
fi

if [[ ! -d "$CORPUS_DIR" ]]; then
    echo "glaurung-qfbv-regular: configured corpus directory does not exist: $CORPUS_DIR" >&2
    exit 2
fi

MANIFEST="${EXPLICIT_MANIFEST:-$CORPUS_DIR/manifest-v1.json}"
if [[ ! -f "$MANIFEST" ]]; then
    echo "glaurung-qfbv-regular: corpus is available but manifest is missing: $MANIFEST" >&2
    exit 2
fi

OUT_DIR="${AXEYUM_GLAURUNG_QFBV_REGRESSION_OUT_DIR:-$ROOT/target/glaurung-qfbv-regular}"
MEMORY_GB="${AXEYUM_GLAURUNG_QFBV_MEMORY_GB:-4}"
mkdir -p "$OUT_DIR"

echo "glaurung-qfbv-regular: using $SOURCE"
echo "glaurung-qfbv-regular: corpus=$CORPUS_DIR"
echo "glaurung-qfbv-regular: manifest=$MANIFEST"

for POLICY in raw canonical; do
    case "$POLICY" in
        raw) POLICY_ARGS=(--rewrite off) ;;
        canonical) POLICY_ARGS=(--rewrite default) ;;
    esac
    ARTIFACT="$OUT_DIR/$POLICY.json"

    MEM_LIMIT_GB="$MEMORY_GB" "$ROOT/scripts/mem-run.sh" \
        cargo run --release -p axeyum-bench --features z3 -- \
        "$CORPUS_DIR" \
        --corpus-manifest "$MANIFEST" \
        --corpus-tier representative \
        --backend sat-bv \
        "${POLICY_ARGS[@]}" \
        --compare-z3 \
        --require-in-process-z3 \
        --require-deterministic-resources \
        --timeout-ms 10000 \
        --resource-limit 2000000 \
        --node-budget 300000 \
        --cnf-var-budget 3000000 \
        --cnf-clause-budget 8000000 \
        --jobs 1 \
        --min-decided-percent 100 \
        --logic QF_BV \
        --out "$ARTIFACT"

    python3 - "$ARTIFACT" "$POLICY" <<'PY'
import json
import sys

artifact_path, policy = sys.argv[1:]
with open(artifact_path, encoding="utf-8") as handle:
    artifact = json.load(handle)

if artifact.get("version") != 28:
    raise SystemExit(
        f"glaurung-qfbv-regular: expected artifact v28, got {artifact.get('version')!r}"
    )

summary = artifact["summary"]
files = summary["files"]
manifest = summary["manifest"]
oracle = summary["oracle"]
comparison = summary["client_comparison"]
layers = summary["layer_attribution"]

required = {
    "decided": summary["decided"],
    "manifest compared": manifest["compared"],
    "manifest agree": manifest["agree"],
    "oracle compared": oracle["compared"],
    "oracle agree": oracle["agree"],
}
bad = {name: value for name, value in required.items() if value != files}
if bad:
    raise SystemExit(
        f"glaurung-qfbv-regular: {policy} incomplete coverage for {files} files: {bad}"
    )
if any(
    (
        summary["errors"],
        summary["disagree"],
        summary["model_replay_failures"],
        manifest["disagree"],
        oracle["disagree"],
        oracle["skipped"],
    )
):
    raise SystemExit(f"glaurung-qfbv-regular: {policy} semantic gate failed")

print(
    "glaurung-qfbv-regular: "
    f"PASS policy={policy} files={files} "
    f"axeyum_s={comparison['axeyum_total_s']:.6f} "
    f"z3_s={comparison['z3_total_s']:.6f} "
    f"ratio={comparison['axeyum_over_z3_ratio']:.3f} "
    f"word_s={layers['word_preprocess_s']:.6f} "
    f"bit_blast_s={layers['bit_blast_s']:.6f} "
    f"cnf_s={layers['cnf_encode_s']:.6f} "
    f"sat_s={layers['solve_s']:.6f} "
    f"artifact={artifact_path}"
)
PY
done
