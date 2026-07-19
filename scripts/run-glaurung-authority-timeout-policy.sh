#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 5 ]]; then
    echo "usage: $0 OUT_DIR GLAURUNG_REPO Z3_BINARY AXEYUM_BINARY TCPIP_SYS" >&2
    exit 2
fi

out_dir=$1
glaurung_repo=$2
z3_binary=$3
axeyum_binary=$4
driver=$5

expected_glaurung_revision=ff3c0a767a0b085f8552bdb2b363c0b7fa273cbe
expected_z3_binary_sha256=63863636b1cd064c664c593b15a29f9e5ab791b013dbf925666481df1861772a
expected_axeyum_binary_sha256=f4f9312fb0257b0a8f4e2a6422247b7dfc279c1a9b308177fa1b9fda2f1c57a5
expected_driver_sha256=ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
axeyum_repo=$(cd -- "$script_dir/.." && pwd)
measure="$script_dir/measure-glaurung-authoritative-findings.py"
analyze="$script_dir/analyze-glaurung-authority-timeout-policy.py"

for path in "$glaurung_repo" "$z3_binary" "$axeyum_binary" "$driver"; do
    if [[ ! -e "$path" ]]; then
        echo "missing required path: $path" >&2
        exit 2
    fi
done
if [[ ! -x "$z3_binary" || ! -x "$axeyum_binary" ]]; then
    echo "authority binaries must be executable" >&2
    exit 2
fi

observed_glaurung_revision=$(git -C "$glaurung_repo" rev-parse HEAD)
if [[ "$observed_glaurung_revision" != "$expected_glaurung_revision" ]]; then
    echo "unexpected Glaurung revision: $observed_glaurung_revision" >&2
    exit 2
fi
observed_z3_binary_sha256=$(sha256sum "$z3_binary" | awk '{print $1}')
observed_axeyum_binary_sha256=$(sha256sum "$axeyum_binary" | awk '{print $1}')
observed_driver_sha256=$(sha256sum "$driver" | awk '{print $1}')
if [[ "$observed_z3_binary_sha256" != "$expected_z3_binary_sha256" ]]; then
    echo "unexpected Z3 authority binary SHA-256: $observed_z3_binary_sha256" >&2
    exit 2
fi
if [[ "$observed_axeyum_binary_sha256" != "$expected_axeyum_binary_sha256" ]]; then
    echo "unexpected Axeyum authority binary SHA-256: $observed_axeyum_binary_sha256" >&2
    exit 2
fi
if [[ "$observed_driver_sha256" != "$expected_driver_sha256" ]]; then
    echo "unexpected tcpip.sys SHA-256: $observed_driver_sha256" >&2
    exit 2
fi

expected_axeyum_revision=$(git -C "$axeyum_repo" rev-parse HEAD)
if [[ -n $(git -C "$axeyum_repo" status --porcelain --untracked-files=no) ]]; then
    echo "tracked Axeyum source changes make the campaign inadmissible" >&2
    exit 2
fi
if [[ -n $(git -C "$glaurung_repo" status --porcelain --untracked-files=no) ]]; then
    echo "tracked Glaurung source changes make the campaign inadmissible" >&2
    exit 2
fi

mkdir -p "$out_dir"
for policy in any-model min-unsigned; do
    for timeout_ms in 100 250 1000; do
        for suffix in report.json stdout.log stderr.log; do
            path="$out_dir/$policy-${timeout_ms}ms-$suffix"
            if [[ -e "$path" ]]; then
                echo "refusing to overwrite $path" >&2
                exit 2
            fi
        done
    done
done
if [[ -e "$out_dir/analysis.json" ]]; then
    echo "refusing to overwrite $out_dir/analysis.json" >&2
    exit 2
fi

common=(
    --glaurung-repo "$glaurung_repo"
    --z3-binary "$z3_binary"
    --axeyum-binary "$axeyum_binary"
    --driver "$driver"
    --repetitions 3
    --deadline-secs 2400
    --max-analyzed-functions 20
    --solve-budget 400000
    --solve-secs 900
    --process-timeout-secs 2700
    --acceptance-population high-confidence
    --require-deterministic-worklists
)

cell_failures=0
for policy in any-model min-unsigned; do
    for timeout_ms in 100 250 1000; do
        policy_args=()
        if [[ "$policy" == min-unsigned ]]; then
            policy_args=(--concretization-policy min-unsigned)
        fi
        set +e
        python3 "$measure" "${common[@]}" "${policy_args[@]}" \
            --check-timeout-ms "$timeout_ms" \
            --out "$out_dir/$policy-${timeout_ms}ms-report.json" \
            >"$out_dir/$policy-${timeout_ms}ms-stdout.log" \
            2>"$out_dir/$policy-${timeout_ms}ms-stderr.log"
        status=$?
        set -e
        if [[ $status -ne 0 ]]; then
            echo "$policy/${timeout_ms}ms rejected with status $status" >&2
            cell_failures=1
        fi
    done
done

set +e
python3 "$analyze" \
    --report-dir "$out_dir" \
    --expected-axeyum-revision "$expected_axeyum_revision" \
    --out "$out_dir/analysis.json"
analysis_status=$?
set -e
if [[ $cell_failures -ne 0 || $analysis_status -ne 0 ]]; then
    echo "authority timeout/policy campaign rejected; preserve all cell artifacts" >&2
    exit 1
fi

jq -e '
    .schema == "axeyum.glaurung-authority-timeout-policy.v1" and
    .valid == true and
    .high_confidence_parity_all_cells == true and
    (.cells | length) == 6
' "$out_dir/analysis.json" >/dev/null

git -C "$axeyum_repo" status --porcelain --untracked-files=no
sha256sum "$out_dir"/*-report.json "$out_dir/analysis.json"
