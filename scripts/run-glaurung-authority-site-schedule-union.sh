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
expected_glaurung_revision=e98c0902d8f232dee8cd6348cffab79dade3eec7
expected_driver_sha256=ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
axeyum_repo=$(cd -- "$script_dir/.." && pwd)
measure="$script_dir/measure-glaurung-authoritative-findings.py"
analyze="$script_dir/analyze-glaurung-authority-site-schedule-union.py"

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
observed_driver_sha256=$(sha256sum "$driver" | awk '{print $1}')
if [[ "$observed_driver_sha256" != "$expected_driver_sha256" ]]; then
    echo "unexpected tcpip.sys SHA-256: $observed_driver_sha256" >&2
    exit 2
fi

mkdir -p "$out_dir"
for name in \
    any-model-report.json any-model.stdout.log any-model.stderr.log \
    min-unsigned-report.json min-unsigned.stdout.log min-unsigned.stderr.log \
    max-unsigned-report.json max-unsigned.stdout.log max-unsigned.stderr.log \
    site-hash-0-report.json site-hash-0.stdout.log site-hash-0.stderr.log \
    site-hash-1-report.json site-hash-1.stdout.log site-hash-1.stderr.log \
    site-schedule-union-report.json; do
    if [[ -e "$out_dir/$name" ]]; then
        echo "refusing to overwrite $out_dir/$name" >&2
        exit 2
    fi
done

common=(
    --glaurung-repo "$glaurung_repo"
    --z3-binary "$z3_binary"
    --axeyum-binary "$axeyum_binary"
    --driver "$driver"
    --repetitions 3
    --deadline-secs 1800
    --max-analyzed-functions 15
    --solve-budget 300000
    --solve-secs 300
    --process-timeout-secs 1800
    --check-timeout-ms 250
)

set +e
python3 "$measure" "${common[@]}" \
    --out "$out_dir/any-model-report.json" \
    >"$out_dir/any-model.stdout.log" \
    2>"$out_dir/any-model.stderr.log"
any_status=$?
set -e
if [[ $any_status -eq 0 ]]; then
    echo "any-model control unexpectedly reached exact authority parity" >&2
    exit 1
fi
jq -e '
    .schema == "axeyum.glaurung-authoritative-finding-parity.v4" and
    .accepted == false and
    .drivers[0].summary.within_backend_stable == true and
    .drivers[0].summary.exact_finding_parity == false and
    .drivers[0].summary.backends.z3.findings_sha256 ==
        "c371df518511ddeac8523e4fea672062ff5e8e7d9916158e15a9cd2836922804" and
    .drivers[0].summary.backends.axeyum.findings_sha256 ==
        "a67d7bca28602ab20bbc46d9a5d42705463bd340067dc8e6ec660b35d58ba265" and
    (.drivers[0].summary.z3_only | length) == 2 and
    (.drivers[0].summary.axeyum_only | length) == 0
' "$out_dir/any-model-report.json" >/dev/null

for policy in min-unsigned max-unsigned site-hash-0 site-hash-1; do
    python3 "$measure" "${common[@]}" \
        --canonical-model-choice "$policy" \
        --out "$out_dir/$policy-report.json" \
        >"$out_dir/$policy.stdout.log" \
        2>"$out_dir/$policy.stderr.log"
done
jq -e '
    .accepted == true and
    .drivers[0].summary.backends.z3.findings_sha256 ==
        "e657ea6be385ba32b2aec6e49f2a780ec7f80850eb3105dc750fce74810d438e" and
    .drivers[0].summary.backends.axeyum.findings_sha256 ==
        "e657ea6be385ba32b2aec6e49f2a780ec7f80850eb3105dc750fce74810d438e"
' "$out_dir/min-unsigned-report.json" >/dev/null
jq -e '
    .accepted == true and
    .drivers[0].summary.backends.z3.findings_sha256 ==
        "ceb7789a3a20100c1f8e12566779a832b1093aa89687ebf3f2fa3d54dff2e01d" and
    .drivers[0].summary.backends.axeyum.findings_sha256 ==
        "ceb7789a3a20100c1f8e12566779a832b1093aa89687ebf3f2fa3d54dff2e01d"
' "$out_dir/max-unsigned-report.json" >/dev/null

python3 "$analyze" \
    --any-model-report "$out_dir/any-model-report.json" \
    --min-report "$out_dir/min-unsigned-report.json" \
    --max-report "$out_dir/max-unsigned-report.json" \
    --site-hash-zero-report "$out_dir/site-hash-0-report.json" \
    --site-hash-one-report "$out_dir/site-hash-1-report.json" \
    --out "$out_dir/site-schedule-union-report.json"

jq -e '
    .schema == "axeyum.glaurung-authority-site-schedule-union.v1" and
    .accepted == true and
    .four_schedule_union.exact_authority_parity == true
' "$out_dir/site-schedule-union-report.json" >/dev/null

git -C "$axeyum_repo" status --porcelain --untracked-files=no
sha256sum \
    "$out_dir/any-model-report.json" \
    "$out_dir/min-unsigned-report.json" \
    "$out_dir/max-unsigned-report.json" \
    "$out_dir/site-hash-0-report.json" \
    "$out_dir/site-hash-1-report.json" \
    "$out_dir/site-schedule-union-report.json"
