#!/usr/bin/env bash
# Mutation-verify every guard in scripts/lib/module_baseline.py and
# scripts/check-module-baseline.py: delete one guard at a time in a SCRATCH
# copy (never the tracked worktree files -- CLAUDE.md's mutation-in-shared-
# checkout warning applies even to a lane's own tree if another process reads
# it mid-mutation) and require EXACTLY ONE test in
# scripts/tests/test-module-baseline.py to die.
#
# Usage: scripts/tests/test-module-baseline-mutations.sh
#
# Exits 0 iff every mutation kills exactly one test and the unmutated
# baseline is fully green. Prints a guard -> outcome table.
#
# Mutations are applied by exact literal Python str.replace (not sed/regex):
# sed's BRE-vs-ERE parenthesis escaping cost real time to get right here, and
# a literal string match/replace with a count check is unambiguous.
set -u
set -o pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRATCH="${TMPDIR:-/tmp}/module-baseline-mutations-${AXEYUM_AGENT:-unknown}-$$"
mkdir -p "$SCRATCH"
trap 'rm -rf "$SCRATCH"' EXIT

TEST_SUITE="$REPO_ROOT/scripts/tests/test-module-baseline.py"

fresh_copy() {
    rm -rf "$SCRATCH/copy"
    mkdir -p "$SCRATCH/copy/lib"
    cp "$REPO_ROOT/scripts/lib/module_baseline.py" "$SCRATCH/copy/lib/module_baseline.py"
    cp "$REPO_ROOT/scripts/gen-module-baseline.py" "$SCRATCH/copy/gen-module-baseline.py"
    cp "$REPO_ROOT/scripts/check-module-baseline.py" "$SCRATCH/copy/check-module-baseline.py"
}

# Apply an EXACT literal replacement (must occur exactly once) to a file.
mutate_literal() {
    local file="$1" search="$2" replace="$3"
    python3 - "$file" "$search" "$replace" <<'PYEOF'
import sys
path, search, replace = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(path, encoding="utf-8").read()
count = text.count(search)
if count != 1:
    print(f"MUTATE_LITERAL_ERROR|count={count}|expected=1", file=sys.stderr)
    sys.exit(3)
open(path, "w", encoding="utf-8").write(text.replace(search, replace, 1))
PYEOF
}

echo "== baseline (no mutation) =="
fresh_copy
BASELINE_STDOUT="$SCRATCH/baseline_stdout.txt"
python3 "$TEST_SUITE" \
    --lib "$SCRATCH/copy/lib/module_baseline.py" \
    --gen "$SCRATCH/copy/gen-module-baseline.py" \
    --check "$SCRATCH/copy/check-module-baseline.py" \
    >"$BASELINE_STDOUT" 2>"$SCRATCH/baseline_stderr.txt"
baseline_rc=$?
baseline_failed=$(/usr/bin/grep -c 'verdict=FAIL' "$BASELINE_STDOUT")
echo "baseline: rc=$baseline_rc failed=$baseline_failed"
if [ "$baseline_rc" -ne 0 ] || [ "$baseline_failed" -ne 0 ]; then
    echo "MUTATION_HARNESS|verdict=FAIL|reason=BASELINE_NOT_GREEN"
    cat "$SCRATCH/baseline_stderr.txt" >&2
    exit 1
fi

overall_rc=0
table_rows=()

apply_and_test() {
    # $1 = guard name, $2 = target file (lib|check), $3 = search, $4 = replace
    local guard="$1" target_key="$2" search="$3" replace="$4"
    fresh_copy
    local target_file
    case "$target_key" in
        lib) target_file="$SCRATCH/copy/lib/module_baseline.py" ;;
        check) target_file="$SCRATCH/copy/check-module-baseline.py" ;;
        *) echo "unknown target $target_key" >&2; exit 2 ;;
    esac

    if ! mutate_literal "$target_file" "$search" "$replace" 2>"$SCRATCH/mutate_${guard}.err"; then
        echo "$guard|NOT_APPLIED ($(cat "$SCRATCH/mutate_${guard}.err"))"
        table_rows+=("$guard|NOT_APPLIED")
        overall_rc=1
        return
    fi

    local out="$SCRATCH/mut_${guard}.stdout"
    local err="$SCRATCH/mut_${guard}.stderr"
    python3 "$TEST_SUITE" \
        --lib "$SCRATCH/copy/lib/module_baseline.py" \
        --gen "$SCRATCH/copy/gen-module-baseline.py" \
        --check "$SCRATCH/copy/check-module-baseline.py" \
        >"$out" 2>"$err"
    local rc=$?

    if [ "$rc" -eq 2 ]; then
        echo "$guard|DID_NOT_BUILD"
        table_rows+=("$guard|DID_NOT_BUILD")
        overall_rc=1
        return
    fi

    local total
    total=$(/usr/bin/grep -c '^TEST|' "$out")
    if [ "$total" -eq 0 ]; then
        echo "$guard|DID_NOT_RUN (zero tests collected)"
        table_rows+=("$guard|DID_NOT_RUN")
        overall_rc=1
        return
    fi

    local newly_failed
    newly_failed=$(/usr/bin/grep '^TEST|.*verdict=FAIL' "$out" | sed -E 's/^TEST\|name=([a-zA-Z0-9_]+).*/\1/')
    local n_failed
    n_failed=$(echo "$newly_failed" | /usr/bin/grep -c . || true)

    if [ "$n_failed" -eq 1 ]; then
        echo "$guard|killed:$newly_failed"
        table_rows+=("$guard|killed:$newly_failed")
    elif [ "$n_failed" -eq 0 ]; then
        echo "$guard|SURVIVED (no test died)"
        table_rows+=("$guard|SURVIVED")
        overall_rc=1
    else
        echo "$guard|killed multiple: $(echo "$newly_failed" | tr '\n' ',')"
        table_rows+=("$guard|killed_multiple:$(echo "$newly_failed" | tr '\n' ',')")
        overall_rc=1
    fi
}

echo "== mutations =="

apply_and_test \
    "M1_comment_string_stripping" lib \
    'stripped = strip_comments_and_strings(text)' \
    'stripped = text  # MUTATED'

apply_and_test \
    "M2_internal_external_split" lib \
    'if target in module_set:' \
    'if True:  # MUTATED'

apply_and_test \
    "M3_sink_count" lib \
    'no_importer_sinks = sorted(m for m in modules if indeg.get(m, 0) == 0)' \
    'no_importer_sinks = []  # MUTATED'

apply_and_test \
    "M4_tie_break_indegree_only" lib \
    'top_indegree = sorted(indeg.items(), key=lambda kv: (-kv[1], kv[0]))' \
    'top_indegree = sorted(indeg.items(), key=lambda kv: (-kv[1],))  # MUTATED'

apply_and_test \
    "M5a_missing_directory_guard" lib \
    'if not mathlib_dir.is_dir():' \
    'if False:  # MUTATED'

apply_and_test \
    "M5b_no_mathlib_subdir_guard" lib \
    'if not (mathlib_dir / "Mathlib").is_dir():' \
    'if False:  # MUTATED'

apply_and_test \
    "M5c_empty_source_guard" lib \
    'if len(modules) == 0:' \
    'if False:  # MUTATED'

apply_and_test \
    "M7_source_drift_detection" check \
    '    if source_mismatch:' \
    '    source_mismatch = False  # MUTATED
    if source_mismatch:'

apply_and_test \
    "M8_parser_drift_detection" check \
    'parser_mismatch = committed_parser.get("sha256") != fresh_parser.get("sha256")' \
    'parser_mismatch = False  # MUTATED'

echo
echo "== summary table (guard|outcome) =="
for row in "${table_rows[@]}"; do
    echo "$row"
done

if [ "$overall_rc" -eq 0 ]; then
    echo "MUTATION_HARNESS|verdict=PASS|guards=${#table_rows[@]}|all_killed_exactly_one=true"
else
    echo "MUTATION_HARNESS|verdict=FAIL|guards=${#table_rows[@]}|see rows above"
fi
exit "$overall_rc"
