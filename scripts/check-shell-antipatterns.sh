#!/usr/bin/env bash
# Ban the shell idioms that print a WRONG ANSWER while exiting 0.
#
# CLAUDE.md lists six; two are mechanically detectable in tracked scripts and
# this gate pins them. Both were real defects here on 2026-08-20, not theory:
#
#   `grep -q` as a pipeline consumer under `set -o pipefail`
#       `-q` exits at the first match, SIGPIPEs the producer, and the pipeline
#       status becomes 141 -- which pipefail reads as "no match". Whether the
#       producer finished writing first depends on buffering, so the SAME
#       unchanged tree reported 7 orphans on one run and 3 on the next in
#       `check-control-registration.sh`. `grep -c` consumes all input and
#       cannot SIGPIPE.
#
#   `$?` read immediately after a pipeline
#       `$?` is the LAST stage. `… | tail -12; echo "exit=$?"` printed `exit=0`
#       for a script that exits 1.
#
# # Why a pinned baseline rather than zero
#
# Sixteen occurrences of the first pattern already exist across eight files, and
# most belong to other lanes. A gate that is red from the day it lands is a gate
# people learn to ignore -- this repository has said so about `local-ci-freshness`
# in its own comments. So the known set is pinned BY FILE AND COUNT: a new file
# fails, and an increased count in a known file fails. Burning the baseline down
# is a fall, which is a result to publish, not a regression.
#
# The DETECTOR had this bug too, on its first run: `[^|]*[[:space:]]-[a-zA-Z]*q`
# matched the ` -eq` in `[ "$(… | grep -c …)" -eq 0 ]`, flagging a line that had
# just been FIXED to use `grep -c`. The `q` must be a grep flag, so it is
# anchored to `grep` with only flag characters between.
#
# # What is SCANNED, and why `git ls-files '*.sh'` was not it
#
# Until 2026-08-30 the scan set was `git ls-files '*.sh'`, so the two tracked
# shell scripts WITHOUT that extension were never read -- and both violated:
#
#   hooks/commit-msg:36  head -1 "$f" | grep -qiE '^(merge|revert|…)'
#   hooks/pre-push:249   printf '%s\n' "$out" | grep -qE '^running [1-9]'
#
# The second is the nonzero-test-count guard this repository leans on hardest,
# built from the exact idiom that reads a SIGPIPE as "no match". Both were
# fail-closed -- a spurious refusal, not an admitted bad commit or push -- and
# both are now fixed. `hooks/` is executable shell that gates every push, so
# "out of scope" was a defect in the scope, not a design decision.
#
# The set is now DERIVED: every tracked file whose first line is a `sh`/`bash`
# shebang, plus every `*.sh` (a sourced fragment may have no shebang). Deriving
# it is the rule CLAUDE.md states for any check named "every X" -- ask the
# authority, do not maintain a literal -- and it is why a third extensionless
# hook added tomorrow is scanned without anyone remembering to list it.
set -uo pipefail
# `AXEYUM_SHELL_ANTIPATTERN_ROOT` points the SHIPPED script at a throwaway git
# repository, so `scripts/tests/test_check_shell_antipatterns_scope.py` can drive
# each scope guard to failure without re-implementing the enumeration. Same
# device as `AXEYUM_KERNEL_SUITES_ROOT`; unset in every real run.
cd "${AXEYUM_SHELL_ANTIPATTERN_ROOT:-$(dirname "$0")/..}" || exit 2

BASELINE="scripts/check-shell-antipatterns.baseline"
fail=0
tmp=$(mktemp); trap 'rm -f "$tmp" "$scanned"' EXIT

# `--list-scanned` prints the derived scan set and exits. It exists so a control
# can assert WHICH files are scanned rather than only how many -- a widening
# that silently reverts leaves every count in the summary unchanged.
list_only=0
[ "${1:-}" = "--list-scanned" ] && list_only=1

# Both thresholds are overridable ONLY so the controls can drive each guard to
# failure on a tree where it would otherwise never fire. Nothing in the
# repository sets them; the defaults are the gate.
MIN_SCAN="${AXEYUM_SHELL_ANTIPATTERN_MIN_SCAN:-100}"
REQUIRED="${AXEYUM_SHELL_ANTIPATTERN_REQUIRED:-hooks/pre-push hooks/commit-msg}"

# The derived scan set, computed once, in ONE python process.
#
# The first draft shelled out per tracked file. That is 14,342 files and two
# subprocesses each, and the gate went from ~2 s to over two minutes -- which
# matters because the controls run it seven times. Reading the first line of
# each candidate in-process is the same measurement at a thousandth of the cost.
#
# `git ls-files -s` carries the index MODE, so the shebang probe only has to
# consider files git records as executable (688 here, against 14,342). A
# non-executable shell fragment is still scanned when it ends in `*.sh`, which
# is every sourced fragment in this tree.
scanned=$(mktemp)
git ls-files -s | python3 -c '
import re, sys, pathlib

# `#!/bin/sh`, `#!/usr/bin/env bash`, `#!/bin/bash -e`, `#!/usr/bin/zsh`.
SHEBANG = re.compile(rb"^#!.*[ /](ba|da|k|z)?sh( |$)")

out = set()
for raw in sys.stdin.buffer:
    # <mode> <sha> <stage>\t<path>
    head, _, path = raw.partition(b"\t")
    path = path.rstrip(b"\n").decode("utf-8", "surrogateescape")
    if not path:
        continue
    if path.endswith(".sh"):
        out.add(path)
        continue
    if not head.startswith(b"100755 "):
        continue
    try:
        with open(path, "rb") as fh:
            first = fh.readline(200)
    except OSError:
        # Tracked but absent from the worktree (a lane mid-rebase).
        continue
    if SHEBANG.match(first.rstrip(b"\r\n") + b"\n") or SHEBANG.match(first):
        out.add(path)

for path in sorted(out):
    print(path)
' > "$scanned"

scan_count=$(wc -l < "$scanned")
if [ "$list_only" -eq 1 ]; then
  cat "$scanned"
  exit 0
fi
# A scan set that has collapsed means the enumeration broke, not that the tree
# became clean -- the failure mode every count-based gate in this repository has
# had at least once. There have been >200 tracked shell scripts since this gate
# was written.
if [ "$scan_count" -lt "$MIN_SCAN" ]; then
  echo "SHELL_ANTIPATTERN_ERROR|the scan set collapsed to $scan_count file(s);" \
       "the enumeration is broken, not the tree" >&2
  exit 1
fi
# The two extensionless hooks are the reason this gate's scope changed, so their
# presence is asserted rather than hoped for: if the shebang probe stops finding
# them, the widening has silently reverted and nobody would see it in the count.
for required in $REQUIRED; do
  if [ "$(grep -cxF "$required" "$scanned")" -eq 0 ]; then
    echo "SHELL_ANTIPATTERN_ERROR|$required is tracked shell and is NOT in the" \
         "scan set; the shebang probe has regressed" >&2
    exit 1
  fi
done

# --- pattern 1: `grep -q` piped, in a script that sets pipefail --------------
while IFS= read -r f; do
  # THIS FILE IS EXCLUDED, and not to spare itself: its own detection regexes
  # and its own error messages contain the literal patterns, so scanning itself
  # reports 2 `grep -q` uses and a `$?`-after-pipeline that do not exist as code.
  # A linter that matches its own pattern strings is reporting on its source
  # text, not on behaviour. Measured the moment the gate first ran in CI.
  [ "$f" = "scripts/check-shell-antipatterns.sh" ] && continue
  # ITS CONTROLS ARE EXCLUDED FOR THE SAME REASON, and it is the reason one line
  # above: a suite proving this detector catches `cmd | grep -q x` has to
  # CONTAIN `cmd | grep -q x`. All six hits in that file are single-quoted
  # arguments to its `case_` helper -- fixture data, never executed. Read every
  # one before excluding; a real pipeline there would be a genuine finding.
  #
  # The cost, stated rather than hidden: a real `| grep -q` written into the
  # controls file later would not be flagged. Bounded -- it is a hundred lines
  # of fixtures, and it exercises the detector directly, so it can conceal a bug
  # in itself but never a bug in the detector.
  [ "$f" = "scripts/tests/test-check-shell-antipatterns.sh" ] && continue
  # `grep -c`, deliberately: this gate must not contain the bug it bans.
  [ "$(grep -cE 'set -[a-z]*o pipefail' "$f")" -gt 0 ] || continue
  # Whole-line comments are prose, not code: a commented-out example must not
  # count, the same rule `check-control-registration.sh` needed.
  # `||` IS NOT A PIPE, and the first version of this detector could not tell.
  # `a || grep -q x file` contains a `|` followed by a non-`|`, so the pattern
  # `\|[^|]*grep -q` matched the SECOND bar of a logical OR. Measured
  # 2026-08-30: two false positives, and one of them was this gate's only
  # ERROR -- `test-creal-prelude-build-ratio.sh:178`,
  # `|| /usr/bin/grep -q "..." "$TMP/out"`, which reads a FILE and cannot
  # SIGPIPE anything. The gate had been red on it.
  #
  # Neutralize `||` first, then look for a real pipe. Verified surgical: of the
  # eight files with any hit, six counts are byte-identical before and after,
  # `test-creal-prelude-build-ratio.sh` goes 1 -> 0 and `test-local-ci-record.sh`
  # 2 -> 1 -- and that file's surviving hit is the genuine one
  # (`printf ... | grep -qxF`), while the removed one was
  # `grep -q ... "$SCRIPT" || ! grep -q ... "$SCRIPT"`.
  n=$(grep -vE '^[[:space:]]*#' "$f" | sed 's/||/ __OR__ /g' | grep -cE '\|[^|]*grep[[:space:]]+(-[a-zA-Z]*q|--quiet)')
  [ "$n" -gt 0 ] && printf '%s %s\n' "$f" "$n"
done < "$scanned" | LC_ALL=C sort > "$tmp"

# --- pattern 2: `$?` after a pipeline on one line ----------------------------
# Zero today, so this one IS enforced at zero.
pipe_status=0
while IFS= read -r f; do
  [ "$f" = "scripts/check-shell-antipatterns.sh" ] && continue
  # ITS CONTROLS ARE EXCLUDED FOR THE SAME REASON, and it is the reason one line
  # above: a suite proving this detector catches `cmd | grep -q x` has to
  # CONTAIN `cmd | grep -q x`. All six hits in that file are single-quoted
  # arguments to its `case_` helper -- fixture data, never executed. Read every
  # one before excluding; a real pipeline there would be a genuine finding.
  #
  # The cost, stated rather than hidden: a real `| grep -q` written into the
  # controls file later would not be flagged. Bounded -- it is a hundred lines
  # of fixtures, and it exercises the detector directly, so it can conceal a bug
  # in itself but never a bug in the detector.
  [ "$f" = "scripts/tests/test-check-shell-antipatterns.sh" ] && continue
  n=$(grep -vE '^[[:space:]]*#' "$f" | grep -cE '\|.*;[[:space:]]*(echo|printf)[^;]*\$\?')
  if [ "$n" -gt 0 ]; then
    echo "SHELL_ANTIPATTERN_ERROR|$f reads \$? after a pipeline ($n occurrence(s));" \
         "that is the LAST stage's status, not the command you meant" >&2
    pipe_status=$((pipe_status + n))
  fi
done < "$scanned"
[ "$pipe_status" -gt 0 ] && fail=1

if [ ! -f "$BASELINE" ]; then
  echo "SHELL_ANTIPATTERN_ERROR|$BASELINE is missing; without it this gate" \
       "cannot fail and is not a gate" >&2
  exit 1
fi

# A baseline that has gone empty means the glob broke, not that the tree is
# clean: this pattern has been non-empty since the gate was written.
if [ ! -s "$BASELINE" ]; then
  echo "SHELL_ANTIPATTERN_ERROR|$BASELINE is empty; a vacuous baseline passes" \
       "for the wrong reason" >&2
  exit 1
fi

while read -r file count; do
  [ -n "$file" ] || continue
  was=$(awk -v f="$file" '$1==f{print $2}' "$BASELINE")
  if [ -z "$was" ]; then
    echo "SHELL_ANTIPATTERN_ERROR|$file: NEW file using \`grep -q\` in a pipeline" \
         "under pipefail ($count). Use \`grep -c\` and test the count -- see" \
         "CLAUDE.md, banned shell idioms." >&2
    fail=1
  elif [ "$count" -gt "$was" ]; then
    echo "SHELL_ANTIPATTERN_ERROR|$file: \`grep -q\`-in-pipeline count ROSE" \
         "$was -> $count" >&2
    fail=1
  elif [ "$count" -lt "$was" ]; then
    echo "  improvement: $file $was -> $count (update $BASELINE to lock it in)"
  fi
done < "$tmp"

total=$(awk '{s+=$2} END{print s+0}' "$tmp")
# `scanned` is in the summary because the scope is the thing that silently
# regressed: a widening that reverts leaves every other number unchanged.
echo "SHELL_ANTIPATTERNS|scanned=$scan_count|files=$(wc -l < "$tmp")|grep_q_in_pipeline=$total|pipeline_status_reads=$pipe_status"
exit "$fail"
