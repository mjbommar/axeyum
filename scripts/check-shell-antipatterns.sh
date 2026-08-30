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
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

BASELINE="scripts/check-shell-antipatterns.baseline"
fail=0
tmp=$(mktemp); trap 'rm -f "$tmp"' EXIT

# --- pattern 1: `grep -q` piped, in a script that sets pipefail --------------
for f in $(git ls-files '*.sh'); do
  [ -e "$f" ] || continue
  # THIS FILE IS EXCLUDED, and not to spare itself: its own detection regexes
  # and its own error messages contain the literal patterns, so scanning itself
  # reports 2 `grep -q` uses and a `$?`-after-pipeline that do not exist as code.
  # A linter that matches its own pattern strings is reporting on its source
  # text, not on behaviour. Measured the moment the gate first ran in CI.
  [ "$f" = "scripts/check-shell-antipatterns.sh" ] && continue
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
done | LC_ALL=C sort > "$tmp"

# --- pattern 2: `$?` after a pipeline on one line ----------------------------
# Zero today, so this one IS enforced at zero.
pipe_status=0
for f in $(git ls-files '*.sh'); do
  [ -e "$f" ] || continue
  [ "$f" = "scripts/check-shell-antipatterns.sh" ] && continue
  n=$(grep -vE '^[[:space:]]*#' "$f" | grep -cE '\|.*;[[:space:]]*(echo|printf)[^;]*\$\?')
  if [ "$n" -gt 0 ]; then
    echo "SHELL_ANTIPATTERN_ERROR|$f reads \$? after a pipeline ($n occurrence(s));" \
         "that is the LAST stage's status, not the command you meant" >&2
    pipe_status=$((pipe_status + n))
  fi
done
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
echo "SHELL_ANTIPATTERNS|files=$(wc -l < "$tmp")|grep_q_in_pipeline=$total|pipeline_status_reads=$pipe_status"
exit "$fail"
