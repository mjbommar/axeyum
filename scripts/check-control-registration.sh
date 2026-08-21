#!/usr/bin/env bash
# Every control script must be RUN by something. A control nobody invokes is
# indistinguishable from a control that does not exist.
#
# This repository has been bitten by the same shape four separate ways -- a
# corpus gate that ran zero tests for 15 days, a pre-push hook that had never
# run because `core.hooksPath` was unset, three axiom-freedom examples cited by
# two ADRs and invoked by nothing, and a `--features full` suite that compiled
# to an empty binary. Each time the artifact was correct and reachable by hand;
# what was missing was a caller.
#
# Measured 2026-08-19, the same hole was open here: `scripts/tests/` held 8
# control scripts and `test-check-lean-golden-pins.sh` was referenced by no
# gate at all. It passes -- 6 assertions, all green -- and had passed unnoticed
# since it landed the day before, because registration in `check.sh` is a
# separate manual step from writing the test, and nothing checked it happened.
#
# So: the registry is derived from the filesystem, not maintained by hand. A new
# `scripts/tests/*.sh` is red until some gate names it.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

# Where a control may be claimed from. `hooks/pre-push` counts: it is a real
# caller even though it is not the aggregate gate.
CALLERS=(scripts/check.sh justfile hooks/pre-push .github/workflows)

orphans=()
total=0
for f in scripts/tests/*.sh; do
  [ -e "$f" ] || continue
  total=$((total + 1))
  base=$(basename "$f")
  found=0
  for c in "${CALLERS[@]}"; do
    [ -e "$c" ] || continue
    # COMMENTS ARE NOT CALLERS. Found the day this gate landed: a `# Control:
    # scripts/tests/test-...sh` line in `hooks/pre-push` satisfied a plain
    # `grep -F`, so a control that nothing ran reported as registered -- this
    # gate failing in exactly the way it exists to prevent. Cross-referencing a
    # control from a comment is good practice and must stay possible; it just
    # must not COUNT. Strip whole-line comments before looking.
    #
    # `grep -c`, NOT `grep -q`, and the difference is not style. This script
    # runs under `set -o pipefail`, and `grep -q` exits the instant it matches
    # -- which SIGPIPEs the producer, making the pipeline status 141. Under
    # pipefail that reads as "not found", so a MATCH was being reported as an
    # orphan. It was worse than a plain wrong answer: whether the producer had
    # finished writing before the consumer exited depends on buffering, so the
    # same tree reported 7 orphans on one run and 3 on the next. `grep -c`
    # consumes all of its input and cannot SIGPIPE.
    hits=$(grep -rhv -e '^[[:space:]]*#' "$c" 2>/dev/null | grep -cF "$base")
    if [ "${hits:-0}" -gt 0 ]; then
      found=1
      break
    fi
  done
  [ "$found" = 0 ] && orphans+=("$f")
done

# A ratchet whose corpus is empty passes for the wrong reason. This one has been
# non-empty since the directory existed; if it ever reads as empty, the glob is
# broken or the directory moved, and that must be loud rather than green.
if [ "$total" -lt 5 ]; then
  echo "CONTROL_REGISTRATION_ERROR|found only $total control script(s) under" \
       "scripts/tests/; the glob is looking at the wrong place and an empty" \
       "corpus would make this gate pass vacuously" >&2
  exit 1
fi

echo "CONTROL_REGISTRATION|controls=$total|orphans=${#orphans[@]}"
if [ "${#orphans[@]}" -gt 0 ]; then
  for o in "${orphans[@]}"; do
    echo "CONTROL_REGISTRATION_ERROR|$o is run by nothing. Register it as a" \
         "\`step\` in scripts/check.sh (and the justfile's \`check\` recipe if" \
         "it belongs in the aggregate gate). A control nobody invokes cannot" \
         "fail, so it is not a control" >&2
  done
  exit 1
fi
echo "  all $total control script(s) are invoked by a gate"
