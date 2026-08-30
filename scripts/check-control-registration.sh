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
#
# ---------------------------------------------------------------------------
# 2026-08-27: THE PYTHON HALF NO LONGER RATCHETS A NUMBER.
#
# It used to. `PY_ORPHAN_BASELINE=188` pinned the count of Python suites no
# caller named, so the gate went red when a NEW orphan appeared and stayed green
# over the standing 188 -- 49% of the corpus, permanently invisible, at a floor
# nobody chose. It accumulated one lane at a time and the ratchet was set to
# whatever the number happened to be the day it was written.
#
# That is the defect this file exists to prevent, arriving one level out. Three
# orphans appeared on 2026-08-27 and all three were checks written THAT DAY to
# close real defects, including the replacement for a pair of tests that could
# not fail.
#
# The floor is gone. Registration is now DERIVED: `scripts/run-python-controls.py`
# discovers every `scripts/tests/test_*.py`, subtracts the suites a caller names
# by hand and the reasoned exclusions in `scripts/control-optout.tsv`, and runs
# the rest. So a new Python control runs the moment it is committed, with no
# registration step to forget.
#
# What this gate checks is therefore no longer "how many are unnamed" (zero, by
# construction) but that the CONSTRUCTION IS INTACT:
#
#   G1  the catch-all runner is itself invoked by a caller. If it is not, every
#       suite falls through it and the whole scheme is inert -- the exact
#       failure this file is about, so it is checked FIRST and by an
#       independent grep rather than by asking the runner.
#   G2  a hyphenated `.py` under scripts/tests/ must be invoked BY PATH by
#       something real. Originally this rejected every hyphenated name
#       outright, reasoning that `test_*.py` discovery cannot see a hyphen AND
#       that a hyphenated name is not an importable module. MEASURED
#       2026-08-30: the second half is FALSE. `python3 -m unittest
#       scripts.tests.check-foo` DOES import the file -- `__import__`/
#       `importlib.import_module` resolve a dotted path by matching FILE NAMES
#       on disk, and only the `import` STATEMENT's parser enforces the
#       identifier restriction. What actually happens with the four scripts
#       this was written against is stranger than "cannot run": none is a
#       `unittest.TestCase`, each is a standalone script that calls
#       `sys.exit(0)`/`sys.exit(1)` at module level, so the IMPORT ITSELF
#       terminates the whole `python3` process before unittest's loader ever
#       builds or runs a TestSuite (confirmed by the absence of any "Ran N
#       tests" line, and by reproducing the identical exit with a bare
#       `importlib.import_module(...)` and no unittest involved at all). That
#       invocation form is not "unittest discovered and ran a test"; it is
#       "importing the file executes it as a script and its own exit code
#       escapes before unittest does anything," and nothing should rely on it.
#
#       What DOES make a hyphenated `.py` reachable is the same thing that
#       already justifies a hyphenated `.sh`: invocation BY PATH, from CALLERS
#       or from a fact's `checker_command`. `scripts/check-fact-evidence-replay.sh`
#       (registered in scripts/check.sh and the justfile) executes every
#       `proved`/`computed`/`refuted`/`axiom` fact's literal `checker_command`
#       string, and 3 of the 4 scripts this guard was written against are
#       cited that way by 7 `proved` facts -- a real caller, exercised on
#       every `just check`, invisible to this gate only because it never read
#       `artifacts/facts/*.json`. So: fine if invoked by path from CALLERS or a
#       fact; still rejected if invoked by nothing (the property is
#       reachability, not the hyphen itself). `.sh` controls keep their
#       separate, pre-existing check below -- hyphens are their convention and
#       all 20 are registered via CALLERS.
#   G3  every opt-out entry names a file that exists (a stale exclusion hides
#       nothing and misstates the corpus).
#   G4  every opt-out entry carries a reason.
#   G5  no suite is both opted out and named by a caller.
#   G6  the opt-out list does not grow silently (ratchet, as before -- but now
#       over 19 NAMED entries a reader can argue with, not an anonymous 188).
#   G7  this gate's own partition agrees with the runner's. Two independent
#       implementations of "which suites are covered"; a disagreement means one
#       of them is wrong, and neither can be trusted to audit itself.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

# Where a control may be claimed from. `hooks/pre-push` counts: it is a real
# caller even though it is not the aggregate gate.
CALLERS=(scripts/check.sh justfile hooks/pre-push .github/workflows)

RUNNER=scripts/run-python-controls.py
OPTOUT=scripts/control-optout.tsv

# G6. A ratchet over the opt-out list. Every entry is a written liability;
# adding one must be deliberate, and removing one is a RESULT that lowers this.
OPTOUT_CEILING=${AXEYUM_CONTROL_OPTOUT_CEILING:-15}

rc=0

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

callers_text=$(for c in "${CALLERS[@]}"; do
    [ -e "$c" ] || continue
    if [ -d "$c" ]; then cat "$c"/* 2>/dev/null; else sed 's/^[[:space:]]*#.*$//' "$c"; fi
  done)

# --- G1: is the catch-all runner itself invoked? -----------------------------
# Checked before anything else and WITHOUT asking the runner, because if the
# answer is no then every number the runner reports is about work that never
# happens. `grep -c` for the SIGPIPE reason above.
runner_named=$(printf '%s' "$callers_text" | grep -cF "$RUNNER")
if [ "${runner_named:-0}" -eq 0 ]; then
  echo "CONTROL_REGISTRATION_ERROR|$RUNNER is invoked by no caller, so every" \
       "python control it would run is inert. Registration is DERIVED from that" \
       "script; if nothing calls it, nothing calls them. Add it as a step in" \
       "scripts/check.sh and the justfile's check recipe." >&2
  rc=1
fi

# --- G2: hyphenated .py controls must be invoked BY PATH ---------------------
# A fact's checker_command is a real caller (scripts/check-fact-evidence-replay.sh
# executes every settled fact's checker_command verbatim, and it is itself
# registered in CALLERS' scripts/check.sh and the justfile) -- see the header
# comment above for the measurement that made this a reachability check rather
# than a blanket rejection.
FACTS_GLOB="${AXEYUM_FACTS_GLOB:-artifacts/facts/*.json}"
facts_text=$(cat $FACTS_GLOB 2>/dev/null)

hyphen_py=()
for f in scripts/tests/*.py; do
  [ -e "$f" ] || continue
  b=$(basename "$f")
  case "$b" in *-*) : ;; *) continue ;; esac
  by_path=$(printf '%s' "$callers_text" | grep -cF "scripts/tests/$b")
  by_path=$((by_path + $(printf '%s' "$facts_text" | grep -cF "scripts/tests/$b")))
  [ "${by_path:-0}" -eq 0 ] && hyphen_py+=("$b")
done
if [ "${#hyphen_py[@]}" -gt 0 ]; then
  for h in "${hyphen_py[@]}"; do
    echo "CONTROL_REGISTRATION_ERROR|scripts/tests/$h is a hyphenated .py control" \
         "invoked by NOTHING: not named by path in scripts/check.sh, the" \
         "justfile, hooks/pre-push, .github/workflows, or any fact's" \
         "checker_command. Either invoke it by path from one of those (the same" \
         "convention a .sh control already uses) or rename it with underscores" \
         "and register it as a discoverable test_*.py suite. (Note:" \
         "\`python3 -m unittest scripts.tests.${h%.py}\` is NOT a fix -- see the" \
         "header comment on why that invocation form does not actually run it" \
         "as a test.)" >&2
  done
  rc=1
fi

# --- G3/G4/G5: the opt-out list ----------------------------------------------
py_optout=0
optout_names=()
if [ ! -e "$OPTOUT" ]; then
  echo "CONTROL_REGISTRATION_ERROR|$OPTOUT is missing; it is the authority for" \
       "which python controls are deliberately not run" >&2
  exit 1
fi
lineno=0
while IFS= read -r line || [ -n "$line" ]; do
  lineno=$((lineno + 1))
  case "$line" in ''|'#'*) continue ;; esac
  name=${line%%$'\t'*}
  reason=${line#*$'\t'}
  if [ "$name" = "$line" ]; then
    echo "CONTROL_REGISTRATION_ERROR|$OPTOUT:$lineno: no TAB. Every exclusion" \
         "needs \`name<TAB>reason\` -- a name without a reason is the anonymous" \
         "numeric floor again with extra steps." >&2
    rc=1
    continue
  fi
  # G4: reason must be non-blank.
  if [ -z "${reason//[[:space:]]/}" ]; then
    echo "CONTROL_REGISTRATION_ERROR|$OPTOUT:$lineno: $name has no reason" >&2
    rc=1
  fi
  # G3: the file must exist.
  if [ ! -e "scripts/tests/$name.py" ]; then
    echo "CONTROL_REGISTRATION_ERROR|$OPTOUT:$lineno: $name does not exist." \
         "Delete the line: a stale exclusion hides nothing and misstates the corpus." >&2
    rc=1
  fi
  # G5: opted out AND named by a caller is a contradiction -- one of the two is
  # a lie about whether this suite runs.
  claimed=$(printf '%s' "$callers_text" | grep -cF "scripts.tests.$name")
  claimed=$((claimed + $(printf '%s' "$callers_text" | grep -cF "scripts/tests/$name.py")))
  if [ "$claimed" -gt 0 ]; then
    echo "CONTROL_REGISTRATION_ERROR|$OPTOUT:$lineno: $name is opted OUT here and" \
         "named by a caller. It cannot be both excluded and run; delete one." >&2
    rc=1
  fi
  optout_names+=("$name")
  py_optout=$((py_optout + 1))
done < "$OPTOUT"

# --- the partition, computed HERE, independently of the runner ---------------
py_total=0
py_named=0
py_mine=()
for f in scripts/tests/test_*.py; do
  [ -e "$f" ] || continue
  b=$(basename "$f" .py)
  py_total=$((py_total + 1))
  # BOTH invocation forms count. A suite run as `python3 scripts/tests/x.py` is
  # just as run as one named `python3 -m unittest scripts.tests.x`, and counting
  # only the module form reported 217 orphans against a true 199 -- an 18-suite
  # overcount that would have been written down as a finding.
  named=$(printf '%s' "$callers_text" | grep -cF "scripts.tests.$b")
  named=$((named + $(printf '%s' "$callers_text" | grep -cF "scripts/tests/$b.py")))
  if [ "$named" -gt 0 ]; then
    py_named=$((py_named + 1))
    continue
  fi
  excluded=0
  for o in ${optout_names[@]+"${optout_names[@]}"}; do
    [ "$o" = "$b" ] && excluded=1 && break
  done
  [ "$excluded" = 0 ] && py_mine+=("$b")
done
if [ "$py_total" -lt 50 ]; then
  echo "CONTROL_REGISTRATION_ERROR|found only $py_total python suite(s); the glob" \
       "is looking at the wrong place and an empty corpus would pass vacuously" >&2
  exit 1
fi

# Everything is named, run by the catch-all, or excluded with a reason. This is
# true by construction, which is the point of the redesign -- so it is printed,
# not celebrated, and the guards that can actually fail are G1-G7.
py_orphans=0

echo "CONTROL_REGISTRATION|controls=$total|orphans=${#orphans[@]}|py_controls=$py_total|py_orphans=$py_orphans|py_named=$py_named|py_catchall=${#py_mine[@]}|py_optout=$py_optout|py_optout_ceiling=$OPTOUT_CEILING"

if [ "${#orphans[@]}" -gt 0 ]; then
  for o in "${orphans[@]}"; do
    echo "CONTROL_REGISTRATION_ERROR|$o is run by nothing. Register it as a" \
         "\`step\` in scripts/check.sh (and the justfile's \`check\` recipe if" \
         "it belongs in the aggregate gate). A control nobody invokes cannot" \
         "fail, so it is not a control" >&2
  done
  rc=1
fi

# --- G6: the opt-out ratchet, both directions --------------------------------
if [ "$py_optout" -gt "$OPTOUT_CEILING" ]; then
  echo "CONTROL_REGISTRATION_ERROR|python control opt-outs ROSE" \
       "$OPTOUT_CEILING -> $py_optout. Excluding a control from the catch-all is" \
       "a decision: raise OPTOUT_CEILING in this file and say why in the commit." >&2
  rc=1
fi
if [ "$py_optout" -lt "$OPTOUT_CEILING" ]; then
  echo "CONTROL_REGISTRATION_ERROR|python control opt-outs FELL" \
       "$OPTOUT_CEILING -> $py_optout. That is a result: lower OPTOUT_CEILING" \
       "to $py_optout." >&2
  rc=1
fi

# --- G7: cross-check the partition against the runner's own -------------------
# Two independent implementations. The runner decides what to RUN; this gate
# decides what SHOULD be run. If they disagree, at least one is wrong, and the
# failure mode a single implementation cannot detect is exactly the one this
# whole file exists for -- a set that silently shrinks.
if [ -x "$RUNNER" ] || [ -e "$RUNNER" ]; then
  runner_list=$(python3 "$RUNNER" --list 2>/dev/null | sort)
  gate_list=$(printf '%s\n' ${py_mine[@]+"${py_mine[@]}"} | sort)
  if [ "$runner_list" != "$gate_list" ]; then
    echo "CONTROL_REGISTRATION_ERROR|the catch-all set this gate computes" \
         "(${#py_mine[@]}) differs from what $RUNNER --list reports. One of the" \
         "two partitions is wrong; they are deliberately separate implementations." >&2
    diff <(printf '%s\n' "$gate_list") <(printf '%s\n' "$runner_list") | head -20 >&2
    rc=1
  fi
else
  echo "CONTROL_REGISTRATION_ERROR|$RUNNER does not exist" >&2
  rc=1
fi

[ "$rc" -eq 0 ] || exit 1

echo "  all $total control script(s) are invoked by a gate"
echo "  $py_total python control(s): $py_named named by a step, ${#py_mine[@]} run by" \
     "the catch-all, $py_optout excluded with a written reason"
