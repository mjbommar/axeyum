#!/usr/bin/env bash
# Do the two "same" aggregate gates actually run the same steps?
#
# CLAUDE.md calls `just check` the preferred gate and `./scripts/check.sh` "the
# same aggregate gate without just"; `check.sh`'s own header says it "mirrors the
# check recipe in the justfile; keep the two in sync". Measured 2026-08-14 they
# ran 112 and 61 steps respectively, and each was missing something the other
# had — `check.sh` had no axiom-ledger check (the SHA-256 binding of all 65
# prelude axiom types, and axiom-freedom is the project's headline metric), while
# `just check` had no `check-gate-liveness.sh` (the ratchet that exists because a
# corpus sweep ran zero tests for 15 days).
#
# Hand-syncing two lists is what produced that. This gate does not sync them: it
# MEASURES the divergence, prints it, and fails when it GROWS. Every accepted
# difference is written down in `scripts/check-aggregate-scope.expected` with the
# side it lives on, so "these two gates differ" stops being invisible.
#
# Usage:
#   scripts/check-aggregate-scope.sh            # check (fails on NEW divergence)
#   scripts/check-aggregate-scope.sh --update   # rewrite the expectation file
#
# Method note worth keeping: `just -n` writes the expanded recipe to STDERR, so
# `just -n check 2>/dev/null | wc -l` reports 0 steps and looks like a clean
# result. This script uses `2>&1`.
set -uo pipefail

# `comm` and `sort` must agree on collation, or `comm` silently reports garbage
# and warns to stderr where a piped gate never sees it.
export LC_ALL=C

cd "$(dirname "$0")/.." || exit 2

expected_file="scripts/check-aggregate-scope.expected"
mode="check"
while [ $# -gt 0 ]; do
  case "$1" in
    --update) mode="update"; shift ;;
    # Used by the negative control to point the gate at a doctored expectation.
    --expected) expected_file="${2:-}"; shift 2 ;;
    *) echo "check-aggregate-scope: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

command -v just >/dev/null 2>&1 || {
  echo "check-aggregate-scope: \`just\` is not installed, so the justfile side of" \
       "the comparison cannot be read. Not a pass — nothing was compared." >&2
  exit 2
}

# Normalize away what is NOT a scope difference, so what remains is a real
# difference in WHAT is checked:
#   * a `MEM_LIMIT_GB=N ./scripts/mem-run.sh` wrapper (a memory cap, not a step)
#   * leading environment assignments (`RUSTDOCFLAGS=...`)
#   * `./` prefixes and whitespace runs
#   * `python3 -m unittest` with several targets, which one side writes as one
#     step over 18 files and the other as 18 steps -- split into one line each,
#     and `scripts/tests/x.py` and `scripts.tests.x` folded to the same key
normalize() {
  python3 -c '
import re, sys

def strip_wrappers(line):
    line = line.strip()
    while re.match(r"^[A-Za-z_][A-Za-z0-9_]*=(\"[^\"]*\"|\S+)\s", line):
        line = line.split(" ", 1)[1].strip()
    # `./` is a path prefix wherever it appears, not only at line start:
    # `scripts/check.sh` writes `python3 ./scripts/x.py` while the justfile
    # writes `python3 scripts/x.py`. An anchored `^\./` sees those as two
    # different steps and reports ONE script as TWO divergences, once on each
    # side -- which is what it did for `check-autogenesis-already-proved` and
    # `check-test-attribute-integrity` after both were correctly added to the
    # justfile. `(^|\s)` keeps `../` safe (its second char is `.`, not `/`).
    line = re.sub(r"(^|\s)\./", r"\1", line)
    line = re.sub(r"^scripts/mem-run\.sh\s+", "", line)
    line = re.sub(r"^[A-Za-z_][A-Za-z0-9_]*=(\"[^\"]*\"|\S+)\s+", "", line)
    line = re.sub(r"^\./", "", line)
    return re.sub(r"\s+", " ", line).strip()

def module(target):
    target = re.sub(r"\.py$", "", target)
    return target.replace("/", ".")

out = set()
for raw in sys.stdin:
    # `just -n` echoes comments that live INSIDE a recipe body, and this
    # normalizer used to accept them as steps. The `facts` recipe has four such
    # lines, so this gate reported four prose sentences as gate blind spots and
    # failed on `main` -- while the divergence it exists to measure was fine.
    if raw.lstrip().startswith("#"):
        continue
    line = strip_wrappers(raw)
    if not line:
        continue
    match = re.match(r"^python3 -m unittest (.+)$", line)
    if match:
        for target in match.group(1).split():
            out.add("python3 -m unittest " + module(target))
    else:
        out.add(line)
for line in sorted(out):
    print(line)
'
}

sh_steps="$(mktemp)"; just_steps="$(mktemp)"; actual="$(mktemp)"
trap 'rm -f "$sh_steps" "$just_steps" "$actual"' EXIT

AXEYUM_CHECK_LIST=1 ./scripts/check.sh 2>/dev/null | cut -f2- | normalize > "$sh_steps"
# 2>&1: `just -n` prints the expansion to stderr.
just -n check 2>&1 | normalize > "$just_steps"

sh_count=$(wc -l < "$sh_steps")
just_count=$(wc -l < "$just_steps")

if [ "$sh_count" -eq 0 ] || [ "$just_count" -eq 0 ]; then
  echo "check-aggregate-scope: one side enumerated ZERO steps (check.sh $sh_count," \
       "just $just_count) — the enumeration is broken, not the gates." >&2
  exit 2
fi

{
  comm -23 "$sh_steps" "$just_steps" | sed 's/^/check.sh-only: /'
  comm -13 "$sh_steps" "$just_steps" | sed 's/^/just-only:     /'
} | sort > "$actual"

divergence=$(wc -l < "$actual")

echo "check-aggregate-scope: check.sh runs $sh_count steps, \`just check\` runs $just_count;" \
     "$divergence step(s) exist on one side only"

if [ "$mode" = "update" ]; then
  {
    echo "# Accepted divergence between ./scripts/check.sh and \`just check\`."
    echo "# Regenerate with: scripts/check-aggregate-scope.sh --update"
    echo "# A step listed here runs on ONE side only. Removing an entry (making the"
    echo "# two agree) is always fine; ADDING one is a new blind spot in whichever"
    echo "# gate a contributor happens to run, so the gate fails until it is recorded"
    echo "# here deliberately."
    cat "$actual"
  } > "$expected_file"
  echo "check-aggregate-scope: recorded $divergence divergent step(s) in $expected_file"
  exit 0
fi

if [ ! -f "$expected_file" ]; then
  echo "check-aggregate-scope: no $expected_file — run with --update to record the" \
       "current divergence." >&2
  exit 1
fi

accepted="$(mktemp)"; new="$(mktemp)"; resolved="$(mktemp)"
trap 'rm -f "$sh_steps" "$just_steps" "$actual" "$accepted" "$new" "$resolved"' EXIT
grep -v '^#' "$expected_file" | grep -v '^[[:space:]]*$' | sort > "$accepted"
comm -23 "$actual" "$accepted" > "$new"
comm -13 "$actual" "$accepted" > "$resolved"

if [ -s "$resolved" ]; then
  echo "check-aggregate-scope: $(wc -l < "$resolved") recorded difference(s) no longer" \
       "exist (the two gates agree about them now); re-run with --update to drop them:"
  sed 's/^/    /' "$resolved"
fi

if [ -s "$new" ]; then
  echo "check-aggregate-scope: $(wc -l < "$new") step(s) run on only ONE side and are" \
       "not recorded as accepted:" >&2
  sed 's/^/    /' "$new" >&2
  echo "check-aggregate-scope: whoever runs the other gate does not get these checks." >&2
  echo "  Either add the step to both, or record it deliberately with --update." >&2
  exit 1
fi

echo "check-aggregate-scope: all $divergence difference(s) are recorded in $expected_file"
