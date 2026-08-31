#!/usr/bin/env bash
# Controls for scripts/lane-merge-resolve.py. One case per failure that has
# actually happened, plus a mutation table proving each guard is load-bearing.
#
# Case 1 IS the 2026-08-30 incident: a conflicted JSON object resolved by
# keeping both sides, producing text that does not parse. The merge commit was
# already made and nothing in `git status` or `git show --stat` showed it.
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
SCRIPT="$ROOT/scripts/lane-merge-resolve.py"
PASS=0; FAIL=0
say() { printf '  %-46s %s\n' "$1" "$2"; }

# A throwaway repo with a real conflict -- never the shared checkout.
fixture() { # $1 = filename  $2 = base  $3 = ours  $4 = theirs
  D=$(mktemp -d); cd "$D" || exit 1
  git init -q . && git config user.email t@t && git config user.name t
  printf '%s' "$2" > "$1"; git add -A >/dev/null; git commit -qm base
  git checkout -q -b theirs; printf '%s' "$4" > "$1"; git commit -qam theirs
  git checkout -q master 2>/dev/null || git checkout -q main
  printf '%s' "$3" > "$1"; git commit -qam ours
  git merge --no-edit theirs >/dev/null 2>&1
  echo "$D"
}

check() { # name  expected_exit  expected_grep  file  base ours theirs  [script]
  local name="$1" want="$2" pat="$3" f="$4" S="${8:-$SCRIPT}"
  local D; D=$(fixture "$f" "$5" "$6" "$7")
  ( cd "$D" && python3 "$S" > out.txt 2>&1; echo $? > code.txt )
  local got; got=$(cat "$D/code.txt")
  local body; body=$(cat "$D/out.txt")
  if [ "$got" = "$want" ] && printf '%s' "$body" | /usr/bin/grep -qE "$pat"; then
    say "$name" "ok"; PASS=$((PASS+1))
  else
    say "$name" "FAIL (exit $got want $want)"; printf '%s\n' "$body" | head -4 | sed 's/^/        /'
    FAIL=$((FAIL+1))
  fi
  rm -rf "$D"
}

J_BASE='{"note":"n","rows":[{"id":"a","v":1}]}'
J_OURS='{"note":"n","amendments":[{"id":"x","v":9}],"rows":[{"id":"a","v":1}]}'
J_THEIRS='{"note":"n","rows":[{"id":"a","v":1},{"id":"b","v":2}]}'

cd "$ROOT" || exit 1
echo "TEST-LANE-MERGE-RESOLVE"

# 1. THE INCIDENT: JSON must be merged structurally, and the result must parse.
D=$(fixture cfg.json "$J_BASE" "$J_OURS" "$J_THEIRS")
( cd "$D" && python3 "$SCRIPT" >/dev/null 2>&1 )
if python3 -c "import json,sys;d=json.load(open('$D/cfg.json'));
sys.exit(0 if len(d['rows'])==2 and 'amendments' in d else 1)" 2>/dev/null; then
  say "json merged structurally and parses" "ok"; PASS=$((PASS+1))
else
  say "json merged structurally and parses" "FAIL"; FAIL=$((FAIL+1))
fi
rm -rf "$D"

# 2. A scalar the two sides disagree on has no rule -- refuse, do not pick.
check "json scalar disagreement refused" 1 'disagree|REFUSED' cfg.json \
  '{"k":1}' '{"k":2}' '{"k":3}'

# 3. Rust cut mid-item: keeping both sides would not compile.
# 2b. THE 2026-08-31 RATCHET: two lanes each land facts, so BOTH raise
# `coverage_floor.min_identity_bound` correctly against their own bases, and the
# pair conflicts. It only ever moves up, so max is the answer -- and the VALUE
# matters, not just the exit code, so this case asserts 102 rather than trusting
# "merged structurally". Hand-resolved twice before it was automated.
D=$(fixture floor.json \
  '{"coverage_floor":{"min_identity_bound":100,"max_header_exempt":5},"pins":[]}' \
  '{"coverage_floor":{"min_identity_bound":102,"max_header_exempt":5},"pins":[]}' \
  '{"coverage_floor":{"min_identity_bound":101,"max_header_exempt":5},"pins":[]}')
( cd "$D" && python3 "$SCRIPT" >/dev/null 2>&1 )
if python3 -c "import json,sys;d=json.load(open('$D/floor.json'));
sys.exit(0 if d['coverage_floor']['min_identity_bound']==102 else 1)" 2>/dev/null; then
  say "ratchet floor takes the max" "ok"; PASS=$((PASS+1))
else
  say "ratchet floor takes the max" "FAIL"; FAIL=$((FAIL+1))
fi
rm -rf "$D"

# 2c. AND THE RULE MUST NOT LEAK. A `max_*` floor has no fixed direction --
# `max_header_exempt` was deliberately RAISED 30 -> 67 once -- so it must still
# refuse. Without this, the narrow rule could be widened to all of
# `coverage_floor` and nothing would die.
check "non-min floor key still refused" 1 'disagree|REFUSED' floor2.json \
  '{"coverage_floor":{"max_header_exempt":30},"pins":[]}' \
  '{"coverage_floor":{"max_header_exempt":67},"pins":[]}' \
  '{"coverage_floor":{"max_header_exempt":40},"pins":[]}'

check "rust cut mid-item refused" 1 'cut mid-item|REFUSED' a.rs \
'fn base() {}
' 'fn base() {}
pub fn mine(
' 'fn base() {}
pub fn theirs(
'

# 4. Genuinely additive text keeps both sides.
check "additive markdown keeps both" 0 'kept both' n.md \
'# t
' '# t
- mine
' '# t
- theirs
'


# 5-6. THE SECOND INCIDENT: both sides edited the SAME definition line. Keeping
# both leaves two, which balances perfectly and breaks the consumer.
# 4b. THE 2026-08-31 INCIDENT: two lanes rewrote the SAME prose paragraph.
# Keeping both concatenated two drafts of one paragraph, and the stale half --
# asserting a row was ABSENT hours after it landed -- survived into a commit
# and was read as current. Prose is not additive; a bullet list is. This case
# and the one above must therefore disagree, which is the whole point.
check "markdown prose paragraph refused" 1 'PROSE on both sides|REFUSED' p.md \
'# t

The original paragraph said one thing.
' '# t

Ours rewrote the paragraph and it now says
something quite different from before.
' '# t

Theirs rewrote the same paragraph and it says
a third thing that contradicts ours.
'

check "justfile duplicate recipe refused" 1 'both sides define|REFUSED' justfile \
'check: a b
    echo hi
' 'check: a b module-baseline
    echo hi
' 'check: a b kernel-differential
    echo hi
'

check "shell duplicate assignment refused" 1 'both sides define|REFUSED' g.sh \
'FLOOR=100
' 'FLOOR=230
' 'FLOOR=261
'

# --- mutations: each guard must be killed by exactly one case ---------------
echo "  mutations (each must kill exactly one case):"
# Each entry is NAME|FROM|TO|EXPECTED_KILLS. The expectation is per-mutation
# because the fixture list is shared: `json_no_parse` disables JSON handling
# entirely, so it necessarily kills BOTH json fixtures (cfg.json and floor2.json).
# The invariant this table enforces is that removing a guard is DETECTED and that
# guards do not all reject through one shared check -- not that exactly one test
# dies regardless of how many fixtures exercise the same code path.
for m in "json_no_parse|resolve_json|CUT|2" "balance_off|if cut:|if False and cut:|1" "dupdef_off|if dupes:|if False and dupes:|1" "prose_off|if prose:|if False and prose:|1" "ratchet_leak|startswith(\"min_\")|startswith(\"\")|1"; do
  NAME="${m%%|*}"; REST="${m#*|}"; FROM="${REST%%|*}"; REST="${REST#*|}"
  TO="${REST%|*}"; WANT="${REST##*|}"
  T=$(mktemp -d); cp "$SCRIPT" "$T/mutant.py"
  if [ "$TO" = "CUT" ]; then
    python3 - "$T/mutant.py" <<'PY'
import sys,re
p=sys.argv[1]; s=open(p).read()
s=s.replace('if ext == ".json":','if False:',1)
open(p,"w").write(s)
PY
  else
    python3 - "$T/mutant.py" "$FROM" "$TO" <<'PY'
import sys
p,f,t=sys.argv[1:4]; s=open(p).read(); open(p,"w").write(s.replace(f,t,1))
PY
  fi
  KILLED=0
  D=$(fixture cfg.json "$J_BASE" "$J_OURS" "$J_THEIRS")
  ( cd "$D" && python3 "$T/mutant.py" >/dev/null 2>&1 )
  python3 -c "import json;json.load(open('$D/cfg.json'))" 2>/dev/null || KILLED=$((KILLED+1))
  rm -rf "$D"
  D=$(fixture justfile 'check: a
' 'check: a m
' 'check: a k
')
  ( cd "$D" && python3 "$T/mutant.py" >/dev/null 2>&1; echo $? > c )
  [ "$(cat "$D/c")" != "1" ] && KILLED=$((KILLED+1))
  rm -rf "$D"
  D=$(fixture a.rs 'fn b(){}
' 'fn b(){}
pub fn m(
' 'fn b(){}
pub fn t(
')
  ( cd "$D" && python3 "$T/mutant.py" >/dev/null 2>&1; echo $? > c )
  [ "$(cat "$D/c")" != "1" ] && KILLED=$((KILLED+1))
  rm -rf "$D"
  # The prose fixture: both sides are multi-line running prose, i.e. two drafts
  # of one paragraph. Without this the prose guard has nothing that kills it and
  # could be deleted with the suite still green -- the exact failure this file
  # exists to prevent.
  D=$(fixture p.md '# t

One original sentence here.
' '# t

Ours rewrote this paragraph and it
now reads quite differently.
' '# t

Theirs rewrote the same paragraph and it
reads a third way entirely.
')
  ( cd "$D" && python3 "$T/mutant.py" >/dev/null 2>&1; echo $? > c )
  [ "$(cat "$D/c")" != "1" ] && KILLED=$((KILLED+1))
  rm -rf "$D"
  # A `max_*` floor must still refuse. Widening the ratchet rule to every
  # `coverage_floor` key makes this resolve silently, which would pick a
  # direction for an allowance that has none.
  D=$(fixture floor2.json \
    '{"coverage_floor":{"max_header_exempt":30},"pins":[]}' \
    '{"coverage_floor":{"max_header_exempt":67},"pins":[]}' \
    '{"coverage_floor":{"max_header_exempt":40},"pins":[]}')
  ( cd "$D" && python3 "$T/mutant.py" >/dev/null 2>&1; echo $? > c )
  [ "$(cat "$D/c")" != "1" ] && KILLED=$((KILLED+1))
  rm -rf "$D" "$T"
  if [ "$KILLED" = "$WANT" ]; then
    say "    $NAME" "killed exactly $WANT"; PASS=$((PASS+1))
  else
    say "    $NAME" "FAIL (killed $KILLED, want $WANT)"; FAIL=$((FAIL+1))
  fi
done

echo "TEST_LANE_MERGE_RESOLVE|pass=$PASS|fail=$FAIL"
[ "$FAIL" = 0 ] || exit 1
