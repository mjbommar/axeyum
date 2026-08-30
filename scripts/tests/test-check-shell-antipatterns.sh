#!/usr/bin/env bash
# Controls for `scripts/check-shell-antipatterns.sh`'s `grep -q`-in-pipeline
# detector. It had none, and it was RED on a false positive.
#
# The bug: `||` is not a pipe, but the pattern `\|[^|]*grep -q` matches the
# SECOND bar of a logical OR (the first `|` is followed by `|`, which `[^|]*`
# rejects; the second is followed by a space, which it accepts). So
# `a || grep -q x file` -- reading a FILE, incapable of SIGPIPE -- was reported
# as the banned idiom. Measured 2026-08-30: two false positives across the
# tree, one of them this gate's only ERROR.
#
# Each case runs the REAL detector line, extracted from the shipped script, so a
# control suite cannot drift from the gate it controls. Extraction failure is a
# failure, never a silent pass.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

GATE=scripts/check-shell-antipatterns.sh
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
fail=0
pass=0

# Pull the detector's own `n=$(...)` line out of the gate and reuse it verbatim.
det=$(grep -E '^[[:space:]]*n=\$\(grep -vE' "$GATE" | head -1)
if [ -z "$det" ]; then
  echo "FAIL extraction: no detector line in $GATE -- a suite that cannot find"
  echo "  its subject must not report success."
  exit 1
fi

count_in() {  # $1 = file -> prints the detector's count for it
  local f="$1"
  eval "${det/n=/__n=}"
  printf '%s' "$__n"
}

case_() {  # name, expected-count, body...
  local name="$1" want="$2"; shift 2
  local f="$TMP/$name.sh"
  { echo '#!/usr/bin/env bash'; echo 'set -uo pipefail'; printf '%s\n' "$@"; } > "$f"
  local got; got=$(f="$f"; eval "${det/n=/__n=}"; printf '%s' "$__n")
  if [ "$got" = "$want" ]; then
    pass=$((pass + 1))
  else
    fail=1
    echo "FAIL $name: detector counted $got, expected $want"
    printf '    %s\n' "$@"
  fi
}

# --- POSITIVE: real pipeline consumers MUST still be caught ------------------
# Delete the detector and every one of these dies. These are the reason the gate
# exists: `-q` exits at the first match, SIGPIPEs the producer, and under
# pipefail the pipeline status becomes 141 -- which reads as "not found".
case_ real_pipe            1 'cmd | grep -q pattern'
case_ real_pipe_long_flag  1 'cmd | grep --quiet pattern'
case_ real_pipe_combined   1 "printf '%s\\n' \"\$got\" | grep -qxF \"\$1\""
case_ real_pipe_two        2 'a | grep -q x' 'b | grep -q y'

# --- NEGATIVE: the false positives the fix removes ---------------------------
# `||` is a logical OR. Both sides read a FILE; nothing is piped; no producer
# exists to SIGPIPE. Without the `||` neutralization each of these counts 1.
case_ logical_or           0 'a || grep -q x file'
case_ logical_or_absolute  0 '   || /usr/bin/grep -q "pat" "$TMP/out"'
case_ logical_or_both      0 'grep -q A "$S" || ! grep -q B "$S"'

# --- NEGATIVE: shapes that were never the idiom ------------------------------
case_ plain_file_read      0 'grep -q pattern file'
case_ and_list             0 'a && grep -q x file'
case_ comment_only         0 '# cmd | grep -q pattern'

# --- MIXED: an OR and a real pipe on separate lines. Guards against a fix that
# --- neutralizes `||` by dropping the whole line.
case_ or_plus_real_pipe    1 'a || grep -q x file' 'b | grep -q y'

# --- The gate itself must be green on the real tree, and say so. -------------
if ! out=$(timeout 300 bash "$GATE" 2>&1); then
  fail=1
  echo "FAIL gate_green_on_real_tree: $GATE exited nonzero"
  printf '%s\n' "$out" | tail -3
else
  pass=$((pass + 1))
fi

if [ "$fail" -ne 0 ]; then
  echo "SHELL_ANTIPATTERN_CONTROLS|FAILED"
  exit 1
fi
echo "SHELL_ANTIPATTERN_CONTROLS|cases=$((pass))|positive=4|negative=6|PASS"
