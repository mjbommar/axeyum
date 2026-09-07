#!/usr/bin/env bash
# Corpus sweep for the `trusted=` field. Prints one TSV row per file plus a
# summary whose EXIT STATUS depends on the finding: a nonzero exit when any file
# reports a verdict that contradicts its declared `:status`, so a clean run is a
# live check and not a decoration.
set -uo pipefail

CLI="$1"
LIST="$2"
LIMIT="${3:-50}"
BUDGET_MS="${4:-10000}"

contradictions=0
files=0
unsat=0
with_step=0
modulo=0

while IFS= read -r f; do
  [ -n "$f" ] || continue
  [ -r "$f" ] || continue
  files=$((files + 1))
  [ "$files" -gt "$LIMIT" ] && break
  declared=$(grep -m1 ':status' "$f" | sed -n 's/.*:status[[:space:]]*\([a-z]*\).*/\1/p')
  out=$(timeout -k 2 30s "$CLI" --evidence --timeout-ms "$BUDGET_MS" "$f" 2>/dev/null)
  verdict=$(printf '%s\n' "$out" | grep -v '^;' | tail -1)
  line=$(printf '%s\n' "$out" | grep -m1 '^; evidence')
  trusted=$(printf '%s\n' "$line" | sed -n 's/.*trusted=\([^ ]*\).*/\1/p')
  kind=$(printf '%s\n' "$line" | sed -n 's/.*kind=\([^ ]*\).*/\1/p')
  ms=$(printf '%s\n' "$line" | sed -n 's/.*ms=\([^ ]*\).*/\1/p')
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$(basename "$f")" "${declared:-none}" \
    "${verdict:-none}" "${kind:-none}" "${trusted:-none}" "${ms:-none}"
  case "$verdict" in
    unsat) unsat=$((unsat + 1)) ;;
  esac
  case "$trusted" in
    ""|none|0) : ;;
    *) with_step=$((with_step + 1))
       case "$trusted" in
         *sat-refutation-modulo-theory*) modulo=$((modulo + 1)) ;;
       esac ;;
  esac
  if [ -n "$declared" ] && [ "$declared" != "unknown" ] && [ -n "$verdict" ] \
     && [ "$verdict" != "unknown" ] && [ "$verdict" != "$declared" ]; then
    contradictions=$((contradictions + 1))
    printf 'CONTRADICTION\t%s\tdeclared=%s\tgot=%s\n' "$f" "$declared" "$verdict" >&2
  fi
done < "$LIST"

echo "SUMMARY|files=$((files > LIMIT ? LIMIT : files))|unsat=$unsat|trusted_nonzero=$with_step|modulo_theory=$modulo|contradictions=$contradictions"
[ "$contradictions" -eq 0 ] || exit 1
