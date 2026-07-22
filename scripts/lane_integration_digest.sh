#!/usr/bin/env bash
# Integrator read-only digest across the concurrent agent lanes.
#
# Companion to docs/contributor-guide/multi-agent-operations.md and the running
# log docs/plan/multiagent-integration-diary-2026-07-22.md. Prints, per lane:
# commits ahead of main, last-commit age, uncommitted WIP (read-only status),
# and an in-memory merge preview vs main (git merge-tree — touches no worktree).
# Then host health: /tmp + /nas4 usage, solver runaways, package temp.
#
# READ-ONLY by contract: it never builds, stashes, checks out, or resets any
# agent worktree (that would compile another lane's half-written WIP and steal
# CPU/heat). Green-verification of a branch happens only in a scratch worktree
# or the integration lane, never here.
#
# Usage:  scripts/lane_integration_digest.sh [integration-repo-path]
# Env:    LANES="name:branch:worktree,..."  overrides the default lane table.
set -u

R="${1:-$HOME/projects/personal/axeyum}"

# Default lane table: name : branch : worktree
DEFAULT_LANES="\
lean:agent/lean/nested-inductive-elimination:$HOME/projects/personal/axeyum-lean-nested,\
smtcomp:agent/smtcomp/full-library-resume:$HOME/projects/personal/axeyum-smtcomp,\
cas:agent/cas/vandermonde-wz:/nas4/data/workspace-infosec/claude-axeyum-cas-work"
LANES="${LANES:-$DEFAULT_LANES}"

main_short=$(git -C "$R" rev-parse --short main 2>/dev/null)
printf '════ LANE DIGEST — main @ %s (%s) ════\n' \
  "$main_short" "$(git -C "$R" log -1 --format='%cr' main 2>/dev/null)"

IFS=',' read -ra rows <<<"$LANES"
for row in "${rows[@]}"; do
  IFS=':' read -r name br wt <<<"$row"
  # Agents switch topic branches per milestone (e.g. CAS: vandermonde-wz →
  # falling-moment-order-* → raw-moment-order-*). Derive the LIVE branch from the
  # worktree HEAD rather than trusting the seed name, so the digest never watches
  # a dead branch. Falls back to the seed if detached/unavailable.
  livebr=$(git -C "$wt" branch --show-current 2>/dev/null)
  [ -n "$livebr" ] && br="$livebr"
  ahead=$(git -C "$R" rev-list --count "main..$br" 2>/dev/null)
  last=$(git -C "$R" log -1 --format='%cr' "$br" 2>/dev/null)
  wip=$(git -C "$wt" status --porcelain 2>/dev/null | grep -c .)
  # in-memory 3-way merge preview; count conflicted paths (line 1 is the tree OID)
  conf=$(git -C "$R" merge-tree --write-tree --name-only main "$br" 2>/dev/null \
           | sed -n '2,$p' | grep -c .)
  mergemsg=$([ "${conf:-0}" = 0 ] && echo CLEAN || echo "${conf} conflict-file(s)")
  flag=$([ "${ahead:-0}" -gt 0 ] && echo '← NEW WORK' || echo '')
  printf '\n[%s] %s\n   ahead=%s  last=%s  uncommitted=%s  merge-vs-main=%s  %s\n' \
    "$name" "$br" "${ahead:-?}" "${last:-never}" "${wip:-?}" "$mergemsg" "$flag"
  [ "${ahead:-0}" -gt 0 ] && \
    git -C "$R" log --format='     • %h %s (%cr)' "main..$br" 2>/dev/null | head -3
done

echo ""
echo "──── host health ────"
printf 'disk: %s /tmp, %s /nas4\n' \
  "$(df -h /tmp 2>/dev/null | awk 'NR==2{print $5}')" \
  "$(df -h /nas4 2>/dev/null | awk 'NR==2{print $5}')"
# Match actual solver runaways, not watchers that merely mention the worktree
# path: exclude pgrep itself, this digest, and the branch-agnostic monitor (whose
# command line contains the `.../axeyum-smtcomp` worktree path + its HEAD loop).
runaways=$(pgrep -af 'compete\.py|axeyum-smtcomp' 2>/dev/null \
             | grep -vcE 'pgrep|lane_integration_digest|rev-parse HEAD|HEADMOVE|declare -A WT')
printf 'solver runaways: %s%s\n' "$runaways" \
  "$([ "$runaways" -gt 0 ] && echo '  ⚠ stop via scripts/smtcomp_repro/stop_run.sh' || echo '')"
if command -v sensors >/dev/null 2>&1; then
  printf 'temp: %s\n' "$(sensors 2>/dev/null \
    | awk '/Package id 0:|Tctl:/{for(i=1;i<=NF;i++)if($i~/^\+[0-9]/){print $i;break}}' \
    | tr '\n' ' ')"
fi
