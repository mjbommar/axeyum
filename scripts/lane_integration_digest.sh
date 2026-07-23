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

# Lane table: name:branch:worktree. Auto-DISCOVERED from `git worktree list` for
# any branch under refs/heads/agent/* — so a new agent worktree (e.g. the Lean
# lane spinning up axeyum-lean-parity for its next round) or a topic-branch switch
# is picked up with no edit here. Override with LANES=... if needed.
if [ -z "${LANES:-}" ]; then
  LANES=$(git -C "$R" worktree list --porcelain 2>/dev/null | awk '
    /^worktree /{p=$2} /^branch /{b=$2}
    /^$/{ if(b ~ /refs\/heads\/agent\//){ sub(/refs\/heads\//,"",b); n=p; sub(/.*\//,"",n); print n":"b":"p } p="";b="" }
    END{ if(b ~ /refs\/heads\/agent\//){ sub(/refs\/heads\//,"",b); n=p; sub(/.*\//,"",n); print n":"b":"p } }' \
    | paste -sd,)
fi

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
# NOTE: the worktrees live under ~/projects on the ROOT fs (/), NOT the NAS.
# `df /nas4` resolves to / (only /nas4/DATA is the 28T NAS mount) — so the disk
# that actually fills from Rust target/ dirs is /, and that is what we flag.
printf 'disk: %s / (root: worktrees+target/, avail %s), %s /nas4/data (NAS 28T), %s /tmp\n' \
  "$(df -h / 2>/dev/null | awk 'NR==2{print $5}')" \
  "$(df -h / 2>/dev/null | awk 'NR==2{print $4}')" \
  "$(df -h /nas4/data 2>/dev/null | awk 'NR==2{print $5}')" \
  "$(df -h /tmp 2>/dev/null | awk 'NR==2{print $5}')"
# Match ONLY genuine solver runaways: the distributed runner (compete.py) or the
# harness-STAGED solver binary running unbounded. Deliberately NOT `axeyum-smtcomp`
# anywhere in the path — that matched every lane build/test binary under the
# `.../axeyum-smtcomp` worktree (cargo_mir_build, rustc, target-codex/deps/…) and
# every shell/monitor carrying the worktree path in its args. The real §4 hazard
# is a `compete.py` orphan or the /harness/bin/ staged binary; those match here.
runaways=$(pgrep -af 'compete\.py|/harness/[^ ]*axeyum-smtcomp' 2>/dev/null \
             | grep -vcE 'shell-snapshots|snapshot-bash|pgrep|lane_integration_digest|[[:space:]]git[[:space:]]')
printf 'solver runaways: %s%s\n' "$runaways" \
  "$([ "$runaways" -gt 0 ] && echo '  ⚠ stop via scripts/smtcomp_repro/stop_run.sh' || echo '')"
if command -v sensors >/dev/null 2>&1; then
  printf 'temp: %s\n' "$(sensors 2>/dev/null \
    | awk '/Package id 0:|Tctl:/{for(i=1;i<=NF;i++)if($i~/^\+[0-9]/){print $i;break}}' \
    | tr '\n' ' ')"
fi
