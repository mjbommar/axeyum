#!/usr/bin/env bash
# Extract a commit into a private, attributable, correctly-stamped build tree.
#
# WHY THIS EXISTS. "Build from your own `git archive HEAD` snapshot" is standing
# advice in this repository -- it is how a lane gets isolation in a shared
# checkout without `git stash` or `git checkout`, both of which destroy other
# lanes' uncommitted work. The advice is right. The recipe everyone types is not:
#
#   1. `mktemp -d` lands in /tmp, which HERE IS A 62 G tmpfs -- i.e. RAM.
#      Measured 2026-08-15: /tmp at 81% (50 G), Shmem 45.1 G of a 123 G box,
#      MemAvailable 57 G. Fifteen abandoned axeyum snapshots were holding 9.3 GB
#      of RAM between them, four of them 15-20 h old. A tmpfs page is not
#      reclaimable under pressure the way page cache is, so this is a direct
#      contributor to the OOM kills that have taken out sessions on this box --
#      and `git archive` of this repo is ~640 MB a time.
#   2. `tar -x` without `--touch` stamps every file with the COMMIT time. Cargo
#      decides freshness by mtime, so extracting an EARLIER commit into a warm
#      target directory -- exactly what an A/B or a bisect does -- makes
#      `cargo test` print "1 passed" for a test that must fail, and
#      `clippy -D warnings` exit 0 over code it never compiled.
#   3. `mktemp -d` names are anonymous. When those fifteen snapshots were found,
#      NOTHING recorded which lane owned which, so they could only be reclaimed
#      by age and a `lsof` check -- and a live lane between two cargo invocations
#      is indistinguishable from an abandoned one.
#
# The repository has documented (1) and (2) in prose at length. It did not work:
# of ~60 `git archive` recipes in tracked files, exactly ONE used `--touch`. So
# this is the recipe as a script rather than as another paragraph.
#
# Usage:
#   W=$(scripts/lane-snapshot.sh)            # HEAD, for $AXEYUM_AGENT
#   W=$(scripts/lane-snapshot.sh <ref>)      # a specific commit (bisect, A/B)
#   scripts/lane-snapshot.sh --list          # who owns what, and how old
#   scripts/lane-snapshot.sh --gc [hours]    # reclaim yours older than N h (default 24)
#
# The path is printed on stdout and NOTHING else is, so it composes:
#   W=$(scripts/lane-snapshot.sh HEAD~5)
#   (cd "$W" && CARGO_TARGET_DIR=$(scripts/lane-snapshot.sh --target) cargo test ...)
set -euo pipefail
cd "$(dirname "$0")/.."

SCRATCH="${AXEYUM_SCRATCH:-/data0/axeyum/scratch}"
TARGETS="${AXEYUM_TARGET_ROOT:-/data0/axeyum/target}"
AGENT="${AXEYUM_AGENT:-unknown}"

die() { echo "lane-snapshot: $*" >&2; exit 1; }

# A scratch root on a tmpfs defeats the entire point. Refuse, with the number.
assert_not_tmpfs() {
  local path="$1" fstype
  fstype=$(findmnt -T "$path" -no FSTYPE 2>/dev/null || echo unknown)
  if [ "$fstype" = "tmpfs" ]; then
    die "scratch root '$path' is a tmpfs -- that is RAM, and a snapshot of this
  repo is ~640 MB. Point AXEYUM_SCRATCH at a disk (default /data0/axeyum/scratch,
  853 G free). See docs/refactor-2026-08/06-scratch-and-snapshots.md."
  fi
}

case "${1:-}" in
  --target)
    mkdir -p "$TARGETS/$AGENT"; echo "$TARGETS/$AGENT"; exit 0 ;;
  --list)
    printf '%-14s %-12s %6s %-10s %s\n' OWNER REF AGE STATE PATH
    for d in "$SCRATCH"/snap-*; do
      [ -d "$d" ] || continue
      owner=$(cat "$d/.lane-owner" 2>/dev/null || echo '?')
      ref=$(cat "$d/.lane-ref" 2>/dev/null || echo '?')
      age=$(( ($(date +%s) - $(stat -c %Y "$d")) / 3600 ))
      state=$([ -f "$d/.lane-complete" ] && echo complete || echo INCOMPLETE)
      printf '%-14s %-12s %5sh %-10s %s\n' "$owner" "${ref:0:12}" "$age" "$state" "$d"
    done
    exit 0 ;;
  --gc)
    hours="${2:-24}"; freed=0
    for d in "$SCRATCH"/snap-*; do
      [ -d "$d" ] && [ ! -L "$d" ] || continue
      # Only ever reclaim YOUR OWN. Another lane's snapshot may be idle between
      # cargo invocations, which is indistinguishable from abandoned.
      [ "$(cat "$d/.lane-owner" 2>/dev/null)" = "$AGENT" ] || continue
      age=$(( ($(date +%s) - $(stat -c %Y "$d")) / 3600 ))
      [ "$age" -ge "$hours" ] || continue
      sz=$(du -sm "$d" 2>/dev/null | cut -f1)
      rm -rf -- "$d" && freed=$((freed + sz)) && echo "reclaimed $d (${sz} MB, ${age}h)" >&2
    done
    echo "lane-snapshot: reclaimed ${freed} MB for '$AGENT'" >&2
    exit 0 ;;
esac

REF="${1:-HEAD}"
SHA=$(git rev-parse --short "$REF") || die "not a ref: $REF"

[ "$AGENT" = "unknown" ] && echo "lane-snapshot: AXEYUM_AGENT unset -- this snapshot will be
  unattributable, which is how 9.3 GB of orphans accumulated. export it." >&2

mkdir -p "$SCRATCH" || die "cannot create scratch root '$SCRATCH'"
assert_not_tmpfs "$SCRATCH"

DIR="$SCRATCH/snap-$AGENT-$SHA"

# An INTERRUPTED extraction is the failure mode this script exists to prevent,
# and the first draft reintroduced it twice over. Found by its own controls: a
# 5-minute timeout killed an extraction (this repo takes ~127 s to lay down), and
# the orphan it left had no owner file -- so `--gc` could never match it, exactly
# the anonymous-orphan problem that put 9.3 GB in RAM. The second consequence is
# worse than the leak: the reuse branch returned ANY existing directory, so a
# truncated checkout would be handed back as a complete snapshot and built
# against. A partial tree that compiles is a wrong measurement, silently.
#
# So: stamp ownership BEFORE extracting (attributable even if killed), and gate
# reuse on a completion sentinel written only after tar returns.
if [ -d "$DIR" ] && [ -f "$DIR/.lane-complete" ]; then
  # Reuse is correct and cheap: same ref, same content, and the target dir stays
  # warm. Refresh the mtime so --gc measures time since last USE, not creation.
  touch "$DIR"
  echo "$DIR"; exit 0
fi
if [ -d "$DIR" ]; then
  echo "lane-snapshot: '$DIR' exists but is INCOMPLETE (a previous extraction was
  interrupted). Re-extracting rather than handing back a truncated tree." >&2
  rm -rf -- "$DIR"
fi

mkdir -p "$DIR"
echo "$AGENT" > "$DIR/.lane-owner"   # before extraction: killable but attributable
echo "$SHA"   > "$DIR/.lane-ref"
# --touch is the whole point: stamp with extraction time, not commit time.
git archive "$SHA" | tar -x --touch -C "$DIR" || die "extraction failed (disk full?)"
touch "$DIR/.lane-complete"

echo "$DIR"
