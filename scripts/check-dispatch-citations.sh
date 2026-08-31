#!/usr/bin/env bash
# Verify every path or declaration a lane brief cites is visible on origin/main.
#
# A lane worktree branches from ORIGIN, not from my local checkout. I merge lane
# branches continuously and push in the background, and pushes here take a ~545 s
# battery and lose races against other commits -- so `origin/main` routinely lags
# my tree by hours. Every brief written in that window cites a tree only I have.
#
# This has now cost three lanes in one session, all on the same dependency chain.
# Each stopped correctly and reported rather than rebuilding, which is the best
# possible outcome and still a wasted dispatch.
#
# The trap that makes a path check insufficient: `gauss_lemma.rs` was on origin
# while the DECLARATION the brief depended on was in an unpushed commit to that
# same file. So check declarations by name, not just paths.
#
#   check-dispatch-citations.sh path <p>...        every path must exist on origin
#   check-dispatch-citations.sh decl <name>...     every name must appear on origin
#
# Exit 0 all visible, 1 something is not -- with the missing items named.
set -u
MODE="${1:?usage: check-dispatch-citations.sh path|decl <item>...}"
shift
[ "$#" -gt 0 ] || { echo "no items given -- nothing checked, which is not a pass" >&2; exit 1; }

git fetch -q origin main 2>/dev/null || true
MISSING=0
for item in "$@"; do
  case "$MODE" in
    path)
      if git ls-tree origin/main "$item" --name-only 2>/dev/null | /usr/bin/grep -q .; then
        echo "  on origin: $item"
      else
        echo "  NOT ON ORIGIN: $item"; MISSING=$((MISSING + 1))
      fi
      ;;
    decl)
      # A declaration lives inside a file that may already be on origin, so the
      # path check above is not enough -- grep origin's own content for the name.
      # NOTE the pathspec: `crates/*/src` matches NOTHING here, and a query that
      # matches nothing makes this check refuse every citation -- which reads as
      # caution and is just a broken check. Caught by running a positive control
      # (`Nat.add_comm`) that MUST hit; it came back empty too.
      HITS=$(git grep -c -F -- "$item" origin/main -- crates 2>/dev/null | head -1)
      if [ -n "$HITS" ]; then
        echo "  on origin: $item"
      else
        echo "  NOT ON ORIGIN: $item"; MISSING=$((MISSING + 1))
      fi
      ;;
    *) echo "unknown mode '$MODE'" >&2; exit 1 ;;
  esac
done

if [ "$MISSING" -gt 0 ]; then
  echo "DISPATCH_CITATIONS|REFUSED|$MISSING of $# not visible to a lane worktree." >&2
  echo "  Either push first, or write the brief as if the work does not exist." >&2
  exit 1
fi
echo "DISPATCH_CITATIONS|checked=$#|all visible on origin/main"
