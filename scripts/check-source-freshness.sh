#!/usr/bin/env bash
# Content-addressed freshness: stop cargo replaying a cached artifact over
# source it never compiled.
#
# WHY THIS EXISTS (measured 2026-08-14, cargo 1.97.0-nightly, clippy 0.1.97).
# Cargo decides a unit is fresh by comparing SOURCE MTIMES against the cached
# artifact. A source file whose mtime is OLDER than the artifact is invisible:
#
#     # example carries `needless_return`, but is stamped in the past
#     touch -d '2020-01-01' examples/warny.rs
#     cargo clippy --all-targets -- -D warnings   -> exit 0, "Finished in 0.00s"
#
#     # a unit test that must now FAIL, stamped in the past
#     touch -d '2020-01-01' src/lib.rs
#     cargo test                                  -> exit 0, "1 passed"
#
# The second one is the serious one: `cargo test` reported a PASSING test over
# code it never compiled. That is worse than the "running 0 tests ... ok" traps
# in CLAUDE.md, because the test count is right and only the code is wrong.
#
# This is not a hypothetical mtime. `git archive HEAD | tar -x` stamps EVERY
# extracted file with the COMMIT timestamp (verified: a snapshot taken at 10:26
# had every file stamped 10:23:41, the commit time), and building from such a
# snapshot in a reused target directory is the workflow every lane in this
# campaign is told to use. Bisecting, `git checkout` of an older commit, restored
# backups, and rsync without `--times` land in the same place.
#
# THE FIX. Keep a manifest of the content hash of every build input that the
# named gate last examined. On the next run, `touch` exactly the files whose
# CONTENT changed, so cargo's mtime comparison cannot be wrong about them, and
# report the counts. Freshness then means "this content was examined", not "this
# file looks old".
#
# Usage:
#   scripts/check-source-freshness.sh --gate <name> [--touch|--report|--record]
#     --touch   (default) touch every input whose content differs from the
#               manifest, so the next cargo invocation must recompile it
#     --report  print what WOULD be touched; change nothing (exit 1 if any)
#     --record  write the manifest; run this only after the gate PASSED
#   --root DIR      repository root (default: the repo this script lives in)
#   --manifest FILE explicit manifest path (default: <target>/gate-scope/<gate>.sha256)
#
# The `--root`/`--manifest` overrides exist so the negative control
# (`scripts/tests/test-gate-scope-controls.sh`) can drive this script against a
# throwaway crate. They are not needed for ordinary use.
set -uo pipefail

gate=""
mode="touch"
root=""
manifest=""

while [ $# -gt 0 ]; do
  case "$1" in
    --gate) gate="${2:-}"; shift 2 ;;
    --touch) mode="touch"; shift ;;
    --report) mode="report"; shift ;;
    --record) mode="record"; shift ;;
    --root) root="${2:-}"; shift 2 ;;
    --manifest) manifest="${2:-}"; shift 2 ;;
    *) echo "check-source-freshness: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

if [ -z "$gate" ]; then
  echo "check-source-freshness: --gate <name> is required" >&2
  exit 2
fi

if [ -z "$root" ]; then
  root="$(cd "$(dirname "$0")/.." && pwd)"
fi
cd "$root" || exit 2

target_dir="${CARGO_TARGET_DIR:-$root/target}"
if [ -z "$manifest" ]; then
  manifest="$target_dir/gate-scope/$gate.sha256"
fi

# Build inputs, enumerated from the filesystem rather than from cargo's module
# graph — the same argument as `check-fmt-complete.sh`. `corpus/`, `artifacts/`
# and `docs/` are here because 40+ `include_str!`/`include_bytes!` sites reach
# into them, so their content is compiled into test binaries.
inputs=(crates corpus artifacts docs Cargo.toml Cargo.lock rustfmt.toml)
present=()
for i in "${inputs[@]}"; do
  [ -e "$i" ] && present+=("$i")
done
if [ ${#present[@]} -eq 0 ]; then
  echo "check-source-freshness[$gate]: no build inputs found under $root -- the enumeration is broken" >&2
  exit 2
fi

hashes="$(mktemp)" || exit 2
trap 'rm -f "$hashes"' EXIT

# `-P` for speed (measured 0.4 s over 6442 files / 426 MB). Stored as
# "<path> <hash>" and sorted on the WHOLE line under `LC_ALL=C`, because `comm`
# below requires both files in that exact order — sorting `sha256sum`'s native
# "<hash>  <path>" by path would silently give `comm` unsorted input.
export LC_ALL=C
find "${present[@]}" -type f -not -path '*/target/*' -not -path '*/.git/*' -print0 \
  | xargs -0 -P 8 -n 200 sha256sum 2>/dev/null \
  | sed -E 's/^([0-9a-f]+)  (.*)$/\2\t\1/' \
  | sort > "$hashes"

count=$(wc -l < "$hashes")
if [ "$count" -eq 0 ]; then
  echo "check-source-freshness[$gate]: hashed 0 files -- the enumeration is broken" >&2
  exit 2
fi

if [ "$mode" = "record" ]; then
  mkdir -p "$(dirname "$manifest")" || exit 2
  cp "$hashes" "$manifest" || exit 2
  echo "check-source-freshness[$gate]: recorded $count build inputs as examined"
  exit 0
fi

# No manifest: nothing certifies that the cached artifacts in this target dir
# were built from this content. If the target dir is empty there is nothing to
# be wrong about; if it is not, every stale artifact is a potential lie, so
# refresh everything (one full rebuild, once).
if [ ! -f "$manifest" ]; then
  if [ -d "$target_dir/debug" ] || [ -d "$target_dir/release" ]; then
    if [ "$mode" = "report" ]; then
      echo "check-source-freshness[$gate]: $count build inputs; NO manifest for this" \
           "target dir, so none of the $count is certified against the cached artifacts"
      exit 1
    fi
    while IFS=$'\t' read -r path _; do touch -c -- "$path"; done < "$hashes"
    echo "check-source-freshness[$gate]: hashed $count build inputs; no manifest for" \
         "this target dir, so ALL $count were touched (cached artifacts here were" \
         "built from unknown content). This costs one full rebuild, once."
  else
    echo "check-source-freshness[$gate]: hashed $count build inputs; target dir is" \
         "empty, so nothing can be replayed from cache"
  fi
  exit 0
fi

changed="$(mktemp)" || exit 2
trap 'rm -f "$hashes" "$changed"' EXIT

# Lines present in the new hash list but not in the manifest = added or edited.
# (A deleted file needs no touch: cargo notices a missing input.)
comm -23 "$hashes" "$manifest" > "$changed"
n_changed=$(wc -l < "$changed")

# Of those, the dangerous ones are the files cargo would consider FRESH: mtime
# not newer than the manifest's own mtime, i.e. content that changed without the
# clock moving forward. Reported separately because that set is the actual bug.
n_stale=0
stale_list=""
while IFS=$'\t' read -r path _; do
  [ -e "$path" ] || continue
  if [ ! "$path" -nt "$manifest" ]; then
    n_stale=$((n_stale + 1))
    [ "$n_stale" -le 10 ] && stale_list="$stale_list  $path"$'\n'
  fi
done < "$changed"

if [ "$mode" = "report" ]; then
  echo "check-source-freshness[$gate]: $count build inputs, $n_changed changed since" \
       "the last recorded run, $n_stale of them older than the manifest (invisible to cargo)"
  [ -n "$stale_list" ] && printf '%s' "$stale_list"
  [ "$n_stale" -gt 0 ] && exit 1
  exit 0
fi

touched=0
while IFS=$'\t' read -r path _; do
  [ -e "$path" ] || continue
  touch -c -- "$path" && touched=$((touched + 1))
done < "$changed"

echo "check-source-freshness[$gate]: $count build inputs hashed, $n_changed changed" \
     "since the last recorded run, $touched touched so cargo must recompile them" \
     "($n_stale would otherwise have been invisible: content changed, mtime did not move forward)"
if [ "$n_stale" -gt 0 ]; then
  printf 'check-source-freshness[%s]: mtime-invisible content (first %d):\n' "$gate" \
    "$(( n_stale > 10 ? 10 : n_stale ))"
  printf '%s' "$stale_list"
fi
exit 0
