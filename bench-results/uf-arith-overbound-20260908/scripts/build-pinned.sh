#!/usr/bin/env bash
# Lane euf-driver-mbtc: build two PINNED binaries — one from the lane's base
# commit, one from the working tree — and copy each out of `target/` so a later
# build cannot swap the file a sweep is reading. That happened once already:
# the first baseline had rows 1-30 from one binary and 31-58 from another.
set -euo pipefail
cd "$(dirname "$0")/.."

LANE=.lane-euf-driver-mbtc
BAK=$LANE/worktree-backup
FILES="crates/axeyum-solver/src/auto.rs crates/axeyum-solver/src/lib.rs crates/axeyum-solver/src/euf.rs crates/axeyum-solver/src/config_registry.rs crates/axeyum-bench/examples/smtcomp_cli.rs"

mkdir -p "$BAK"
for f in $FILES; do
  mkdir -p "$BAK/$(dirname "$f")"
  cp "$f" "$BAK/$f"
done

restore() {
  for f in $FILES; do cp "$BAK/$f" "$f"; done
  touch $FILES
}
trap restore EXIT

echo "== building BASE (HEAD) =="
for f in $FILES; do git show "HEAD:$f" > "$f"; done
touch $FILES
./scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli
cp target/release/examples/smtcomp_cli "$LANE/smtcomp_cli.base"

echo "== building NEW (working tree) =="
restore
trap - EXIT
./scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli
cp target/release/examples/smtcomp_cli "$LANE/smtcomp_cli.new"

sha256sum "$LANE/smtcomp_cli.base" "$LANE/smtcomp_cli.new"
echo PINNED_BUILD_COMPLETE
