#!/usr/bin/env bash
# Lane euf-driver-mbtc: does the reachability guard actually fail when the thing
# it guards is removed?
#
# Mutation: make `OverboundOutcome::FallThrough` answer for the dispatcher, i.e.
# restore the behaviour this lane removed. Exactly the tests that assert the
# ladder runs must die, and no others. Isolated worktree, with a trap that
# restores the file whatever happens.
set -uo pipefail
cd "$(dirname "$0")/.."

F=crates/axeyum-solver/src/auto.rs
BAK=.lane-euf-driver-mbtc/auto.rs.premutation
cp "$F" "$BAK"
restore() { cp "$BAK" "$F"; touch "$F"; }
trap restore EXIT

python3 - <<'PY'
p='crates/axeyum-solver/src/auto.rs'
s=open(p,encoding='utf-8').read()
old="""    match dispatch_uf_arith_overbound(arena, assertions, config, features, entry_deadline, rec)? {
        OverboundOutcome::NotEngaged | OverboundOutcome::FallThrough => {}
        OverboundOutcome::Answer(result) => return Ok(Some(result)),
    }"""
new="""    match dispatch_uf_arith_overbound(arena, assertions, config, features, entry_deadline, rec)? {
        OverboundOutcome::NotEngaged => {}
        OverboundOutcome::FallThrough => return Ok(None),
        OverboundOutcome::Answer(result) => return Ok(Some(result)),
    }"""
assert old in s, "MUTATION ANCHOR NOT FOUND -- the mutation did not apply, so a green run proves nothing"
open(p,'w',encoding='utf-8').write(s.replace(old,new))
print("mutation applied")
PY

touch "$F"
./scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full -- overbound --test-threads=2
echo "MUTANT_EXIT=$?"
