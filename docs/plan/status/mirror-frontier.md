# Lane `mirror-frontier`

**Status:** in progress — closing `ml430` mirrors from the live dispatchable set.

Frontier at lane start (`python3 scripts/check-dispatchable-frontier.py --json`):
exit 0, 26 dispatchable, 166 held-out, `settled=0`.

Selected group: the `Nat` min/max family (12 dispatchable mirrors) — they all
share one piece of machinery (`Max.max` / `Min.min`, already declared as
definitions in `crates/axeyum-lean-kernel/src/nat_prelude/minmax.rs`, with no
theorem about either).

## Landed changes

(in progress)
