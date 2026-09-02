# Lane: divergence-bitwise — register Nat.land/lor/ldiff/bitwise in the divergence registry

<!-- plan-section: lane-status -->

**divergence-bitwise (`DONE`, divergence-bitwise, 2026-09-02).** Took
`testbit-codomain`'s named next action: `Nat.land`/`Nat.lor`/`Nat.ldiff`
diverge from Mathlib by the same standard the registry applies to
`Nat.minFac`. Registered three rows (`class: recursion-principle`), each
read at the pinned commit `c5ea00351c28e24afc9f0f84379aa41082b1188f` --
Mathlib builds `land`/`lor` from core's well-founded `Nat.bitwise`
(`Init/Data/Nat/Bitwise/Basic.lean:27`, `decreasing_by`), `ldiff` from the
same combinator one layer up (`Mathlib/Data/Nat/Bits.lean:147`); this
kernel lands each as an independent structural fuel recursion
(`nat_prelude/land.rs:90-190`, `lor.rs:113-217`, `ldiff.rs:120-228`), and
its own general `Nat.bitwise` (`nat_prelude/bitwise.rs:339-482`) is ALSO
fuel-based, never well-founded.

**`Nat.bitwise` itself is deliberately NOT a standalone row.** A naive
blanket surface form (`"&&&"`, `"|||"`, `"Nat.bitwise"`) was tried and
measured, not assumed, to fail `check-dispatchable-frontier.py`'s own G3
guard: `Nat.land` with `surface_forms: ["&&&"]` blocks 13 already-settled
mirrors closed by this kernel's own `bitwise_and_eq_land`/`bitwise_or_eq_lor`
bridge theorems (`nat_prelude/rec_agreement.rs:403-411`); `Nat.bitwise` with
`surface_forms: ["Nat.bitwise"]` likewise blocks its own 3 settled mirrors
and matches zero open ones. Per that guard's stated philosophy -- "a
construction we have closed a mirror over does not diverge" -- registering
either would be a false claim, the same over-blocking direction caught for
`Max.max`/`Min.min` on 2026-09-01. The three rows landed instead use
`surface_forms` scoped to the operator-composed-with-`.testBit` shape
(`"&&& n).testBit"` etc.), matching Mathlib's own `testBit_land`/
`testBit_lor`/`testBit_ldiff` argument names (`Mathlib/Data/Nat/Bitwise.lean
:115,118,122`) -- the only shape currently unclosed.

**`brief-step0.py` verdict move.** Grepping `artifacts/facts/F-ml430-*.json`
for `land`/`lor`/`ldiff`/`bitwise` (by id/title, the reliable axis --
operator-notation false-positives on `formal.statement` substrings were
ruled out by hand) found 13 facts total: **10 already `proved`** (`and-comm`,
`and-assoc`, `and-le-left`, `and-le-right`, `and-self`, `and-div-two`,
`and-mod-two-eq-one`, `and-one-is-mod`, `and-or-distrib-left`,
`and-or-distrib-right`, plus `land-comm`/`land-assoc`/`land-bit`/`lor-comm`/
`lor-assoc`/`lor-bit`/`ldiff-bit`/`bitwise-bit`/`bitwise-comm`/
`bitwise-swap` -- 19 distinct ids across the `nat-and-*`/`nat-land-*`/
`nat-lor-*`/`nat-ldiff-*`/`nat-bitwise-*` families, not the ~10-20 the brief
predicted for the OPEN set specifically) and exactly **3 open**:
`F:ml430-nat-testbit-land-dfef7ca4`, `F:ml430-nat-testbit-lor-7644e067`,
`F:ml430-nat-testbit-ldiff-16f94162`. `python3 scripts/brief-step0.py` on
all three, before and after: **all three were ALREADY `DIVERGENCE-BLOCKED`
before this lane**, via the pre-existing `Nat.testBit` row (its own `why`
field already narrated this exact chain as item 3). After: each now shows
**two** independent `DIVERGENCE-BLOCKED` lines (`Nat.testBit (codomain)` +
`Nat.land`/`Nat.lor`/`Nat.ldiff (recursion-principle)`). No fact moved
buckets -- expected and documented, not a defect: the value is an
independent, second, checkable reason plus G3/`--screen` coverage against a
future misclosure or a future preregistration of this same composite shape.

**Frontier and census counts, before vs. after (registry swapped both ways
against the identical fact/nursery snapshot):**

| | before (9 registry rows) | after (12 registry rows) |
| --- | --- | --- |
| `check-dispatchable-frontier.py --json`: `blocked` | 12 | 12 |
| `check-dispatchable-frontier.py --json`: `dispatchable` | 2 | 2 |
| `check-dispatchable-frontier.py --json`: `guard_failures` | 1 (pre-existing `G7 queue-below-floor`, unrelated) | 1 (same) |
| `frontier-shape-census.py --print`: `divergence-blocked` | 9 | 9 |
| `frontier-shape-census.py --print`: `genuinely targetable` | 4 | 4 |

Unchanged in every column. Full chain, empirical G3 failure text, and file:
line citations on both sides in
[2026-09-02-land-lor-ldiff-are-recursion-principle-divergences.md](../../research/11-design-review/2026-09-02-land-lor-ldiff-are-recursion-principle-divergences.md).

**Held-out check (deliverable 4).** All three affected `ml430` facts are
`partition: development`, family `natural-bitwise`, confirmed both by
reading `artifacts/autogenesis/nursery-v1.json` directly and by calling
`check-dispatchable-frontier.py`'s own `load_partitions()` -- none is in the
`held` set. Registry rows are about declarations, not facts, so this was
never expected to arise, and it did not.

**Verified.** `python3 scripts/frontier-shape-census.py --check`: PASS
(committed artifact already matches fresh recomputation -- no `--write`
needed, since no fact moved buckets). `python3
scripts/gen-obstruction-producers.py --check`: `OK`. `python3
scripts/check-obstruction-producers.py`: `OK -- 7 obstruction(s) classified,
2 producer contract(s) compiled, all guards passed` (both producers already
`kind=fulfilled`, unrelated to this lane's change -- the `P2` failure
`testbit-codomain` recorded on `main` was already fixed by lane
`obstruction-producers-red` before this lane merged `main`). `python3
scripts/validate-facts.py`: `2606 facts checked, 0 errors`. `python3
scripts/check-mirror-statement-fidelity.py`:
`MIRROR_STATEMENT_FIDELITY|facts=2606|mirrors=716|hash_verified=702|
unpinned=14|violations=0|verdict=PASS`. No ADR needed (no decision
reversed).

**Did not run:** `just check`/`./scripts/check.sh` (Rust workspace gate --
this lane touched no Rust or fact-ledger content, only the registry JSON and
docs; `just brief`/`shape_search` rebuild not attempted, no cargo needed per
brief). `cargo` was not invoked at all.

<!-- plan-section: landed-changes -->

| 2026-09-02 | 8a8412634 | lane stub opened |
| 2026-09-02 | f6e747001 | 3 rows added to `mirror-divergence-registry.json` (`Nat.land`/`Nat.lor`/`Nat.ldiff`, `class: recursion-principle`); `Nat.bitwise` deliberately left unregistered (would violate the registry's own G3 guard against its 3 already-settled mirrors); `docs/research/11-design-review/2026-09-02-land-lor-ldiff-are-recursion-principle-divergences.md` records the chain, file:line citations, and the empirical G3 failure text. No fact moved buckets (all 3 affected facts were already `DIVERGENCE-BLOCKED` via the pre-existing `Nat.testBit` row); each now carries a second, independent, checkable reason. |
