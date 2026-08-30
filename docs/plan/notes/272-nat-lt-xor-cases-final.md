# Notes: 272-nat-lt-xor-cases-final

Detail moved out of [`../status/272-nat-lt-xor-cases-final.md`](../status/272-nat-lt-xor-cases-final.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

`F:ml430-nat-lt-xor-cases-c43a1e85`'s `formal.statement`
(`∀ {a b c : ℕ}, a < b ^^^ c → a ^^^ c < b ∨ a ^^^ b < c`) mentions no
`testBit`/`Bool` anywhere — every quantifier is `Nat`, every operator
(`<`, `^^^`, `∨`) already existed with a matching codomain in this prelude
before this lane started. Unlike six sibling `testBit`-family mirrors this
session found unflippable (Mathlib's `testBit` returns `Bool`, ours
returns `Nat`), there is no codomain mismatch here to begin with. The
declared `Nat.lt_xor_cases` matches the fact's `formal.statement` verbatim.

## The composition, following Mathlib's own route

Read directly from the pinned v4.30 source (`Mathlib/Data/Nat/
Bitwise.lean:266-297`, commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`),
not paraphrased — see `xor_trichotomy.rs`'s module doc for the full Lean
source quoted verbatim plus the exact translation to this kernel's
`Nat`-valued `testBit`.

**`xor_trichotomy`**: three rotation identities (`Eq (xor a v) (xor b c)`,
etc., where `v := xor (xor a b) c`), each derived from `Nat.xor_assoc`/
`Nat.xor_comm`/`Nat.xor_xor_cancel_left` alone — **`Nat.xor_xor_cancel_right`
turned out unnecessary**, because `v`'s own definition IS `xor_assoc`'s LHS,
so `xor a v` collapses to `xor b c` by ONE application of
`xor_xor_cancel_left`, not two. Then `exists_most_significant_bit` on `v`
gives the highest differing bit `i`; a direct forward 8-way case split on
`testBit a i`/`testBit b i`/`testBit c i` (via `Nat.lt_two_cases`, since this
kernel's `testBit` is `Nat`-valued rather than `Bool`, so Mathlib's
`contrapose!`/`simp_rw [Bool.eq_false_eq_not_eq_true]` step does not apply)
picks out which of the three has bit `i` set; that branch closes via
`Nat.lt_of_testBit` transported along the matching rotation. The one
degenerate branch (all three bits `= 0`) is refuted against `hi : testBit v
i = 1` by computing `testBit v i = 0` from `Nat.testBit_xor` applied twice
plus `Nat.succ_ne_zero`.

**`lt_xor_cases`**: reuses `xor_trichotomy` at the SAME `(a, b, c)` it is
given (not a permutation) — `Lt a (xor b c)` gives `Not (Eq a (xor b c))`
(built inline via `Nat.lt_irrefl` + a transport, since no bare `ne_of_lt`
lemma exists in this prelude), then `Nat.xor_ne_zero_iff.mpr` composed with
`Nat.xor_assoc` routes that into `xor_trichotomy`'s exact hypothesis. The
`Lt (xor b c) a` branch is refuted the same way (`Nat.le_succ`/
`Nat.le_trans`/`Nat.lt_of_lt_of_le`/`Nat.lt_irrefl`, since no bare
`lt_asymm` lemma exists either); the other two branches route through
`Nat.xor_comm` (one of them) or land directly (the other).

Two small helpers were duplicated into the new file rather than exposed
from `xor_algebra.rs`/`bit_order.rs`/`rec_agreement.rs` (private `fn`s, not
cross-file accessible, per this session's standing convention):
`msb_predicate`, `exists_elim`, `ex_falso` (verbatim copies), plus a new
`xor_bit_zero_right : Eq (xor_bit x 0) x` given `Le x 1` (the same
`{0, 1}` case-split shape `xor_algebra.rs`'s `round_trip_le_one` uses,
applied to a different target).

## Evidence and closing the fact

New test `xor_trichotomy_and_lt_xor_cases_apply_at_concrete_discriminating_instances_and_symbolically`
(`nat_prelude_tests.rs`): `xor_trichotomy` checked at `(a, b, c) = (1, 2, 4)`
(`v = 7`, all three disjuncts of `Or (Lt 6 1) (Or (Lt 5 2) (Lt 3 4))`
genuinely discriminating — exactly the third holds); `lt_xor_cases` checked
at `(a, b, c) = (0, 2, 3)` (`Or (Lt 3 2) (Lt 2 3)` — `Lt 3 2` false, `Lt 2 3`
true, discriminating the two branches) AND symbolically at a genuinely free
`(a, b, c)` triple with a free hypothesis fvar. Confirmed running by name,
`1 passed`, not `0 filtered out`.

`F:ml430-nat-lt-xor-cases-c43a1e85` flipped `open` -> `proved`,
`proof_route: kernel-lean`, `axiom_footprint: []`. Three evidence rows, each
re-run and confirmed passing before committing: `nat_theorem_inventory`
(anchored `grep -Ec`, kernel presence by exact rendered name), the
concrete+symbolic evaluation test by name, and `nat_axiom_inventory
--require-axiom-free nat` (axiom-free footprint). `depends_on` names the
four direct dependency facts. `scripts/gen-autogenesis-bitwise-family-
projection.py` checked directly — does not name this fact, so nothing pins
it open independent of provability.

`the_build_is_deterministic` pin: `93 + 514` -> `93 + 516` (two new
theorems), taken from the panic's own mismatch.

## Commits (this lane)

1. `wip(nat): xor_trichotomy.rs scaffold -- Nat.xor_trichotomy/Nat.lt_xor_cases, compiles, NOT yet kernel-checked`
   (`8e18a981c`) — the new file, prelude wiring (mod declaration, use
   import, two new `NameId` fields, dispatch call). Landed within the first
   ten tool calls per the standing rule; compiled but not yet
   test-verified.
2. `feat(nat): Nat.xor_trichotomy, Nat.lt_xor_cases -- admitted axiom-free on the first real kernel-check attempt`
   (`9de6fa62e`) — confirms both theorems kernel-check on the first attempt,
   registers them in `theorem_names`, recounts the pin, adds the
   evaluation test, fixes a `clippy::too_many_arguments` lint.
3. `close: F:ml430-nat-lt-xor-cases-c43a1e85 -- Nat.lt_xor_cases, the last closable ml430 nat row`
   (`c5e964056`) — the fact ledger flip.

## Verified

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **158 passed, 0
failed** (157 before this lane, +1 new test, confirmed running by name).
`cargo fmt --all --check` clean (files formatted individually with
`rustfmt --edition 2024 <file>`). `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` clean. `python3
scripts/check-test-attribute-integrity.py` — 0 findings across 1,514
files. `python3 scripts/validate-facts.py` — 1949 facts, 0 errors.
Workspace gate NOT run (coordinator re-verifies before merging, per the
lane brief). Not pushed.
