# Notes: 288-int-emod-additive

Detail moved out of [`../status/288-int-emod-additive.md`](../status/288-int-emod-additive.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. `emod_two_eq_zero_or_one` (already built by the prior lane) splits each of
   `m`'s and `n`'s parity into `emod _ 2 = 0` or `= 1`.
2. `to_modeq(d, n, x, r, h, hr)` lifts a plain `Eq (emod x n) r` fact into an
   `Int.ModEq n x r` fact — `ModEq` unfolds to exactly that `Eq`, one delta
   step, so `Eq.trans h (Eq.symm hr)` already has the right shape (`hr` is a
   tiny idempotence fact, `emod_zero_two`/`emod_one_two`, both closed by
   plain reduction on magnitudes 0/1).
3. `modeq_add` combines `m`'s and `n`'s `ModEq` facts into one for `m+n`
   against the literal sum of residues (`sum_parity_hyp`).
4. The residue sum (`0+0`, `0+1`, `1+0`, `1+1`) reduces by plain computation
   to the target residue (`0` or `1`) — magnitudes are all ≤ 2, so this is
   cheap (see the "unary numeral blowup" gotcha — not triggered here).
5. Reading the resulting residue back into `Even`/`Odd` needed the
   CONVERSE of what the prior lane built (`even_implies_emod_zero`/
   `odd_implies_emod_one`, `mp`-only) — new here:
   `emod_zero_implies_even`/`emod_one_implies_odd`. `ofNat m` branch: plain
   `int_eq_rewrite` injectivity through `natAbs`. `negSucc m` branch: the map
   `r ↦ subNatNat 2 (succ r)` SWAPS `0`/`1` rather than fixing them, so this
   case-splits on `Nat.mod_two_eq_zero_or_one m` itself and refutes the wrong
   disjunct via the already-private `izero_ne_one`. Needed one new Nat-level
   helper, `nat_odd_implies_even_succ` (mirror of the existing
   `nat_even_succ_implies_odd`).
6. Each of the three theorems' proof is then a case split (four-way for
   `even_add`/`even_add'`, two-way for `even_add_one`) combined through a
   small generic `Iff`-truth-value combinator (`TruthFact`/`iff_fact`) that
   handles "both hold" / "both refuted" / "exactly one, so the whole `Iff` is
   refuted" uniformly — shared by all three theorems and both the inner
   (`Even m ↔ Even n` or `Odd m ↔ Odd n`) and outer (`Even (m+n) ↔ …`) `Iff`.

**`Int.even_add` vs `Int.even_add'` re-confirmed genuinely different**
(the prior lane already verified this against Mathlib source; not
re-litigated here beyond reuse): `even_add`'s inner predicate is `Even`,
`even_add'`'s is `Odd`. Both share `even_add_family_stmt_and_proof`,
parametrized by `inner_fact`/`inner_pred` (`even_fact`/`even_pred` vs
`odd_fact`/`odd_pred`); only the inner predicate differs, the outer `Even
(m+n)` and the whole case-split/`ModEq` machinery are identical.

**A real bug, found and fixed via a throwaway probe.** First attempt failed
every one of the 49 `int_prelude::` tests with `TypeMismatch { expected:
<huge>, got: ExprId(3) }` — the "one bad declaration poisons the whole
prelude build" symptom. Bisected by disabling two of the three new
`declare_*` calls and confirming the culprit was `declare_even_add`, then
built a temporary `#[cfg(test)] mod debug_probe` (removed before the final
commit, per the standing rule) that constructed a fresh `IntDev` over the
ALREADY-BUILT kernel via axiom-typed placeholder `m`/`n`/`hm0`/`hn0`, and ran
`Kernel::infer` on each intermediate (`sum_parity_hyp` → `even_fact` for
`m`/`n`/sum → `iff_fact` inner → outer) to find exactly which step failed.
Root cause: `emod_zero_implies_even`/`emod_one_implies_odd` used `d.irefl`
(the `IntDev`-specific, **Int-typed** `Eq.refl`) on `r := Nat.mod m 2`, a
**Nat**-sorted term — wrong carrier. Fixed by using `d.refl` (the `NatOps`
trait's Nat-level reflexivity, already used correctly elsewhere in this same
file). Worth carrying forward: `IntDev` exposes BOTH an Int-level `irefl`
(its own inherent method) and a Nat-level `refl` (via `NatOps`), with no
type-level guard against calling the wrong one on the wrong-sorted term —
the kernel's own type check is what caught it, not the Rust type system.

**Files:**
- `crates/axeyum-lean-kernel/src/int_prelude/parity.rs` — all new code
  (`modeq_add`, `to_modeq`, `emod_zero_two`/`emod_one_two`,
  `emod_zero_implies_even`/`emod_one_implies_odd`,
  `nat_odd_implies_even_succ`, `TruthFact`/`iff_fact`/`mk_iff_both_true`/
  `mk_iff_both_false`/`refute_iff_from_mp`/`refute_iff_from_mpr`,
  `even_fact`/`odd_fact`/`even_pred`/`odd_pred`, `sum_parity_hyp`,
  `add_case`/`even_add_family_stmt_and_proof`, `add_one_parity_hyp`/
  `even_add_one_case`, and the three `declare_even_add*` functions).
- `crates/axeyum-lean-kernel/src/int_prelude.rs` — three new `IntPrelude`
  fields (`even_add`, `even_add_prime` → kernel name `"even_add'"`,
  `even_add_one`) and their dispatch calls, placed right after
  `parity::declare_odd_of_mul_right` (after `Int.ModEq`'s additive
  congruences, declared much earlier in the same build).
- `crates/axeyum-lean-kernel/src/int_prelude/int_prelude_tests.rs` — the
  three new theorems added to `derived_laws`; the pinned array size
  recounted 177 → 180 via `scripts/recount-pinned-inventory.py` (not
  incremented by hand).
- `artifacts/facts/F-ml430-int-even-add-3c4536e3.json`,
  `F-ml430-int-even-add-bc8e1394.json`,
  `F-ml430-int-even-add-one-af33da18.json` — flipped `open` → `proved`, each
  with a `kernel-term` evidence row (`cargo test -p axeyum-lean-kernel --lib
  int_prelude::`) and a `theorem_axiom_footprint`-based axiom-freedom row.

**Checks run:** `cargo test -p axeyum-lean-kernel --lib int_prelude::` (49
passed), `rustfmt --edition 2024 --check` on all four touched Rust files
(clean), `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`
(clean), `python3 scripts/check-test-attribute-integrity.py` (0 findings —
touched `int_prelude_tests.rs`), `python3 scripts/validate-facts.py` (2034
facts, 0 errors). Each `theorem_axiom_footprint` `checker_command` verified
three ways: passes for real (count 1), fails on a mutated footprint value
(`...\t1\t`, count 0), fails on a nonexistent theorem name (count 0) — the
`-xF` exact-line grep is load-bearing because the tool's own CLI name
argument is a PREFIX match (`Int.even_add` alone also returns
`Int.even_add'`/`Int.even_add_one` rows).

**Straggler note (NOT attempted, per the brief — do not start until the
`emod` law was done, which it now is).** Two facts named as possible
follow-ons in the brief:
- `F:ml430-nat-add-div-of-dvd-add-add-one-f17dffc0` — the `nat-div-mod-family`
  lane's own leftover; route sketch in
  `docs/plan/status/283-nat-div-mod-family.md`.
- `F:ml430-nat-base-induction-83561d4c` — not investigated at all in this
  lane.

Neither was started: this lane's time went to the `emod` law (which turned
out cheaper than sized, but the debugging round-trip on the `irefl`/`refl`
bug cost real time) plus the three mirrors and their evidence. Both remain
open for a future lane. `nat_prelude/div_mod_lemmas.rs` was NOT touched (per
the brief, since a sibling lane may still be in it).

Commits (not pushed):
- `wip(int): emod additive law + even_add/even_add'/even_add_one (untested)`
  — early checkpoint, uncompiled.
- `fix(int): emod additive law fix (irefl->refl bug) + close all 3 even_add
  mirrors` — the working kernel/prelude code.
- `facts: flip the three ml430-int-even-add-* mirrors to proved` — the fact
  ledger.
