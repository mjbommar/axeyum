# Lane: nat-parity — a real `Nat.Even`/`Nat.Odd` predicate family

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-parity, 2026-08-28).** Landed `Nat.Even n :=
Exists (fun k => Eq n (add k k))` and `Nat.Odd n := Exists (fun k => Eq n
(succ (add k k)))` — the `k+k`/`succ(k+k)` form (not `2*k`/`2*k+1`), chosen
because `Nat.even_or_odd` (`powsq.rs`) already produces exactly that shape as
its own branch equations, so `even_or_odd_exists` hands them straight to
`Exists.intro` at witness `div n 2` with no conversion. All three requested
items (1–3) landed with real kernel-checked proofs, plus all of the "bonus"
item 4: `even_not_odd`, `odd_not_even` (via a new
`add_self_ne_succ_add_self : ∀ k j, Not (Eq (add k k) (succ (add j j)))`,
proved by induction on `k` with an inner case split on `j`), and
`even_iff_odd_succ` (direct `congrArg succ`/`succ_injective`, no induction
needed). All seven declarations rest on zero axioms (kernel-verified, not
asserted). New module: `crates/axeyum-lean-kernel/src/nat_prelude/parity.rs`.

`powsq.rs`'s inline even/odd split (`declare_even_or_odd`, the
`Or (Eq n (add half half)) (Eq n (succ (add half half)))` disjunction) was
**not** re-derived — `even_or_odd_exists` calls the existing theorem
`Nat.even_or_odd` as a lemma and repackages its two branches via
`Exists.intro`, with zero new case-analysis machinery. Nothing else this
brief expected to find already-existing (`Nat.Even`/`Nat.Odd` under any
spelling) was present — the grep-with-positive-control the brief specified
came back empty both times, and it stayed empty.

`nat_prelude::` sweep: 95 passed before this lane, 97 passed after (95 + the
previously-failing coverage-inventory assertion, now fixed, + one new
concrete-witness cross-check test). 0 failed throughout. No fact-ledger entry
was created — these are infrastructure declarations with no formal-statement
consumer yet; a downstream lane building `Coprime 2 n ↔ Odd n` or similar
should register the fact then, not here.

Not attempted (explicitly out of scope per the brief): `Coprime 2 n ↔ Odd n`
and any other downstream cascade.

<!-- plan-section: landed-changes -->

| 2026-08-28 | `de8d37ef5` | `Nat.Even`/`Nat.Odd` + `even_or_odd_exists`, `add_self_ne_succ_add_self`, `even_not_odd`, `odd_not_even`, `even_iff_odd_succ` (new `nat_prelude/parity.rs`) |
| 2026-08-28 | `acc299135` | register the 7 new declarations in `every_nat_declaration_is_checked_and_axiom_free`'s inventory; recount `the_build_is_deterministic`'s pin (65+331 -> 67+336) |
| 2026-08-28 | `4cf8aa9ec` | concrete-witness cross-check (`Even 4`, `Odd 5` hand-built) catching an `mp`/`mpr` swap that type-shape alone would not |
