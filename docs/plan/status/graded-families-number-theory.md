# graded-families-number-theory — lane status

<!-- plan-section: lane-status -->

Status: IN PROGRESS. Step 0 (existing-work survey) complete; implementation
of Family A underway.

## Step 0 findings — what already exists (read this before assuming anything below is open)

- **ADR-0716 is accepted** and settles the framing: for Nat/Int/Rat the
  analysis-style row 2 (order totality) is a proved, axiom-free theorem, so
  it is EMPTY for number theory. Two other boundaries survive (unbounded
  search / LNP-implies-EM, and an expressiveness row 2'). Per this lane's
  brief, row 2 is out of scope here regardless.
- **The unrestricted LNP-implies-EM row 2 is ALREADY LANDED**, by a sibling
  lane, committed and merged to `main` before this lane started:
  `nat_prelude/least_number.rs::declare_lnp_unrestricted_implies_em`
  (commit `b81277a5c`, "the unrestricted least-number principle IS excluded
  middle"). Do not rebuild this.
- **Euler's theorem (`a^phi(n) = 1 mod n`) is NOT close**, contrary to
  ADR-0716's "one theorem away" framing, which is itself corrected by a
  sibling lane's own handoff: `docs/plan/status/374-euler-theorem.md`
  (status: PARTIAL) plus `int_prelude/euler_theorem.rs`'s module doc, both
  landed and merged (`f0453c65f`). `Int.prodRangeIf`/`Int.prodRangeIf_permute`
  are landed; three more genuinely hard pieces remain (Nat/Int index
  bridging, the IFF-converse of `euler_unit_coprime`, and final assembly).
  Not attempted by this lane — too large a bite alongside a second family,
  and actively claimed by another lane's handoff.
- **The classical Euclid-Euler even-perfect-number theorem (Euclid IX.36) is
  under ACTIVE multi-lane construction** in
  `nat_prelude/perfect.rs` (3702 lines as of this session; commits include
  "step 4 of the Euclid IX.36 chain", "Euclid IX.36's family non-overlap",
  etc., all recent and merged). `Nat.sumDivisors`, `Nat.Perfect`,
  `Nat.sumDivisors_two_pow`, `Nat.dvd_two_pow_mul_classify` are landed;
  `declare_perfect_all` does not yet wire up the full Euclid IX.36 result.
  **Not touched by this lane** — high collision risk with active work, deep
  existing proof architecture not worth re-deriving in one session.

Conclusion: picked a family away from the three hot areas above, using
already-landed but currently-unconnected infrastructure.

## Family A (in progress): Fermat's little theorem, contrapositive form — a computable compositeness certificate

New file: `crates/axeyum-lean-kernel/src/nat_prelude/fermat_witness.rs`
(not yet created as of this commit).

Plan:
1. `Nat.mod_eq_iff_mod_eq : forall d a b, Iff (ModEq d a b) (Eq (modulo a d) (modulo b d))`
   — bridges the existential balanced-witness `ModEq` to the EXECUTABLE
   `Nat.mod` comparison, built from two already-landed theorems:
   `mod_eq_iff_div_mod_remainder_eq` (`modular.rs`) instantiated with
   `div_mod_exec` (`division.rs`) supplying the `divMod` witness at both `a`
   and `b`. (No new induction — pure composition of landed lemmas.)
2. `Nat.not_prime_of_pow_mod_ne : forall p a, Not (Eq (modulo (pow a p) p) (modulo a p)) -> Not (Prime p)`
   — ADR-0603 row 1, general constructive form, true for every `p, a` with
   no restriction and no decidability principle beyond what already exists:
   direct contrapositive of the already-landed `Nat.pow_prime_modeq_self`
   (Fermat's little theorem), composed through step 1's bridge.
3. Row 2: none, argued from shape — this is a one-step modus tollens on an
   unconditional theorem; there is no comparison or search to extract a
   boundary from.
4. Row 3 (decidable/exact fragment): a concrete evaluation test
   instantiating `not_prime_of_pow_mod_ne` at small numerals that
   DISCRIMINATE (composite `p=4`, witness `a=3`: `3^4 mod 4 = 1 != 3 mod 4 = 3`,
   giving `Not (Prime 4)`), executed via kernel reduction plus
   `Nat.ne_of_beq_eq_false`. Positive control at prime `p=5, a=3`
   (`3^5 mod 5 = 3 = 3 mod 5`, consistent, antecedent false) to confirm the
   check does not fire on a genuine prime.

Not yet committed: the `.rs` file, the `NatPrelude` struct/init/dispatch
edits (3 minimal insertion points in the shared `nat_prelude.rs`), the fact
ledger entries, or the tests. This status file records the plan so a
successor (or this lane, resumed) can pick it up with full context if the
session ends before Family A is finished.

## Holdout isolation

Not yet run in this lane (nothing touches `artifacts/autogenesis/` yet).
Will run and report both before/after once any fact-ledger or nat_prelude
change is committed.

## Next steps

1. Implement `fermat_witness.rs`.
2. Wire into `nat_prelude.rs` (struct field, name init, dispatch call) —
   minimal diff, verify no other lane's hunk is touched.
3. `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — confirm nonzero,
   confirm previous count + new tests.
4. Register facts via `scripts/gen-kernel-facts.py --prelude nat`.
5. Decide on Family B given remaining time (candidate: a similar
   contrapositive/certificate family reusing already-landed `Int.wilson`/
   `Int.wilson_converse`, or another small self-contained corollary that
   does not touch `perfect.rs` or the Euler-theorem files).
