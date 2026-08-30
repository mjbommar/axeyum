# graded-families-number-theory — lane status

<!-- plan-section: lane-status -->

Status: DONE for this session. One complete graded family landed (rows 1
+ 3, row 2 argued absent), both declarations axiom-free, both facts
registered and validated, ADR-0825 records the reasoning. Family B was
NOT attempted -- see "Why only one family" below.

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

## Family A (landed): Fermat's little theorem, contrapositive form — a computable compositeness certificate

Detail moved to [`../notes/graded-families-number-theory.md`](../notes/graded-families-number-theory.md).

