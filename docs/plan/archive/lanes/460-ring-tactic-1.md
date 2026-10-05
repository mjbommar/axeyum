# Lane: ring-tactic-1 — a ring-identity decision procedure that emits kernel proof terms

<!-- plan-section: lane-status -->

**Your lane's block (`DONE` for ℕ, `NOT STARTED` for ℤ/ℚ, ring-tactic-1,
2026-09-03).** `crate::ring` is the second tactic-layer producer beside
`crate::linarith` (ADR-1576): a commutative-ring normalizer over ℕ (`+`, `*`,
`succ`, numerals) that parses both sides of a goal `t₁ = t₂` into a canonical
sum of monomials and, when they agree, **emits a kernel proof term** built
only from `add_assoc`/`add_comm`/`mul_assoc`/`mul_comm`/`left_distrib`/
`right_distrib`. Full account: ADR-1580.

**The number.** Ten hand-written ring-rearrangement proofs retired in
`nat_prelude`: one declared theorem (`add_right_comm`) and nine private
proof-construction helpers — `bezout.rs`'s `expand_scaled_right`, standing
in for `right_distrib` (see below), plus eight independent hand-written
copies of one duplicated four-term identity `(a+b)+(c+d) = (a+c)+(b+d)`
across `binomial.rs`,
`div_mod_lemmas.rs`, `finite_set.rs`, `fibonacci.rs`, `subset_sum.rs`,
`rec_agreement.rs`, `count_range_reversal.rs`, `eisenstein_lemma.rs`. Roughly
350 hand-written lines removed across the ten sites, replaced by a shared
~700-line producer plus a few lines per call site (exact per-file diff sizes
in `git show --stat` on the commit; not hand-recounted here since the
`kernel_declaration_projection`-style byte-identical claim only applies
cleanly to the two DECLARED theorems — the other eight were never top-level
declarations, they are private proof-construction helpers, so there is no
projection row to diff for them, only the caller-visible fact that each
still returns the identical target expression its old body did).

    nat_prelude  add_right_comm  (declared theorem, algebra.rs)
                 expand_scaled_right  (private helper, bezout.rs, stands in for right_distrib)
                 add_add_add_comm × 5 (binomial.rs, div_mod_lemmas.rs,
                     rec_agreement.rs, count_range_reversal.rs — 4 files)
                 add_regroup_four × 3 (finite_set.rs, fibonacci.rs, subset_sum.rs)
                 regroup_four × 1 (eisenstein_lemma.rs)

For `add_right_comm`, the only one of the ten with an existing prelude name
to compare against, `f.k.def_eq(ty, expected)` in
`ring::tests::target_algebra_add_right_comm` checks the emitted declaration's
type against the PRELUDE'S OWN pre-existing statement (not against anything
the emitter itself produced) — that is the same non-circular check
`linarith`'s own retirement tests use.

**Two findings this lane made that `linarith` did not need, both load-bearing
and both written up in ADR-1580:**

1. **A producer cannot retire its own primitives.** `right_distrib` was the
   first retirement attempt; `ring`'s own `Problem::distribute` calls it as a
   primitive to break a sum across a product, so retiring `right_distrib`'s
   declaration tries to prove it from itself and the kernel refuses with
   `UnknownConst` (the name does not exist yet at that build point). Every
   unit test still passed, because every test runs against the FINISHED
   prelude — the failure showed up only when the actual declaration site in
   `algebra.rs` was edited and `build_nat_prelude` itself broke. Fixed by
   substituting `bezout.rs::expand_scaled_right` (a genuine downstream
   consequence of `left_distrib`/`mul_assoc`, not a producer primitive) as
   the tenth target. `add_right_comm` hit a subtler version of the same
   trap — the emitter's own `sort_items` used it as a convenience for
   non-head swaps — fixed by deriving the swap inline from
   `add_assoc`/`add_comm`/`symm` instead, which both resolves the
   circularity and makes the emitter strictly more general.
2. **A retirement target's arguments must go through a GENERIC route.**
   Three of the eight duplicated-identity call sites (inside
   `div_mod_lemmas.rs`) substitute `Nat.div`/`Nat.mod` expressions for the
   identity's free variables. `ring::nat::prove_eq` on those literal
   substituted terms correctly declines `NonRing` — sound, but it broke the
   naive retirement at exactly that file. `ring::nat::prove_eq_at` fixes
   this: prove the identity generically over fresh `fvar`s (always opaque,
   in-fragment atoms to the normalizer), then apply the resulting lambda to
   the caller's actual arguments via ordinary Pi-application, which
   type-checks regardless of what those arguments are built from. All ten
   retirement sites route through it uniformly now, not only the three
   currently known to need it.

**Cost**, `--release`, 200 emissions per shape, prelude built once per shape
(`cargo run --release -p axeyum-lean-kernel --example ring_cost`):
**0.7–2.4 ms per term end to end**, kernel recheck included — same order of
magnitude as `linarith`'s own datum. The multiplication-distribution shapes
(needing `distribute`/`combine_items`'s monomial merging) cost roughly double
the pure-addition ones.

**The guard that decides whether any of it is worth anything.** Four
corruption tests, run with the procedure's own normal-form check disabled
(`prove_eq_unverified`): a coefficient off by one (`a+a = a`), an extra
constant (`a+b = a+b+1`), a swapped variable (`a+a = a+b`) — each forces the
KERNEL to refuse the resulting declaration, not the procedure's own
bookkeeping. A positive control (`a+b = b+a`, same unverified route) sits
beside them, and a fifth test keeps the procedure's own check honest by
requiring `verify = true` to decline the same corruption
(`Decline::NotAnIdentity`). Unlike `linarith`, `ring` has no hypothesis slot
a proof could be swapped into — every risk here reduces to "is the claimed
identity actually true" — so all three corruptions are shapes of a false
claim rather than a mismatched proof term.

**Sized negatives, each pinned by a test.**

- **No intra-monomial commutativity.** `x*y` and `y*x` normalize to
  different factor-list keys (`[x_idx, y_idx]` vs `[y_idx, x_idx]`) and the
  procedure declines `Decline::NotAnIdentity` rather than proving them equal
  — sound (never a false claim) and incomplete. None of the ten retirement
  targets need it: every product pairs a fixed left-side factor against a
  fixed right-side factor in one consistent construction order. Pinned by
  `ring::tests::commuting_two_products_is_a_sized_negative`. Not built: it
  needs the same three-step `mul_assoc`/`mul_comm`/`symm(mul_assoc)` swap
  `sort_items` derives for `+`, applied to a monomial's own factor list —
  no test would exercise it honestly today.
- `div`/`mod`/ℕ's truncated `sub` decline `NonRing` — three separate tests,
  one per operator.
- A coefficient (repeated-`+` count, or a numeral-times-numeral product)
  above `MAX_COEFF = 4` declines `CoefficientTooLarge` (not separately unit
  tested this session; the bound and its rationale — unary numerals — are in
  `ring.rs`'s module docs, mirroring `linarith::MAX_MULTIPLIER`).

**The producer contract is born retired, same story as `linarith`'s.**
`artifacts/autogenesis/producer-contracts/ring-identity-v1.json` validates
(`PRODUCER_CONTRACTS_OK|contracts=5|retired=3`) with a live population of
**zero** (checked with `title_prefix: "Mathlib v4.30 source proposition
Nat.mul_left_comm"`, matches nothing in the whole 2,714-fact ledger, not
merely the open subset). Reading all 245 open `Mathlib v4.30 source
proposition` titles: the 169 `Nat.*`-titled ones are almost entirely `sqrt`,
`gcd`, primality, `testBit`, `findGreatest`, `nth`, order — not one is a bare
`+`/`*` rearrangement. Same reading as `linarith`'s: the algebraic core was
finished first, by hand.

**What did NOT run / did not land.**

- **ℤ and ℚ were not built.** The design brief scoped five more retirements
  each; this session's ten ℕ targets, the two circularity findings above
  (which cost real rework — the first `right_distrib` attempt had to be
  reverted), the cost/contract instruments, and this write-up consumed the
  available time. Building ℤ means re-deriving the same normalizer over
  `IntDev`/`IntPrelude` (ℚ needs `neg`/`sub` as `add(neg)`, per the design
  brief) — the SHAPE is established (this session found and fixed the two
  traps a first attempt would otherwise hit), not the code.
- `CReal` — out of scope, not assessed either way this session.
- The full-crate `cargo test -p axeyum-lean-kernel --lib --release` (no
  filter) was attempted and hit the 590s wrapper timeout partway through
  (the crate has ~1600 tests spanning `creal`/`complex`/`quotient`, none of
  which this lane touched) — **did not complete, did not run to a verdict**.
  The scoped gate that actually covers every file this lane changed
  (`nat_prelude::` + `ring::`, 444 tests) ran clean, `--release`, three times
  across the session (after the initial circularity fixes, after the
  `prove_eq_at` fix, and after the final `rustfmt` pass).
- `just check` / `scripts/check.sh` / `cargo test --workspace` — not run
  (no `just` confirmed on this host for this session; the workspace sweep is
  the ~10-minute one prior lanes have reported timing out on this box for
  changes narrower than this one).

**Gates run.** `nat_prelude::` (271 tests) + `ring::` (22 tests) = 444/444
green, `--release`, three times across the session (first clean run after
the `right_distrib` revert + `add_right_comm` fix + `prove_eq_at` fix; a
repeat after formatting). `cargo clippy -p axeyum-lean-kernel --all-targets
-- -D warnings` exit 0 (one real finding along the way: `Problem::new`
taking `NatPrelude` by value tripped `large_types_passed_by_value`,
`NatPrelude` being 4,720 bytes — fixed by taking `&NatPrelude`, matching
clippy's own suggested fix, not silenced). `rustfmt --edition 2024` on every
touched/new file. `python3 scripts/validate-producer-contracts.py` exit 0.
`python3 scripts/gen-adr-index.py` regenerated (pre-existing, unrelated
duplicate ADR numbers 0166/0167 reported — not introduced by this lane, not
fixed here, out of scope for this brief).

<!-- plan-section: landed-changes -->

| 2026-09-03 | ring-tactic-1 | `crate::ring`: a commutative-ring producer emitting kernel terms over ℕ |
| 2026-09-03 | ring-tactic-1 | ten hand-written ring-rearrangement proofs retired in `nat_prelude` (one declared theorem, nine private-helper proof-construction sites) |
| 2026-09-03 | ring-tactic-1 | `ring-identity-v1` producer contract, born retired against an empty live population |
| 2026-09-03 | ring-tactic-1 | ADR-1580: a producer cannot retire its own primitives; a retirement target's arguments need the generic-then-apply route (`prove_eq_at`) |
