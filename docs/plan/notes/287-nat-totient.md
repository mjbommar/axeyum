# Notes: 287-nat-totient

Detail moved out of [`../status/287-nat-totient.md`](../status/287-nat-totient.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Mirror-flip check.** Read `Mathlib/Data/Nat/Totient.lean:38` at the pinned
v4.30 commit (`c5ea0035…`, checked out at
`/data0/axeyum/lean-import-toolchain/mathlib4`): `def totient (n : ℕ) : ℕ :=
#{a ∈ range n | n.Coprime a}` — the cardinality of the coprime-to-`n` subset
of `range n = [0,n)`. This kernel's `Nat.totient n := countRange (fun k =>
beq (gcd k n) 1) n` is the SAME construction (count over `[0,n)` filtered by
a coprimality predicate), differing only in `gcd`'s argument order
(`gcd k n` vs Mathlib's `gcd n a`, the same proposition by commutativity).
**Every mirror in this family is an honest flip target in principle** —
what blocks eight of the nine is proof difficulty over an honest statement,
not a definitional mismatch. Full reasoning, restated per-mirror, is in
`crates/axeyum-lean-kernel/src/nat_prelude/totient_lemmas.rs`'s module doc.

**Closed, 1 of 9 — `F:ml430-nat-totient-eq-zero-3be161d6`.** `∀ n,
Iff (totient n = 0) (n = 0)`. New building block:
`Nat.coprime_succ_self : ∀ m, gcd m (succ m) = 1` (consecutive naturals are
coprime), which fell out cheaply from three already-declared facts with no
new induction — `coprime_add_self_right(m, 1)` plus `coprime_one_right_iff(m)`
give `gcd m (add 1 m) = 1` unconditionally, and `add 1 m = succ m` via
`succ_add`/`zero_add` congr'd through `succ`. `totient_eq_zero` then
case-splits `n` (`cases_zero_succ`, no induction hypothesis): `n = 0` is the
`countRange` base case by pure `Eq.refl`; `n = succ k` uses the range's own
TOP index `k` as the witness (`coprime_succ_self k` promotes the predicate
at `k` to `true` via `beq_eq_true_of_eq`, so `countRange`'s succ-case
defining equation makes `totient (succ k)` defeq `succ (countRange f k)` —
never `0`, matching `succ k` itself never being `0`) — both `Iff` legs close
by `ex_falso`. No existence/counting machinery beyond the top-index witness
was needed. New file `crates/axeyum-lean-kernel/src/nat_prelude/totient_lemmas.rs`.

**Open, 8 of 9 — triaged, not attempted, and why (all detail in the module
doc, summarized here):**

- **`totient_eq_one_iff`** (`totient n = 1 ↔ n = 1 ∨ n = 2`): reverse
  direction is cheap (concrete `def_eq` computation, like
  `totient_computes_on_small_numerals`). Forward direction needs a SECOND,
  DISTINCT coprime witness below the top index once `n ≥ 3`, plus a lemma
  this prelude does not have: "two distinct true witnesses below `n` give
  `countRange f n ≥ 2`". The top-index technique above only ever produces
  `≥ 1`, by construction.
- **`totient_even`** (`2 < n → Even (totient n)`): needs the classical
  fixed-point-free-involution pairing argument (`k ↦ n - k` on the coprime
  residues) — `totient.rs`'s own module doc already calls this out as
  separate, larger work. Not machinery this prelude has for a
  `Bool`-predicate-defined subset of `[0,n)`.
- **`odd_totient_iff`**, **`odd_totient_iff_eq_one`**: both reduce to
  `totient_eq_one_iff` combined with `totient_even` — blocked on both.
- **`totient_coprime_totient_iff`**: the "if" direction is cheap; the "only
  if" direction's contrapositive needs `totient_even` at both arguments.
  Blocked on `totient_even`.
- **`eq_or_eq_of_totient_eq_totient`**, **`totient_gcd_mul_totient_mul`**:
  both need real structural results connecting `totient` to
  multiplication/divisibility — standardly the multiplicative formula
  `totient(m*n) = totient(m)*totient(n)` for coprime `m,n` (a CRT-style
  bijection argument) or an equivalent prime-power decomposition. Neither
  exists in this prelude; building it is a project on the scale of
  `totient_even`'s pairing argument, not a slice of this one.
- **`totient_dvd_of_dvd`**: also standardly proved via the multiplicative
  formula. Same blocker.

So the honest shape: one closed, and the rest bottleneck on one of two
missing pieces of real infrastructure (a general
existence-witness-to-positive-count lemma — small, unlocks
`totient_eq_one_iff`'s forward direction and `dvd_two_of_totient_le_one`;
the fixed-point-free-involution pairing argument for `totient_even` — large,
additionally unlocks `odd_totient_iff{,_eq_one}` and half of
`totient_coprime_totient_iff`) plus the multiplicative formula (largest,
needed by `totient_gcd_mul_totient_mul`, `totient_dvd_of_dvd`, and the other
half of `eq_or_eq_of_totient_eq_totient`).

**Verification.** `cargo test -p axeyum-lean-kernel --lib nat_prelude::` —
**161 passed, 0 failed** (159 baseline + two new tests,
`coprime_succ_self_applies_at_a_concrete_instance_and_symbolically` and
`totient_eq_zero_applies_at_zero_a_concrete_successor_and_symbolically`,
each instantiated concretely with a discriminating negative control
(`gcd 4 6 ≠ 1`, `totient 5 ≠ 0`) AND against a genuinely free variable via
an explicit `LocalContext` + `Kernel::infer_in` — a bare unregistered
`FVar` is `UnboundFVar` to `Kernel::infer` directly, which is what the first
draft of these tests hit and is recorded as a discovery in the commit
history, not left undocumented). `cargo fmt --all --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both
clean. `python3 scripts/check-test-attribute-integrity.py`: 0 findings.
`python3 scripts/validate-facts.py`: 0 errors. `the_build_is_deterministic`'s
pin moved from `93 + 524` to `93 + 526` (two new theorems), taken from the
panic message's own mismatch (619 vs 617), not hand-incremented.

`F:ml430-nat-totient-eq-zero-3be161d6` flipped to `proved`,
`proof_route: kernel-lean`, `axiom_footprint: []`, with a kernel-term
evidence row (`nat_theorem_inventory -- totient_eq_zero`, verified both to
pass for real — count 1 — and to fail on a mutated name — count 0, exit 1)
and an exhaustive-enumeration axiom-freedom row
(`nat_axiom_inventory --require-axiom-free nat`, exit 0). `Nat.coprime_succ_self`
is a direct theorem dependency of `totient_eq_zero`
(`theorem_dependency_inventory Nat.totient_eq_zero`) with no fact ledger
entry of its own — an unregistered nat-prelude theorem, not an axiom, per
the empty-footprint evidence; noted in the fact's `notes` field rather than
silently omitted.

**Commits** (not pushed): `4df14e45d` (wip: the two declarations, build
unverified — landed within the first ten tool calls per the session rule),
`eaeab9d5a` (borrow-checker + clippy doc-lint fixes, the two concrete+
symbolic tests, the determinism-pin recount, and coverage-list
registration), `978c1fd18` (the fact-ledger flip). This status file is
uncommitted as of writing it — commit it together with `PLAN.md`
regeneration before ending the session.

**For the next lane on this family:** the two missing infrastructure pieces
above are the actual blockers, not proof difficulty on any individual
mirror beyond them. `dvd_two_of_totient_le_one` is the cheapest next target
once the existence-witness-to-positive-count lemma exists (its contrapositive
needs the same "second distinct witness below `n`" argument
`totient_eq_one_iff`'s forward direction needs). `totient_even` is the
higher-leverage build (unlocks three more mirrors transitively) but is a
genuinely larger slice — size it as its own task, not a continuation of
this one.
