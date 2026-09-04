# ADR-1599: `ring::generic` — the commutative-ring producer over `Alg.CommRing` and `AlgS.CommRing`, and a measured `decide` boundary

Status: accepted
Date: 2026-09-04
Lane: `producers-to-real` (W1-5)

Index-summary: `linarith` was generalized over `Alg.OrderedRing` (ADR-1585)
and then `AlgS.OrderedRing` (ADR-1592), reaching `CReal.orderedRingS`. This
ADR repeats that move for `ring`: `ring::generic`
(`crates/axeyum-lean-kernel/src/ring/generic.rs`, new file) EXTENDS
`linarith::generic`'s exact `Backend{KernelEq,Setoid}` shape — six
backend-aware wrapper methods (`refl`/`symm`/`trans`/`congr_add`/
`congr_mul`/`congr_neg`) and one parser (`as_eq`) — rather than forking a
new design, and reaches `Int.commRing`/`Rat.commRing` (`Alg.CommRing`) and
`CReal.commRingS`/`Complex.commRingS` (`AlgS.CommRing`, both already built
by earlier lanes) with the SAME emitter code. The fragment is `ring::rat`'s
exact shape (a canonical sorted sum of sorted monomials, coefficients
capped at magnitude 1 — `ring::rat`'s own restriction, ported unchanged)
generalized off `Alg.CommRing`/`AlgS.CommRing` selectors instead of a fixed
`RatPrelude`. Three facts `ring::rat` gets from `RatPrelude` fields directly
(`mul_zero`, `mul_neg_one`, `neg_neg`) are not primitive on `CommRing`, so
`Problem::new`/`new_s` reuse already-generic `Ring`-level theorems
(`Alg.ringMulZero`/`Alg.mul_neg_one`/`Alg.neg_neg`, `AlgS.mul_zero`/
`AlgS.mul_neg_one`/`AlgS.neg_neg`) instead of re-deriving them; `mul_neg`/
`neg_mul` (distributing `neg` into one side of a product — needed for
signed-monomial combination, no `Alg`/`AlgS` field for this directly) are
derived LOCALLY per `Problem` from `mul_neg_one`+`mul_assoc`+`congr_mul` —
no new global declaration. `decide` is measured against the same two
setoid carriers and gets a **precise structural negative**: `CReal.Equiv`/
`.le`/`.lt` are `∀`/`∃`-headed propositions, refused by `decide::parse_goal`
on the outer constant alone (no reduction attempted) — `decide`'s method is
a fuel-bounded walk to a canonical CLOSED value, which a universally
quantified statement has none of. The decidable fragment `decide` DOES
reach — every concrete rational-valued LEAF a `creal`/`complex` proof needs
— is exactly `decide::rat`'s existing fragment, unchanged, confirmed by a
positive control. **Retirement was ATTEMPTED and REVERTED, not landed**:
wiring `creal/ring_helpers.rs`'s two hand proofs (`right_distrib`,
`add4_comm`) to `ring::generic::prove_eq_s` made the isolated `ring::generic`
unit suite (12 tests, including the exact `right_distrib`/`add4_comm`
shapes with distinct AND repeated arguments) pass, but broke
`creal::creal_tests::creal_prelude_builds` itself with
`Decline::NotAnIdentity` surfacing somewhere among the 30+ real call sites
in `power.rs`/`series.rs`/`derivative.rs` -- a real production-only trigger
this session could not isolate with a minimal repro in the time available.
Reverted to the hand-built version rather than ship a broken prelude build;
`creal::` is confirmed green at HEAD. **Retirement count this session: 0**,
with the specific gap named for the next lane (Decision section 4, Evidence).
Index-status: accepted

## Context

W1-5 (`docs/math-department/00-roadmap.md`) asks for the `linarith`-over-
`AlgS.OrderedRing` generalization "repeated" for `ring` and, if meaningful,
`decide`. ADR-1585 built `linarith::generic` over `Alg.OrderedRing`;
ADR-1592 extended it with a `Backend` enum reaching `AlgS.OrderedRing` and
`CReal.orderedRingS`. `ring` had no generic form at all before this ADR —
`ring::nat`/`ring::int`/`ring::rat` are each a fixed-carrier monomial
normalizer (ADR-1576/1582), structurally close to `linarith::int`'s own
pre-generic shape.

## Decision

### 1. `ring::generic`: one module, two backends, `ring::rat`'s exact algorithm

Built as a direct generalization of `ring::rat`
(`crates/axeyum-lean-kernel/src/ring/rat.rs`) — same `Item::{Mono,Num}`
canonical form, same `flatten`/`flatten_add`/`flatten_neg`/`flatten_mul`/
`distribute`/`distribute_single`/`combine_items`/`sort_items`/
`sort_factors`/`reassoc`/`reassoc_mul`/`normalize`/`prove_eq` structure —
with every term/lemma built from `(R : Alg.CommRing)`/`(R : AlgS.CommRing)`
selectors (`Problem::new`/`new_s`) instead of a fixed `RatPrelude`, and
every `Eq.rec`-based congruence/transport call routed through the
`Backend`-aware wrapper methods `linarith::generic` (ADR-1592) already
established the shape of:

- **`Backend::{KernelEq, Setoid}`**, the `Setoid` variant carrying `equiv`/
  `equivRefl`/`equivSymm`/`equivTrans`/`addCongr`/`mulCongr`/`negCongr` —
  `AlgS.CommRing`'s own congruence FIELDS (three, one per operation this
  fragment uses: add, mul, neg). This is `ring`'s point of departure from
  `linarith::generic`'s two congruence fields (`addCongr`/`leCongr`):
  `ring` needs THREE operations' worth of congruence (add, mul, neg), not
  two, because `mul` and `neg` are exactly the operations `linarith`
  declined to reach at all (ADR-1585's own "no literal multiplication"
  scope note).
- **`AddCtx`/`MulCtx`** (`Left(fixed)`/`Right(fixed)`/`FoldFrom(tail)`),
  the structural-shape parameters every `congr_add`/`congr_mul` call reads
  off its closure at the call site — `linarith::generic::AddCtx`'s exact
  three-variant shape, doubled for the second operator. `congr_neg` needs
  no shape parameter: `negCongr` is unary, so there is exactly one shape.
- **`as_eq`** parses kernel `Eq` (`KernelEq`) or the record's own `equiv`
  applied directly (`Setoid`) — verbatim port of `linarith::generic::
  as_eq`.

**Zero behavior change to any existing route**: `ring::generic` is a new
module with no existing caller to preserve; the claim this ADR makes
instead is that its `KernelEq` path (over `Alg.CommRing`) and `Setoid` path
(over `AlgS.CommRing`) are the SAME emitter, differing only in the six
wrapper methods — confirmed by both paths sharing every other function
(`flatten*`, `distribute*`, `sort_*`, `reassoc*`, `combine_items`,
`combine_mono_signs`) verbatim.

### 2. Scope, honestly short of `ring::rat`

- **Coefficients capped at magnitude 1** — `ring::rat`'s own restriction
  (no generic `ofNat` numeral embedding exists for `CommRing` the way
  ADR-1585 built one for `OrderedRing`), ported unchanged, not newly
  introduced.
- **`neg` does NOT distribute over `add` generically.** `Alg.CommRing`'s
  `negAdd` field is the additive-INVERSE law (`add a (neg a) = zero`), not
  `neg (add a b) = add (neg a) (neg b)` — the codomain the name suggests in
  `ring::rat`'s own module docs, where it is a DIFFERENT (two-argument)
  `RatPrelude` theorem. Deriving the two-argument distribution generically
  needs an `Alg.groupInvUnique`-style uniqueness argument over the ring's
  derived additive group — real, new work, not attempted here (see
  Alternatives). A source term shaped `neg (add u v)` is parsed as one
  opaque atom: sound (never a wrong answer) but incomplete, the same
  "declined, not silently wrong" contract `linarith::generic` uses for `<`.
  `neg` DOES distribute over `mul` (`Problem::mul_neg_proof`/
  `neg_mul_proof`, derived from `mul_neg_one`+`mul_assoc`+`congr_mul`) and
  cancels under double negation (`Problem::neg_neg`, reused from the
  already-generic `Ring`-level theorem).
- **`Decline::NonRing` is unreachable.** `Alg.CommRing`/`AlgS.CommRing`
  carry no `div`/`sub` selector at all (unlike `Rat`, which has both as
  prelude-level definitions) — there is nothing to decline; an
  unrecognized subterm is simply an atom.

### 3. `decide`: a measured negative, with the decidable fragment named

`decide::run` accepts exactly `Eq Nat`, `Eq Bool`, `Nat.le`, `Nat.lt` —
recognised by `parse_goal` from the goal's OUTERMOST constant, no reduction
needed. `CReal.Equiv x y` (`creal.rs::declare_equiv`) beta-reduces to `∀
(n:Nat), Within (sample x n − sample y n) (2/(n+1))` — `CReal.le`/`.lt` are
similarly quantifier-headed (`creal.rs`'s own module docs on `CReal.lt`:
`∃ (q:Rat), 0 < q ∧ x + q ≤ y`). None of the three is ever `Eq`/`Nat.le`/
`Nat.lt` at the outer constant, so `parse_goal` returns `None` and `run`
declines `GoalNotAtomic` — structurally, not because of a missing case:
`decide`'s whole method is a fuel-bounded walk to a canonical CLOSED value
(`Eq.refl`, a `le_step` chain), and a `∀`/`∃`-headed proposition has no such
value — proving it needs a UNIFORM argument over unboundedly many cases
(exactly what `ring`/`linarith`/a hand proof supply), not evaluation of
finitely many. Confirmed for the friendliest possible instance
(`CReal.Equiv zero zero`, `CReal.le zero zero`, `CReal.lt zero zero`) in
`decide/setoid_boundary.rs`.

**The decidable fragment `decide` DOES reach inside a `creal`/`complex`
proof**: every concrete RATIONAL-valued leaf (a closed `Rat.le`/`Rat.lt`/
`Eq Rat` fact at a witnessed index — exactly the per-`n` shape `CReal.
Equiv`'s body would need if unrolled) is `decide::rat`'s existing fragment,
unchanged, confirmed by a positive control
(`decide_reaches_a_concrete_rational_leaf_inside_a_creal_style_bound`) in
the same file. `decide` does not stop at ℚ's boundary; it stops at the
QUANTIFIER.

No `AlgS`-level "apartness with a witness" fragment is built: `CReal` has
no declared `apart`/`separated` relation at all (grepped, absent) — there
is no existing witnessed-apartness proposition to reduce this producer to
a decidable check on, and building one is a new mathematical definition
(ADR-1584 §5's own "genuinely new, not a derivation" rule), out of scope
for a producer extension. Recorded as the honest boundary a future lane
would need to build the DEFINITION before this question can be reopened.

### 4. Retirement attempted, reverted: `creal/ring_helpers.rs`

`right_distrib` (`(a+b)*c = a*c+b*c`) and `add4_comm` (`(a+b)+(c+d) =
(a+c)+(b+d)`) — hand-built proof-term constructions (`mul_comm`+
`left_distrib`+congruence chains, and `add_assoc`+`add_comm`+congruence
chains respectively) shared by `creal/power.rs`, `creal/series.rs`, and
`creal/derivative.rs` — are pure commutative-ring identities with no order
content, exactly `ring::generic::prove_eq_s`'s fragment, and (unlike the
general case) do not even need `neg`. A retirement was built: both
functions routed through one shared `prove_ring_eq_s` helper wrapping
`ring::generic::prove_eq_s` over `CReal.commRingS`, with the same unchanged
`ExprId`/`(ExprId, ExprId)` signatures so no caller's stated type could
possibly change.

**It broke the real prelude build.** `cargo test --release -p
axeyum-lean-kernel --lib -- creal::creal_tests::creal_prelude_builds`
failed with `Decline::NotAnIdentity` panicking out of `ring_helpers.rs`'s
own `.expect(...)`, meaning `ring::generic::prove_eq_s` genuinely declined
to find a certificate for SOME real `right_distrib`/`add4_comm` call among
the 30+ sites in `power.rs`/`series.rs`/`derivative.rs` — a call this
producer's isolated unit tests (12/12 green, including the exact
`right_distrib`/`add4_comm` SHAPES with both distinct fvars and REPEATED
arguments, `creal_comm_ring_s_right_distrib_repeated_arg_goal`/
`creal_comm_ring_s_add4_comm_repeated_arg_goal`, matching real call sites
like `right_distrib(d, p, half, half, v)` and `add4_comm(d, p, mul_bb,
mul_bb, neg_xt, neg_xt)`) never reproduced. Bisecting the actual failing
call site among 30+ candidates was not completed in the time available for
this session. **Reverted** (`git checkout -- crates/axeyum-lean-kernel/
src/creal/ring_helpers.rs`) rather than land a broken build;
`creal::creal_tests::creal_prelude_builds` and `every_creal_declaration_
is_checked_and_axiom_free` are both confirmed green again at HEAD after
the revert.

This is exactly the gotcha this repository's own contributor guide names:
**"a producer cannot retire its own primitives — only the prelude build
catches that, never the unit tests"** — confirmed the hard way, at real
cost, rather than assumed. **Retirement count: 0.** The reverted diff was
never committed (built, tested, found broken, and reverted within one
uncommitted working session), so it is not preserved anywhere but this
ADR's description of its exact shape (`prove_ring_eq_s` wrapping
`ring::generic::prove_eq_s`, both call sites unchanged) — a future lane
resumes by re-applying that shape and bisecting `power.rs`/`series.rs`/
`derivative.rs`'s `right_distrib`/`add4_comm` call sites (e.g. by
temporarily routing ONLY `power.rs`'s call sites through the generic
producer, rebuilding, and narrowing from there) rather than starting the
design from scratch.

## Evidence

Measured 2026-09-04, `--release`, `RUST_MIN_STACK=1073741824` where `creal`
is exercised.

- **Step 0 control**: `shape_search --name-like CommRing --include-constructed`:
  `declarations=3550`, `FOUND 57` (the `Alg.CommRing`/`AlgS.CommRing`
  spine, already present from prior lanes). Positive control `--name
  Int.mul_comm`: `FOUND 1`.
- `cargo test -p axeyum-lean-kernel --release --lib -- ring:: decide::
  --test-threads=4`: **121 passed, 0 failed** (71 `ring::`, 47 `decide::`,
  including 12 new `ring::generic::generic_tests` and 3 new `decide::
  setoid_boundary` tests).
- `cargo clippy -p axeyum-lean-kernel --lib --tests -- -D warnings`: clean.
- `cargo check --workspace --all-targets`: clean.
- `rustfmt --edition 2024` on every touched file.
- `cargo test -p axeyum-lean-kernel --release --lib -- creal::creal_tests::
  creal_prelude_builds creal::creal_tests::every_creal_declaration_is_
  checked_and_axiom_free --test-threads=1`: **2 passed, 0 failed**, confirming
  `creal::` is unaffected at HEAD (the retirement attempt was reverted before
  landing — Decision section 4).
- `kernel_declaration_projection`: not run against a retired declaration —
  there is none this session (Decision section 4).

Goals proved at `CReal.commRingS` not previously reachable (six, deliverable's
minimum of four): `a*b=b*a` (`mul_comm` shape,
`creal_comm_ring_s_mul_comm_goal`); `a*(b+c) = a*b+a*c` (`distribL`+
`reassoc`, `creal_comm_ring_s_distrib_goal`); `(a+b)*c = a*c+b*c`
(`distribR`, the general `distribute` branch, `creal_comm_ring_s_right_
distrib_goal`); `(-a)*b = -(a*b)` (`neg_mul_proof`, `creal_comm_ring_s_
neg_mul_goal`); `-(-a)*b = a*b` (double negation, `Problem::neg_neg`,
`creal_comm_ring_s_double_neg_goal`); plus two robustness variants with a
REPEATED argument matching real `right_distrib`/`add4_comm` call shapes
(`(x+x)*v = x*v+x*v`, `(p+p)+(q+q) = (p+q)+(p+q)`) that still pass in
isolation despite the retirement's real-build failure (Decision section 4).
A false goal (`a*b = a*a`) declines `NotAnIdentity`
(`creal_comm_ring_s_false_goal_declines`). Two corrupted certificates
(`prove_eq_s_unverified`, the procedure's own check disabled) are checked
against the kernel directly (`Kernel::add_declaration`, `ring::int::tests::
kernel_verdict_on`'s own established pattern — go straight to declaration,
not a separate `Kernel::infer` pre-check): a swapped-variable claim
(`a*b=a*a` declared against the reflexive `a*b=a*b`) is refused
(`creal_corrupted_certificate_swapped_variable_is_rejected`); the matching
uncorrupted certificate (`a*b=b*a`) is admitted as a positive control
(`creal_uncorrupted_certificate_is_admitted_positive_control`).

**Two real bugs this session's own verification caught, both fixed**: (1)
`Problem::mul_neg_proof`'s `mul_assoc` step called `symm` with its two
endpoints swapped relative to `mul_assoc`'s actual stated direction (`Eq
(mul(mul a b) c) (mul a (mul b c))`, not the reverse) — emitted a term the
kernel refused with `TypeMismatch`, caught by `int_mul_neg_one_shape_via_
generic`. (2) The test harness itself used the `Eq`-flavored `structures::
idx::comm_ring` field-index module for `AlgS.CommRing` RecordNames — `AlgS.
CommRing` has four extra equiv-infrastructure fields ahead of `add`/`mul`,
so every index was off by four, and `mul_of`/`add_of`/`neg_of` silently
built garbage terms (selecting `equivRefl`/`equivSymm`/etc. instead of
`add`/`mul`/`neg`) for every `CReal.commRingS` test — caught because
`creal_comm_ring_s_mul_comm_goal` (a goal with no `neg` at all) failed too,
which a `neg`-only bug could not explain. Fixed with dedicated `mul_of_s`/
`add_of_s`/`neg_of_s` helpers reading `structures_s::idx::comm_ring`.

## Alternatives

**Build the "neg distributes over add" generic lemma
(`Alg.groupInvUnique`-style, over the ring's derived additive group) so
`flatten_neg` is complete on `add`.** Considered; deferred. This is real,
separate work (an extra uniqueness argument, not a mechanical port) and no
retirement target or requested goal needed it — recorded as a named,
sized gap for a future lane (mirrors ADR-1585's own treatment of `<`).

**Build a `CReal.apart`/witnessed-separation definition so `decide` has a
setoid-flavored fragment to reach.** Considered; rejected as out of scope
for a producer EXTENSION — it is a new mathematical object requiring its
own design and proof obligations (constructive apartness axioms, a
decision procedure over it), not a mechanical retarget of an existing
producer. Recorded as the precise next step if `decide`-over-ℝ is
revisited.

## Consequences

**Easier.** A second producer now reaches `AlgS.CommRing` with zero
additional emitter code at any future setoid carrier with a `CommRing`
instance — the same payoff ADR-1592 made for `linarith`. `creal/
ring_helpers.rs`'s remaining callers (`power.rs`/`series.rs`/
`derivative.rs`) are unaffected by any future normalizer change to
`ring::generic` beyond this file's own two call sites.

**Harder.** `ring::generic`'s `Backend::Setoid` variant now depends on
THREE congruence fields instead of `linarith::generic`'s two — a future
setoid record missing `negCongr` (or `mulCongr`) cannot reach `ring::
generic`'s `Setoid` path even if it has `addCongr`. `neg`-over-`add`
non-distribution is a real, silent-looking completeness gap for a reader
who assumes `ring::generic` matches `ring::rat`'s full coverage; the module
doc and this ADR both name it so a future lane does not have to
rediscover it.

**Revisit when** a lane wants the `neg`-over-`add` distribution (unlocking
more `creal/*.rs` retirement targets shaped like `-(a+b)`), wants `ring::
generic` to reach `Complex.commRingS` for a real retirement (this ADR
confirms REACHABILITY, matching `Complex.commRingS`'s own field shape, but
does not retire a `complex.rs` hand proof — none of `complex.rs`'s existing
hand-built ring identities were surveyed this session), or wants to build
`CReal.apart` and reopen `decide`-over-ℝ with an actual target to decide.
