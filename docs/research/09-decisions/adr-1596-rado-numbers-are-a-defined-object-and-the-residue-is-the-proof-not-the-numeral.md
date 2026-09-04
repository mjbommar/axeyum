# ADR-1596: Rado numbers are a defined object, and the residue is the proof, not the numeral

Status: accepted
Date: 2026-09-04
Index-summary: `Nat.Rado` defines Sol/IsColouring/MonoSol/Arrows/IsRadoNumber over `Nat.inClosedInterval` and `Nat.Finset`, parameterized over the bound so no large numeral is formed; `R_2(x=y+z)=5` is closed end to end from search; and the measured residue against the ledger's two `computed` four-colour values is the PROOF term, not the unary numeral — the statement `IsRadoNumber 5 3 4 625` type-checks.
Index-status: accepted

## Context

The fact ledger holds two four-colour Rado numbers with
`epistemic_status: computed`:

| fact | statement | evidence |
|---|---|---|
| [`F:rado-r4-a5-b3`](../../../artifacts/facts/F-rado-r4-a5-b3.json) | `R_4(5(x−y) = 3z) = 625` | a replayed lower-bound colouring and a DRAT refutation at `n = 625` (220,077,720 steps, 19.9 GB, checked in 14,499 s by this repository's own backward checker) |
| [`F:rado-r4-a5-b4`](../../../artifacts/facts/F-rado-r4-a5-b4.json) | `R_4(5(x−y) = 4z) = 741` | a complete adaptive cube cover of `F_741`: 6,241 cubes, every one refuted, covered measure exactly `4294967296/4294967296` |

Both are genuine extremal-combinatorics results — the `(5,4)` cell is blank in
Chang–De Loera–Wesley's Table 10 and their `external_status` is `open`.

**Nothing in the kernel said what a Rado number is.** So each was a number with
a certificate rather than a theorem about a defined object, and the two shelves
never met: the `Nat.Finset`/pigeonhole work is `proved`, the Rado work is
`computed`, and no declaration connected them. Three of the twelve standing
reviewers made closing that gap their first item, independently
([07.1](../../math-department/07-combinatorics.md),
[11.1](../../math-department/11-applied-and-computational.md), 12.4), which is
the C2 convergence and roadmap item **W1-1**.

The engineering constraint is stated in the same reviewers' files: every `Nat`
numeral in this kernel is unary, so cost is superlinear in the largest
magnitude *formed*, and `625` as `succ^625 zero` was assumed to put the ledger's
own results out of reach of any kernel statement. That assumption is the thing
this ADR measures.

## Decision

### 1. The object, over the range predicate that already existed

`crates/axeyum-lean-kernel/src/nat_prelude/rado.rs` declares, under `Nat.Rado`:

```text
Sol a b x y z        := a * x = a * y + b * z
IsColouring k n c    := ∀ i, Nat.inClosedInterval 1 n i → c i < k
MonoSol a b n c      := ∃ x y z, all three in [1,n] ∧ Sol a b x y z
                                 ∧ c x = c y ∧ c y = c z
Arrows a b k n       := ∀ c : Nat → Nat, IsColouring k n c → MonoSol a b n c
IsRadoNumber a b k n := Arrows a b k n ∧ ∀ m, m < n → ¬ Arrows a b k m
```

Three choices in that block are decisions rather than transcription:

**`Sol` is subtraction-free.** The family is Chang–De Loera–Wesley's
`a(x − y) = bz`, and the obvious transcription `a * (x - y) = b * z` is *wrong
in this kernel*: `Nat` subtraction truncates, so it is TRUE for every `x ≤ y`
at `z = 0`, and `Sol 5 3 1 2 0` would hold as `0 = 0`. The declared form makes
that instance `5 = 10`, which the kernel refuses. This is not a hypothetical —
the type of the two definitions is identical, both are axiom-free, and no
sweep in this repository distinguishes them.
`rado_tests::sol_is_subtraction_free_and_rejects_the_truncated_form` is the
only thing that does. The subtraction-free form is also the shape
[`tests/rado_sharp_factorization.rs`](../../../crates/axeyum-lean-kernel/tests/rado_sharp_factorization.rs)
already uses for the paper's `thm:sharp`.

**The range is `Nat.inClosedInterval 1 n i`, not a new predicate.** It existed
(`Nat.inClosedInterval lower upper value := Le lower value ∧ Le value upper`)
and `shape_search` found it; declaring an `InRange` would have been a fourth
spelling of the same proposition.

**Leastness is `∀ m < n, ¬ Arrows`, and monotonicity is what makes that
equivalent to "not at the predecessor".** `Nat.Rado.arrows_of_le` is the
monotonicity theorem; `Nat.Rado.isRadoNumber_of_succ` is the reduction
(below).

### 2. `Nat.Finset` is where the colouring certificate lives

A `k = 2` colouring of `[1,n]` **is** a finite set — the class of colour 1 —
and `Nat.Rado.ofFinset s` makes that literal as the indicator of
`Nat.Finset.memB s`. `Nat.Rado.isColouring_ofFinset : ∀ n s, IsColouring 2 n
(ofFinset s)` holds for **every** `Nat.Finset` at **every** range with no side
condition, because ADR-1577's `memB` truncates inside its own definition. So a
lower-bound certificate — a subset of `[1,n]` produced by search — transcribes
into the kernel with no well-formedness obligation of its own.

The one-line lemma underneath is `Nat.boolSelect_lt`, a `Bool.rec` case split
saying a `Bool`-selected value is below any bound both branches are below. It
is general and is declared under `Nat`, not `Nat.Rado`.

### 3. `isRadoNumber_of_succ` is the reduction a certificate needs

```text
Nat.Rado.isRadoNumber_of_succ :
  ∀ a b k m, Arrows a b k (succ m) → (Arrows a b k m → False)
           → IsRadoNumber a b k (succ m)
```

Those two hypotheses are **exactly** the two halves a Rado search produces: a
refutation at `n` (every colouring admits a monochromatic solution) and a
witness at `n − 1` (this colouring does not). `m` is a variable throughout, so
a certificate at `m = 624` instantiates it without any statement here being
restated and without the proof of *this* lemma growing by a single node.

### 4. One instance closed end to end, both halves reconstructed from search

`R_2(x = y + z) = 5` — the two-colour Schur number in Rado form, `a = b = 1`.

* **Upper bound**, `Nat.Rado.schur_arrows_five : Arrows 1 1 2 5`. The search
  enumerates the `2^5` colour assignments to `[1,5]` and finds the
  monochromatic triple for each; the proof term is the matching
  `Nat.lt_two_cases` decision tree, one `Or.elim` per index, with that triple
  at the leaf. **A leaf with no triple returns `None` and nothing is
  declared** — the builder cannot fall back to something weaker.
* **Lower bound**, `Nat.Rado.schur_not_arrows_four : Arrows 1 1 2 4 → False`.
  The search enumerates the `2^4` subsets of `[1,4]` and returns `{2,3}` — the
  partition `{1,4}/{2,3}`, which is the unique avoiding one up to swapping the
  colours; `Nat.Rado.schurSet` is that set. The refutation is by
  **reflection**: a `Bool` triple loop over `Nat.Finset.allBelow` that the
  kernel's own conversion check reduces to `true`, read back at the three
  existential witnesses by `Nat.Finset.allBelow_true_at`, then six `Eq.rec`
  transports landing on `Bool.false = Bool.true`. Nothing in the proof term
  asserts the loop is true; the trusted gate computes it.
* **Joined**, `Nat.Rado.schur_two : IsRadoNumber 1 1 2 5`, by
  `isRadoNumber_of_succ` at `m := 4`.

Seventeen declarations, every one admitted on the first attempt with an empty
`Kernel::axiom_footprint`.

## The residue against the ledger, measured

**The unary numeral is not the obstacle to the STATEMENT.** The standing rule
— cost is superlinear in the largest magnitude formed — is a rule about
*reduction*: `decide`'s `MAX_MAGNITUDE` is 30 because peeling a unary tower
costs real time. A `Prop` that merely mentions the numeral neither reduces it
nor unfolds anything. `rado_tests::the_statement_at_the_ledgers_own_constant_type_checks`
builds `Nat.Rado.IsRadoNumber 5 3 4 625` and `Nat.Rado.IsRadoNumber 5 4 4 741`
and has the kernel infer their types, in the same fixture and the same budget
as every other test in the file. Both are `Prop`. Both are distinguishable
from their neighbours one `succ` away.

So the ledger's two results **are** stateable in this kernel, verbatim, today.
What is missing is the proof term, and the reason is combinatorial, not
numeric:

| half | what a kernel term would have to be | size |
|---|---|---|
| upper, `Arrows 5 3 4 625` | a term ranging over every 4-colouring of `[1,625]`. Colourings are *functions*, so they are not enumerable in-kernel; the `Nat.lt_two_cases` tree that works at `k = 2` has `k^n` leaves | `4^625` |
| lower, `¬ Arrows 5 3 4 624` | the `allBelow` reflection route, which runs `(n+1)^3` triples of unary arithmetic against a `k = 4` colouring | `2.4 × 10^8` triples |

The lower half is the reachable frontier: it is the same construction as
`schur_not_arrows_four` with a `k`-valued `ofFinset` analogue, and its cost is
polynomial rather than exponential. The upper half is not reachable by any
route in this repository, and saying so is the honest form of the finding —
the DRAT certificate for `F_625` is 220 million steps and 19.9 GB, and a
kernel proof term is not a smaller object than the proof it records.

**Consequence for the ledger: both facts stay `computed`.** A kernel
definition of the object is not a kernel proof of the value. What changes is
that their statements now *have* a formal home, which is recorded in each
fact's notes and in the new `F:rado-r2-schur-two` row.

## Consequences

- The `computed`→`proved` route for a Rado number now exists and is
  demonstrated. What a future certificate has to produce is named exactly:
  two terms of type `Arrows a b k (succ m)` and `Arrows a b k m → False`.
- The two shelves meet. `Nat.Finset` (ADR-1577) is load-bearing in a
  combinatorics theorem rather than only in cardinality arithmetic, which is
  what [07-combinatorics.md](../../math-department/07-combinatorics.md) asked
  for.
- A general lower-bound theorem is now cheap to state and is the obvious next
  increment: Chang–De Loera–Wesley's Lemma 4.1 (`R_k ≥ a^k` by the `a`-adic
  valuation colouring, for `gcd(a,b) = 1` and `a ≥ b + 2`) is a *parameterized*
  statement whose proof forms no constant at all, and it would back the lower
  half of `F:rado-r4-a5-b3` as a theorem rather than a replay. This ADR does
  not do it; it records that nothing blocks it.
- Cost: the module adds 17 declarations to a prelude every kernel test builds.
  The measured build delta is recorded in
  [`docs/plan/status/501-rado-in-kernel.md`](../../plan/status/501-rado-in-kernel.md);
  the largest magnitude any *proof* here forms is `5`.

## Alternatives rejected

**State the Rado number as an equality `R k E = n` with `R` a function.**
Would need `R` to be *defined*, i.e. a least-element search over a
non-decidable predicate (`Arrows` quantifies over functions). `IsRadoNumber` as
a relation says the same thing with no such obligation, and it is the form the
certificate discharges.

**Prove the instance by `decide` on a closed proposition.** `Arrows` is not a
closed `Bool`; it quantifies over `Nat → Nat`. The reflection route in
`schur_not_arrows_four` is the closest thing available and it works only for
the *lower* half, where the colouring is fixed.

**Put the instance in a test file rather than the prelude**, as
`tests/rado_sharp_factorization.rs` does for the paper's algebra. Rejected: a
theorem in a test file is admitted by the same trusted gate but is not in the
declaration inventory, so it does not appear in the metric the reviewers asked
about. The build-cost price is recorded instead of avoided.
