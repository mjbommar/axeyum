# ADR-1075: The curriculum graph measures scenarios, not the kernel — so it gets a second axis rather than a status flip

Status: accepted
Date: 2026-08-31
Index-summary: `docs/curriculum/curriculum.toml`'s `status` field is the
SCENARIO axis and nothing else -- `mathtour.rs` defines `Status::Covered` as
"has a self-checking exercise family today" and a test enforces it, while
`LeanHorizon` means "primarily a proof-reconstruction target, not a
benchmark". Neither value says anything about what the Lean-core kernel has
PROVED, and read as if it did the two axes disagree in OPPOSITE directions
across the destinations: measured 2026-08-31 over 2,562 axiom-free
declarations, `calculus` is `lean-horizon` with 349 kernel declarations (the
largest node after `naturals`) while `linear-algebra` is `covered` with 55.
Rejects the status flip -- flipping `calculus` to `covered` would assert a
scenario family that does not exist and would break
`covered_nodes_have_a_family_realized_by_a_self_checking_scenario` -- and
adds a measured `kernel_decls` field per node instead, produced by
`scripts/measure-curriculum-kernel-coverage.py` whose exit status depends on
the finding. Repairs four summaries that were false rather than merely
incomplete (`calculus` said "epsilon-delta is Lean-horizon" while carrying
the FTC, MVT, Rolle, IVT, EVT and the Weierstrass M-test) and the
`calculus.md` destination page, which the 2026-08-30 correction sweep missed
even though it fixed both siblings. Also records three stale NEGATIVES found
in the process, two of them this lane's own, and one subject -- 47
declarations of probability through the weak law of large numbers -- that the
23-node graph has no node for at all
Index-status: accepted

Related: ADR-0033 (the double-duty educational artifacts this graph serves),
ADR-0512 (`CReal`, the constructed reals at trusted surface 0), ADR-0522
(`Real` -> `AxReal`, the rename that keeps the axiomatized package
distinguishable), ADR-0716 (row two of a decidable subject; the graded
families the destination docs cite), ADR-0845/ADR-0865 (the infrastructure
frontier and the dispatcher that reads this file)

## The finding

`docs/curriculum/curriculum.toml` is the machine-readable curriculum DAG: 23
nodes, layers 0 (foundations) through 3 (three destinations). Four of its
nodes carry `family = ""` and `status = "lean-horizon"`, which reads as *"we
do not have this."*

Measured against the kernel on 2026-08-31 — `kernel_declaration_projection`,
2,562 distinct declarations across every kind, every one axiom-free — the two
axes disagree in **opposite directions** on the two destinations that are not
analysis:

| destination | `status` | `family` | kernel declarations |
|---|---|---|---|
| `calculus` | `lean-horizon` | `""` | **349** (294 theorems, 46 definitions) |
| `linear-algebra` | `covered` | `LinearAlgebra` | **55** |
| `number-theory` | `covered` | `NumberTheory` | 105 (+151 divisibility, +104 modular) |

`calculus` is the largest node in the graph after `naturals`. It carries
`CReal.integral` with additivity and integration by parts, the fundamental
theorem (`integral_eq_antideriv_diff`), `HasDerivativeOn` with an explicit
modulus and the sum/product/chain/power rules, Rolle, the mean value theorem,
the intermediate value theorem *with an exact root*, the extreme value theorem,
`supOn`, uniform convergence, the Weierstrass M-test, exp/sin/cos as power
series, and `sqrt`. All over `CReal`, the constructed reals, trusted surface 0.

`linear-algebra` is the thinnest of the three and says `covered`.

## The decision

**Do not flip any status.** Both values are correct on their own axis, and
this is the load-bearing point:

- `crates/axeyum-scenarios/src/mathtour.rs` defines `Status::Covered` as
  *"has a self-checking exercise family today"*, and
  `covered_nodes_have_a_family_realized_by_a_self_checking_scenario` enforces
  exactly that against `all_catalog_scenarios()`. Flipping `calculus` to
  `covered` would assert a family that does not exist and would break that
  test in the Rust mirror.
- `Status::LeanHorizon` is defined as *"primarily a proof-reconstruction
  target (P3.6/P3.7), not a benchmark"*. That is a true and useful description
  of `calculus`. The kernel work on it **is** proof reconstruction.

So the file was not wrong about `status`. It had **no field for the other
axis**, and the failure mode is that a reader — human or dispatcher — supplies
the missing axis from the one that is present.

**Add `kernel_decls` per node**, measured rather than asserted, with the
regeneration command in the file's header and the attributed total pinned:

```sh
cargo run --release -p axeyum-lean-kernel \
  --example kernel_declaration_projection > /tmp/proj.tsv
python3 scripts/measure-curriculum-kernel-coverage.py /tmp/proj.tsv \
  --expect-attributed 2433
```

`scripts/measure-curriculum-kernel-coverage.py` is new. Its exit status
depends on what the run found, not on the run completing: `--expect-attributed`
fails when the total moves (verified: 9999 → exit 1), `--require-node` fails
when a named node attributes zero (verified: `linear-algebra` against the
pre-correction pattern → exit 1), and an unknown node id is an error rather
than a silent zero (verified → exit 1).

It reads the **projection**, not a theorem inventory, because
`prelude_theorem_inventory` filters to `Declaration::Theorem` and therefore
returns zero rows for `CReal.integral`, `Rat.matMul`, `Nat.add` and every other
definition. 349 of the calculus figure is 294 theorems and 46 definitions; a
theorem inventory would have missed the definitions entirely.

## What the graph does NOT gate, contrary to the framing that started this

The task that produced this ADR was briefed on the premise that *"a node marked
`lean-horizon` is a node nothing will be dispatched against."* **That is false
for the dispatcher.** `scripts/lib/graph_dispatcher.py` loads `status` into its
node dict at line 121 and never reads it again; `destination_candidates` ranks
by how many published infrastructure-frontier rows name a node's doc path, and
its own docstring says ranking by curriculum status *"would be fabricating
priority the data does not support"*. So the stale statuses were costing
nothing mechanically.

They were costing something in every other direction — the destination pages,
the generated curriculum status audit, and any reader sizing the subject — which
is why the repair is still worth making. But the mechanism matters: this is a
**documentation-integrity** defect, not a dispatch defect, and briefing it as
the latter would have justified a status flip that is wrong.

The one consumer that *does* couple to these fields is
`scripts/validate-foundational-concepts.py`, which requires every
`artifacts/ontology/foundational-concepts.json` row's `curriculum_status` and
`curriculum_family` to match this file exactly. Since neither moved, it passes
unchanged (137 rows).

## Four summaries that were false, not merely incomplete

Repaired in `curriculum.toml`:

- **`calculus`** said *"ε–δ is Lean-horizon"*. The kernel has ε–δ with an
  explicit modulus.
- **`sequences-and-limits`** said *"the ε–N definition is Lean-horizon"*.
  `CReal.Converges`, `CReal.Cauchy` and `CReal.limit` are declared, with
  uniqueness, squeeze, the algebra of limits and Bishop completeness
  (`limitSeq`).
- **`complex`** said *"analysis is Lean-horizon"* without noting the 263
  declarations of `Complex` ring and `CPoint` plane geometry that exist.
  (Complex *analysis* — holomorphy, contour integration — genuinely is absent,
  and the repaired summary says so.)
- **`cardinality`** did not mention `Nat.countRange` and its 18 lemmas.

And in `docs/curriculum/03-destinations/calculus.md`, whose Lean-horizon
paragraph named continuity, differentiability, the MVT, the FTC and series
convergence as out of reach. Its two siblings — `linear-algebra.md` and
`number-theory.md` — each received a measured "Proved in the kernel" section on
2026-08-30 and this page was missed. It now has one: a 24-row table, every
declaration name checked present in the projection, plus a "Still Lean-horizon"
section naming what is genuinely unbuilt (non-constructive limit reasoning,
multivariable and metric calculus, measure theory, transcendence).

## Three stale negatives, two of them mine

This is the part worth carrying forward, because the same failure occurred
three times in one session in the same direction.

1. **`--name-like matrix|determinant|eigen` returned ABSENT and I recorded
   `linear-algebra = 0`.** The query was correct and useless: this kernel spells
   its linear algebra `Rat.det2` / `Rat.det3` / `Rat.dotN`, because a vector is
   a finite function plus a dimension and there is no `List` or product type.
   An empty answer and a wrong query are the same observation.

2. **I then read `linear-algebra.md` and recorded 25.** That page had
   `det2`/`det3`/`dotN` right and stated *"what is genuinely unbuilt is the
   matrix layer over `Nat → Nat → Rat`"*. True on 2026-08-30; false now.
   `Rat.matMul`, `Rat.matId`, `Rat.matTranspose`, `matMul_assoc`,
   `matMul_id_left`/`_right`, `matTranspose_mul` and `matTranspose_transpose`
   are landed, along with `Rat.cramer2_*` and the 2×2 adjugate inverse. The
   real figure is **55**, and that page is corrected.

3. **The number-theory destination read 79** because a prefix-only attribution
   pattern let `Nat.exists_prime_gt`, `Nat.exists_prime_factorization`,
   `Nat.pow_prime_modeq_self` and `Nat.sumDivisors*` fall through into the
   `naturals` carrier bucket. The obvious widening (`.*prime_`) overcorrects to
   152 by stealing 40 `coprime_*` lemmas from `divisibility-and-euclid`. Naming
   the specific stems gives 105 / 151, which is the partition the destination
   docs describe.

The generalisation, and it is one this repository already knows about its
*kernel* work but had not applied to its *maps*: **a document that records what
is missing accumulates stale entries by construction, and its authority is
exactly what makes them expensive.** Three readers, three numbers, one
measurement. The fix is not better prose — it is that `kernel_decls` is now
regenerable in one command with a discriminating exit status, so the next
reader re-measures instead of quoting.

## A subject with no node at all

The measurement found 47 `Rat` declarations of probability and statistics
attributing to `rationals` because nothing better exists: `Rat.IsDistribution`,
`Rat.uniform`, `Rat.bernoulli`, `Rat.indicator`, `Rat.expectation` with
linearity and monotonicity, `Rat.variance` and `Rat.covariance` with
`covariance_sq_le_variance_mul` (Cauchy–Schwarz for random variables),
`Rat.markov_inequality`, `Rat.chebyshev_inequality`, and
**`Rat.weak_law_of_large_numbers`**.

That is an ordered spine — distribution → expectation → variance → Markov →
Chebyshev → weak law — already built, axiom-free, and entirely outside the map.
A graph with no `probability` node cannot record it, cannot dispatch against its
next rung, and does not know it is missing anything. This is the strongest
evidence that the graph's blind spot is **structural** rather than four stale
summaries, and it is why the depth work below is a proposal rather than a patch.

## The depth proposal, and why it is not applied

`docs/curriculum/DEPTH-PROPOSAL-number-theory-and-linear-algebra.md` gives an
eleven-rung spine for `number-theory` and a nine-rung spine for
`linear-algebra`, in the Spivak sense: an ordered list of earned results, each
naming what it needs from below, what the kernel has, and what is missing.

It is **not** applied to `curriculum.toml`. Adding ~30 nodes moves
`scripts/lib/graph_dispatcher.py`, `scripts/gen-import-backlog.py`,
`scripts/validate-foundational-concepts.py`,
`artifacts/ontology/foundational-concepts.json` and the `mathtour.rs` Rust
mirror together, and each of those has its own gate. Landing the measurement
and the design separately from the graph surgery is deliberate.

Two results from that work are worth stating here because they change what to
dispatch:

- **Number theory's three live rungs** are the uniqueness half of prime
  factorization *restated as multiplicity agreement* (multiset equality has no
  carrier, but `Nat.countRange_permute` reaches the expressible form), Euler's
  theorem `a^φ(n) ≡ 1 (mod n)` (both residue-permutation ingredients are
  landed), and quadratic reciprocity (the genuine frontier).
- **Linear algebra's keystone is the determinant at general `n`**, not the
  matrix layer — that landed. The route is a cofactor recursion over the
  dimension bound; a permutation sum needs permutations as data, which this
  kernel has no type for. Span (`L3`) is a cheap `Rat.sumRange` assembly.

## Consequences

- `curriculum.toml` gains one integer field per node and four repaired
  summaries. No `status`, `family`, `prerequisites` or `unlocks` value changes,
  so the graph invariants and the Rust mirror are untouched and
  `mathtour.rs`'s tests are unaffected by construction.
- `kernel_decls` is a snapshot with a stated date and a one-command
  regeneration. It will go stale; the header says so and says how to fix it.
- The attribution table in the script is a **stated judgement**, not a derived
  fact — the projection carries no source module — and the residual (129: the
  30 legacy `AxReal` axioms and the 94-declaration string package) is printed
  on every run so an unattributed namespace cannot hide.
- A separate, pre-existing gate failure was found and deliberately **not**
  fixed here: `python3 scripts/gen-import-backlog.py --check` is red on `main`
  because the fact ledger moved from 147 to 164 qualifying rows and
  `artifacts/import-backlog.json` was not regenerated. Confirmed independent of
  this change (the regenerated diff touches only fact rows). It belongs to
  whoever owns the ledger.
