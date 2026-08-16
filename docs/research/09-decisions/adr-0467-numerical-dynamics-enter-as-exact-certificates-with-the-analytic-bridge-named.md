# ADR-0467: Numerical Dynamics Enter As Exact Certificates, And The Analytic Bridge Is An Axiom Rather Than A Step

Status: accepted
Index-summary: Stability, safety and nonnegativity questions about polynomial ODEs are settled by exact rational SOS certificates in `axeyum-cas`; the passage from a pointwise polynomial inequality to a statement about solutions is recorded in `axiom_footprint`, never taken silently
Date: 2026-08-15
Supersedes: none

> Renumbered from ADR-0466 on 2026-08-15: two lanes (`numerics` and `import-projrec`) picked the next free number concurrently and both wrote an
> ADR-0466. `import-projrec`'s already had a code reference (`k_like_reduction.rs`), so that one
> kept the number and this one moved. Both files were still untracked when the collision was found.

## Context

The project's owner asked for the stack to be pointed at useful computations —
"planning, logistics, database design, or general numerical approximation / ode
/ pde systems". Planning and logistics had schedule infeasibility, IIS cores and
Farkas certificates reconstructed into Lean. Database design had just been built
([ADR-0463](adr-0463-relational-database-design-enters-the-stack-as-certificates-not-verdicts.md)).
Numerical / ODE was the remaining named domain with nothing in it.

The obvious way to do numerics in a solver stack is the wrong way. Simulating a
trajectory produces a picture, not a theorem; a floating-point sweep over a grid
produces a *sample*, and a sample cannot distinguish "this system is stable" from
"this system is stable at the 10⁴ points I happened to visit". Neither is
something this repository can put in a fact ledger, because neither has a
checker that fails when the claim is false.

But there is a shape of numerical question that fits this project's identity
sentence — *untrusted fast search, trusted small checking* — better than almost
anything already here. For a polynomial vector field, the interesting global
properties reduce to **polynomial inequalities on ℝⁿ**, and a polynomial
inequality has a small certificate: a sum-of-squares decomposition. Finding one
is a semidefinite program; checking one is expanding a few squares and comparing
coefficients. The gap between those two costs is the whole business.

| question | certificate | what checks it |
|---|---|---|
| is the origin globally exponentially stable? | `V` with `V − ε‖x‖²`, `C‖x‖² − V`, `−∇V·f − δ‖x‖²` all SOS | expand the squares over ℚ; the rate is `δ/C` |
| can the flow ever reach an unsafe set? | barrier `B` with Positivstellensatz multipliers on each set and `−∇B·f` SOS | expand three identities; evaluate two witnesses |
| is this polynomial nonnegative? | SOS decomposition of `‖x‖²·p` | expand one identity |
| is it a sum of squares? (**no**) | a PSD moment functional negative on `p` | exact rational LDL^T, plus one dot product |

Three things had to be decided before any of this could become public surface.

## Decision

**Numerical-dynamics questions enter the ledger as exact rational certificates
over ℚ, checked by code that re-derives every derived quantity itself; and the
step from a pointwise polynomial inequality to a claim about solutions is
recorded as a named assumption in `axiom_footprint`, never taken silently.**

### 1. Exact rationals, and therefore a claim about every ordered field

Every coefficient in a certificate — the weights, the squares, the multipliers,
the dual values — is an `axeyum_ir::Rational`. The format's parser refuses a
decimal literal outright. This is not fastidiousness: it changes what is proved.

`p = Σ wᵢ qᵢ²` with `wᵢ ∈ ℚ≥0` and `qᵢ ∈ ℚ[x]` is an identity in `ℚ[x]`, so it
holds in **every ordered field**, and `p ≥ 0` there. A floating-point check at a
million points establishes nothing about any point it did not visit, and a
rounded "certificate" whose residual is `10⁻¹⁴` is not a certificate at all. So
the rational route is not merely cleaner than the numerical one; it proves a
strictly stronger statement, and the extra strength is free once the search is
allowed to be untrusted.

This mirrors the field question the `simson` lane settled for geometry
([ADR-0453](adr-0453-route-dependent-provability.md), and
`F:geometry-simson-line`): a cofactor identity with rational coefficients is a
characteristic-zero theorem, and the real-plane reading is a specialisation of
it. The difference here is the *ordering*: a sum of squares needs an ordered
field, not merely characteristic zero, because `Σ wᵢ qᵢ² ≥ 0` is an order
statement. So the SOS facts are theorems of every ordered field — an even more
specific class than the geometry facts, and stated as such.

### 2. The analytic bridge is named, not taken

Lyapunov's direct method says: if `V` is positive definite, radially unbounded
and `V̇ < 0` off the equilibrium, then the equilibrium is asymptotically stable.
The hypotheses are polynomial inequalities. **The conclusion is not.** Getting
from `∇V(x)·f(x) ≤ −δ‖x‖²` for all `x` to `‖x(t)‖² ≤ K‖x(0)‖²e^{−rt}` requires
that solutions exist, that `t ↦ V(x(t))` is differentiable with the chain rule,
and a Grönwall comparison — real analysis over a complete ordered field, none of
which any certificate in this module touches.

The decision is to keep those apart in the artifact and in the fact:

* `formal.statement` of an SOS fact asserts the **polynomial inequalities**, and
  nothing else. That is exactly what is proved.
* the analytic theorem that converts them appears in `axiom_footprint` under a
  name (`dynamics.lyapunov-direct-method`,
  `dynamics.barrier-certificate-soundness`, `analysis.gronwall-comparison`).
* the checker *prints* the distinction in the obligation it discharges, so a
  reader of a passing run sees it rather than inferring it.

The alternative — stating "the origin is globally exponentially stable" as the
proved fact — would be the exact overstatement this ledger has a field to
prevent. It is also the overstatement the surrounding literature makes casually,
because in that literature the analytic theorem is not in question. Here it is
not in evidence, which is a different thing.

### 3. The route's own incompleteness is a fact, not a caveat

`p ≥ 0` does not imply `p` is a sum of squares — Hilbert 1888, non-constructively;
Motzkin 1967, explicitly. So the SOS route is *incomplete* for polynomial
nonnegativity, and every stability or safety question it declines might be
declined for that reason rather than because the answer is no.

The decision is to record that as a settled fact with its own certificate rather
than as prose in a README. `F:motzkin-nonnegative-not-sum-of-squares` carries
both halves:

* **primal**: `(x²+y²+z²)·M` is a sum of five weighted squares, so `M ≥ 0`. The
  multiplier is required by the checker to be exactly `Σ xᵢ²`, because only a
  multiplier strictly positive off the origin licenses the inference.
* **dual**: a linear functional `L` on the degree-six monomials whose moment
  matrix over the ten degree-three monomials is PSD, with `L(M) = −1`. If `M`
  were `Σ qᵢ²` then `L(M) = Σ L(qᵢ²) ≥ 0`.

The dual half is a **new kind of evidence for this repository**: it refutes
*representability in a proof system*, not the truth of a proposition. `M ≥ 0` is
true and is proved on the same artifact; what is refuted is that this route can
show it directly. Nothing else in the ledger does that, and it is why the fact is
worth more than the two positive ones next to it.

### 4. `axeyum-cas`, not a new crate, and not `axeyum-solver`

[ADR-0001](adr-0001-minimal-crate-split.md) admits a crate only once a boundary
is proven by use. This module needs exactly one thing that already exists: an
exact multivariate polynomial ring with checked rational coefficients
(`axeyum_cas::mvpoly`). Duplicating it into `axeyum-scenarios` to keep that
crate's dependency list short would be the worse trade, and `axeyum-solver`'s
SOS code is degree-2 only, `pub(crate)`, and owned by another lane's refactor.

So `axeyum_cas::sos` sits beside `geometry_certify` / `geometry_check` /
`geometry_json` and copies their shape deliberately: a corpus in Rust, an emitted
JSON artifact, a checker that shares no code with the producer, and a committed
suite of tamperings.

One primitive is genuinely new. `matrix::cholesky_decomposition` introduces
surds and rejects any zero pivot, so it cannot decide semidefiniteness; a moment
matrix is exactly where a zero pivot lands (this one has corank 3). `sos::psd`
is an exact rational `LDL^T` with the semidefinite rule stated explicitly: a zero
pivot with a nonzero entry to its right is a `[[0,a],[a,b]]` minor of determinant
`−a² < 0`, hence not PSD. Overflow is a **decline**, never a verdict.

## Consequences

**A numerical practitioner gets something they could not get before.** Not a
simulation and not a bound with a tolerance: an exactly rational decay rate
(`1/26` for the committed system, with overshoot `104`), and an unbounded-horizon
safety claim with no time discretisation anywhere in it. Both re-derive in
about a tenth of a second from a 20-line file.

**The checker must never trust a derived quantity.** `V̇` and `Ḃ` are formed by
the checker from the declared vector field; `‖x‖²` is built from the declared
variables; the moment matrix is assembled from the functional and a
checker-built monomial basis. The consequence is testable and is tested: editing
the *dynamics* in an artifact breaks the certificate even though no field in the
file names a derivative.

**Every quantified-over set must be shown nonempty.** An empty initial set
satisfies every barrier certificate ever written. The artifact carries a point in
each set and the checker evaluates the generators there. This is the same defect
class as the 2026-08-15 audit's "40 of 162 checker runs exit 0 on completion
alone", one level up: not a checker that ran nothing, but a *theorem* that
quantified over nothing.

**The negative controls are the gate.** 21 committed false certificates, each a
single surgical edit from an honest artifact, produced by a generator that
refuses to write a fixture whose edit did not apply. The sharpest is
`motzkin-dual-nonneg-on-form`: raising one dual value keeps the moment matrix PSD
and flips the functional's sign, so a checker running only the matrix test
accepts it. The suite was itself probed — dropping a *copy* of an honest artifact
into the fixture directory makes the gate report `ACCEPTED` and exit 1.

**What this does not do.** There is no SOS *search* here: the certificates were
found by hand. That is a deliberate first slice and the honest description of the
lane — the identity sentence permits an untrusted search of any kind, including a
person, but a repository that wants to answer *new* stability questions needs an
SDP and a rounding step that lands in ℚ. Nothing in this ADR is a commitment
about how that search is built, only about what its output must look like when it
arrives. Likewise PDEs are untouched: the module handles ODEs with polynomial
right-hand sides, and a PDE would need a different certificate shape entirely.
