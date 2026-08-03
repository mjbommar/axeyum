# Phase 1 — the direction algebra and verdict licensing

Verdict from review: **needs revision.** The core claim is correct and the
mechanism is genuinely missing (no `Direction` type exists anywhere in
`crates/`), but the three-way classification is too small and attaches at the
wrong granularity. This is the **soundness-critical phase** of the track.

## The claim under review

> Every bridge is `equivalence` | `over-approximation` (preserves UNSAT only) |
> `under-approximation` (preserves SAT only). Composition must be monotone, and
> the system must refuse to emit a verdict the composed direction does not
> license — structurally, not by test.

## What the review corrected

**Direction is per-instantiation, not per-reduction.** `IntBlast` is the
disproof: the width ladder is an under-approximation (sound for `Sat` only,
`auto.rs:3470-3476`, `axeyum-rewrite/src/int_blast.rs:13-21`) while the
proven-box sub-case is an equivalence (`trust.rs:67-76`). One `TrustId`, two
opposite directions, selected by a per-query precondition. `Fpa2Bv` is the same
per operator set (`trust.rs:252-276`). **A static direction column on `TrustId`
would itself be a soundness bug.**

**Direction is primarily an UNSAT-soundness mechanism.** The Hard Rule already
forces every `sat` to replay against the original term, and `Evidence::Sat` is
*defined* as "a model whose canonical replay against the query is the evidence"
(`evidence.rs:256-259`). So SAT goes wrong only if a chain replays against an
*intermediate* formula. UNSAT has no analogous universal backstop:
`Evidence::Unsat(None)` is a legal terminal (`evidence.rs:260-262`), so a
mis-licensed unsat ships silently. Say this explicitly in the design.

## The actual algebra — five components

1. **Direction lattice** = subsets of `{SAT, UNSAT}` licensing transfer of a leaf
   verdict to the source. `Equivalence = {SAT,UNSAT}`, `OverApprox = {UNSAT}`,
   `UnderApprox = {SAT}`, `Heuristic = {}` (legal as search guidance).
   Composition = **intersection**: commutative, associative, idempotent monoid,
   identity `Equivalence`, absorbing `Heuristic`, monotone.
2. **Guarded direction**: applying an edge to a concrete query *returns* a
   direction produced by its own precondition check, bound to a fingerprint of
   the exact input formula.
3. **Model-lift axis, separate from direction**: direction licenses *attempting*
   a sat; replay *validates* it. The dual for unsat is licensed (direction) vs
   certified (per-run `TrustStep::certified` + certificate recheck) — already
   modelled; keep orthogonal.
4. **CEGAR is a combinator, not an edge**: `cegar(over_approx, refiner)`
   *derives* `Equivalence` (`lazy_bv.rs:22-28` — "sound, complete, terminating"),
   degrading to `OverApprox` when the round budget ends first.
5. **Unknown propagation** needs no direction, but a *refused* verdict must map
   to `UnknownKind::Incomplete` with structured detail, never be dropped and
   never be retried by a fallback inheriting the refused leaf's work.

**Generalization flag:** if the search's action space ever includes dual/negation
edges (validity via unsat of ¬φ, interpolation, abduction side-queries),
verdict-preserving intersection is wrong — the algebra becomes a monoid of
partial verdict *maps* under function composition. MVP: make such edges
**unrepresentable** as `Bridge` and record the restriction in the ADR.

## Rust enforcement (structural, not a test)

```rust
/// Fields private: the only values are the four consts and anything `compose`
/// produces — a chain cannot mint a stronger direction than its weakest edge.
pub struct Direction { sat: bool, unsat: bool }
impl Direction {
    pub const EQUIVALENCE: Self  = Self { sat: true,  unsat: true  };
    pub const OVER_APPROX: Self  = Self { sat: false, unsat: true  };
    pub const UNDER_APPROX: Self = Self { sat: true,  unsat: false };
    pub const HEURISTIC: Self    = Self { sat: false, unsat: false };
    #[must_use]
    pub const fn compose(self, next: Self) -> Self {
        Self { sat: self.sat && next.sat, unsat: self.unsat && next.unsat }
    }
}

pub struct AppliedBridge { target: QueryState, direction: Direction,
                           trust: Vec<TrustStep>, lift: ModelLift }
pub struct Chain { source: SourceQuery, composed: Direction,
                   lifts: Vec<ModelLift>, owed: Vec<TrustStep> }
pub struct LicensedVerdict(CheckResult);   // private field
```

Load-bearing properties: `Direction` unforgeable outside its module;
`Chain.composed` private and `extend` monotone by construction;
`LicensedVerdict` has a private field so the search **cannot** return a
`CheckResult` it assembled itself; **replay lives inside `conclude` and is bound
to `self.source`**, closing the replay-against-an-intermediate trap by
construction; `Bridge` is sealed so out-of-tree edges cannot skip the witness
discipline.

Monoid laws get property tests. The *licensing* is not test-enforced — it is the
only code path.

## Verdict-licensing rule (normative)

Emit `Sat` iff `composed.sat` ∧ lift succeeds ∧ `check_model` against the **chain
source** passes. Emit `Unsat` iff `composed.unsat`, with
`EvidenceReport.trusted_steps` = the whole-chain union (dedup via the existing
helper, `evidence.rs:222`). Anything else is `Unknown` with a
`direction-unlicensed` detail, recorded via a new `DeclineReason` variant
analogous to `VerifierRejected` (`route_trace.rs:66-68`).

## Direction classification of the 14 TrustIds

Produced by the review; the ambiguity column is the actionable part.

| TrustId | Direction | Flag |
|---|---|---|
| BitBlast, Tseitin | Equivalence | faithfulness, not direction, is the trust question |
| SatRefutation, Farkas, Sos, Diophantine | **not edges** — terminal one-sided certificates | category error to model as bridges |
| ArrayElim, Ackermann | equisat in the math; certificate witnesses **only** the over-approx direction ("sound relaxation") | **witnessed direction ≠ true direction; ledger records neither** |
| IntBlast | **two opposite directions under one id** | width ladder = under-approx; proven-box = equivalence |
| DatatypeElim | Equivalence + sat replay | the only fully uncertified TrustId for unsat |
| Fpa2Bv | per-operator: exact = equivalence; unspecified-result = over-approx | direction metadata already exists as an ad-hoc op allow-list |
| TermLevelEnum, LraDpll | Equivalence | — |
| XorGaussian | Unsat-only | **direction never stated in the prose** |

**Direction-bearing routes absent from the ledger** (the real edge inventory must
include these): `lazy_bv.rs` over-approx CEGAR; `int_real_relax.rs`
(unsat-only, argued at lines 19-22); coercion relaxation (`auto.rs:1676-1752`,
sat replay-gated at 1747); MILP LP-relaxation (`auto.rs:1765-1811`); `bv2nat`
range relaxation (`auto.rs:1985-2008`); NRA product abstraction; the
`check_qf_abv_lazy_row` CEGAR (`auto.rs:3440`); the int width ladder.

## Soundness-negative fuzz design

The composed-bridge analogue of CLAUDE.md's degenerate-argument rule. Every
direction-bearing edge gets a seed family that **constructs the divergence** — a
source query whose leaf verdict through that edge differs from ground truth —
and the harness asserts the system emits `Unknown`, never the unlicensed verdict.

- **ladder-poison**: int queries SAT only above every ladder width (`x = 2^80`
  shapes); every bounded blast refutes; the chain must refuse `Unsat`.
- **abstraction-poison**: heavy-op queries UNSAT whose fresh-var abstraction is
  SAT (`x*x = -1` class); must refuse `Sat` without replay.
- **relaxation-poison**: int-UNSAT/real-SAT (`2x = 1`); the real relaxation must
  never transfer `Sat`.
- **guard-epsilon**: box bound off by exactly one (`2^w`), FP width 129, op-list
  plus one rounding op, coercion near-miss — the edge must instantiate as the
  weaker direction or decline, never as equivalence.
- **random-chain differential**: random compositions over small queries
  cross-checked against `check_auto` and the Z3 oracle, with the refusal
  assertion checked on **every** emission.

Gate: every single-edge direction flip (OVER↔UNDER↔EQ) must be caught by at least
one seed, or the gate is blind exactly where the `a946f925` lesson says fuzzes go
blind.

## Prior art

- **UppSAT** — decomposes an approximation into encoding + precision ordering +
  model reconstruction + refinement, and supports approximations that are
  **neither** under- nor over-approximations. Direct evidence the three-way
  classification is too small. <https://arxiv.org/abs/1711.08859>
- **Bryant/Kroening/Ouaknine/Seshia/Strichman/Brady**, *Deciding Bit-Vector
  Arithmetic with Abstraction* (TACAS 2007) — one procedure, two directions,
  refinement between them.
  <https://people.eecs.berkeley.edu/~sseshia/pubdir/uclid-tacas07.pdf>
- **Why3 proof-carrying logical transformations** — skeptical
  certificate-producing transformations, the direct analogue of the
  ArrayElim/Ackermann re-checkers. <https://arxiv.org/pdf/2107.02352>
- **Galois connection composition** (Cousot & Cousot, POPL 2014) — the theorem the
  compose monoid instantiates.
- **cvc5 flexible proof production** — most proof holes come from preprocessing
  passes. <http://theory.stanford.edu/~barrett/pubs/BRK+22.pdf>

## Tasks

| id | title | size |
|---|---|---|
| [T1.1](T1.1-direction-monoid.md) | `Direction` monoid + law property tests | S |
| [T1.2](T1.2-edge-inventory-ledger.md) | Edge inventory + golden direction ledger | M |
| [T1.3](T1.3-bridge-chain-types.md) | `Bridge`/`AppliedBridge`/`Chain`/`LicensedVerdict` + 3 pilot edges | M |
| [T1.4](T1.4-model-lift-cegar.md) | Model-lift axis + CEGAR combinator | M |
| [T1.5](T1.5-soundness-negative-fuzz.md) | Soundness-negative chain fuzz + direction-flip mutation gate | L |
| [T1.6](T1.6-licensed-verdict-surface.md) | Search surface restricted to `LicensedVerdict`; evidence provenance | L |
| [T1.7](T1.7-adrs.md) | ADRs: direction algebra scope; ledger placement | S |
