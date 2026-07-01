# P2.5 · Phase E — Nonlinear integer arithmetic (NIA)

**Size:** L · **Depends on:** Phases A–D (reuses ~100% of the real machinery) ·
**Repositions** the existing width-ladder bit-blast as a SAT-finishing fallback.

> **The central fact (drives the whole design):** QF_NIA is **undecidable**
> (Hilbert's 10th / MRDP; the ∃ quantifier-free fragment over ⟨ℤ;0,1,<,+,×⟩ is
> exactly QF_NIA). There is **no complete decision procedure**. So NIA is a
> **portfolio of sound, incomplete deciders** that share machinery with NRA and
> return honest `unknown`. The honest target is high decide-rate, never
> completeness. (Borralleras et al., *ACM TOCL* 2019: "no tool always outperforms
> all the others" — the signature of an undecidable theory.)

## First slice — grounded in the measured NIA declines (2026-07-01)

The QF_NIA declines (20/28) were root-caused (see
[the scoreboard](../../measured-scoreboard-2026-07-01.md)). The cluster —
integer div/mod by *variable* divisor (`div.03/08`, `mod.02/03`), `iand`, and
nonlinear-int — bottoms out at **one** missing capability, demonstrated by a clean
experiment:

> `div.03` = `n>0 ∧ x≥n ∧ (div x n)<1`. Its **manually Euclidean-eliminated** form
> `n>0 ∧ x≥n ∧ q<1 ∧ x=q·n+r ∧ 0≤r<n` is **still undecided** by axeyum. It is
> **unsat over ℤ but sat over ℝ** (`q=0.5` works), so `int_real_relax` cannot
> transfer the unsat. The unsat needs **integer tightening** (`q<1 ⟹ q≤0`, valid
> only over ℤ) followed by a **sign lemma** (`q≤0 ∧ n>0 ⟹ q·n≤0`, so
> `x = q·n + r ≤ r < n` contradicts `x≥n`).

So `eliminate_int_divmod` (extending it to variable divisors) is **not** the lever
— the resulting NIA still declines. The lever is an **integer analog of
`check_with_nra`**: abstract each product `a·b` to a fresh var, add the same
sign/zero/monotonicity lemmas the real path already has (`nra.rs`), but solve the
relaxation over the **integer** solver (`lia`/`dpll_lia`) so integrality is kept
(`q<1 ⟹ q≤0`) and combines with the sign lemma to refute. Concretely:

- **E.0a** `check_with_nia` (mirror `check_with_nra`): product abstraction + the
  existing sign/zero/monotonicity lemma builders, relaxation solved by the integer
  DPLL(T) (`check_with_lia_dpll`), replay against the **original** (per the
  div-by-zero lesson: replay against the true original, never the eliminated form).
- **E.0b** route the integer nonlinear tail (`dispatch_nonlinear_int_tail`) into it
  before the width-ladder blast; strictly additive (`unknown → decision`).
- **E.0c** then (and only then) extend `eliminate_int_divmod` to variable divisors
  (Euclidean `x=q·n+r ∧ 0≤r<|n|` with sign/zero handling + division congruence, as
  in the RealDiv fix), so `div.03`-style instances reach `check_with_nia`.
- Gate: `nia_differential_fuzz` (18 min) DISAGREE=0; re-measure QF_NIA.

This is the tractable, measured-grounded entry to Phase E — reusing the real
path's lemma machinery, differing only in the linear solver (LIA vs LRA) and the
integrality it preserves.

## The SAT/UNSAT split (the key empirical fact)

The literature is consistent: **bounded/model-construction finds SAT models;
incremental linearization and CAD/coverings prove UNSAT.** axeyum today has the
SAT-finding half (width ladder) and almost none of the UNSAT half. Phase E adds
the UNSAT engine and runs both complementarily — exactly what the SMT-COMP winners
do (cvc5, Z3++, Yices-ismt).

## Layered NIA engine (composes with NRA)

```
Layer 0  Shared substrate (with NRA): fmul purification, LIA branch-and-bound,
         LRA/NRA relaxation oracle, the CEGAR lemma driver
              │
Layer 1  Real relaxation + branch-and-bound  ── solve LRA/NRA relaxation;
         integral model? done; else branch/cut toward integers   (cheap, high-yield)
              │  unknown
Layer 2  Incremental linearization (the UNSAT engine, Phase B specialized to UFLIA)
         ── abstraction over-approximates ⇒ UNSAT abstraction = real UNSAT;
            integrality comes FREE from Layer-0 LIA branch-and-bound
              │  unknown
Layer 3  iand / int-blasting bridge ── iand a first-class NIA op (lazy UF + partial
         lemmas; eager sum/bitwise fallback); wide QF_BV can route IN here
              │  unknown
Layer 4  Bounded bit-blast / width ladder (EXISTING, repositioned) ── SAT-finishing
         fallback ONLY; never claims UNSAT for unbounded integers
              │
Layer 5  (later) complete-real fallback = Phase D CAC, reached via branch-and-bound
```

## What changes vs. today

- **`nia_square.rs`** (single-variable, exact) is retained as a fast pre-path and a
  differential oracle, folded into `nra/nia.rs`.
- **Width ladder** (`auto.rs` tail) is repositioned: it is **Layer 4**, a SAT
  finisher, explicitly documented as *unable to certify UNSAT for unbounded
  integers* (it only proves "no model up to the current bound"). The
  `int_real_relax` UNSAT short-circuit becomes Layer 1.
- **New:** incremental linearization over **UFLIA** (Layer 2) is the UNSAT engine
  axeyum lacks. It shares 100% of its lemma machinery with NRA Phase B — only the
  underlying linear theory differs (LIA vs LRA), and integrality is inherited from
  LIA branch-and-bound. This is the FroCoS-2017 "base + extension" pattern.

## Tasks

| id | task | key references | size | exit |
|---|---|---|---|---|
| T-E.1 | Fold `nia_square` + width ladder + int-real-relax into `nra/nia.rs` as Layers 1 & 4; preserve verdicts | this repo `nia_square.rs`, `auto.rs` | M | regression-clean; ladder documented as SAT-only |
| T-E.2 | **Incremental linearization over UFLIA** (Layer 2) — reuse Phase B lemma builders with LIA branch-and-bound | Cimatti et al. SAT 2018; FroCoS 2017 | L | NIA **UNSAT** instances decided that the ladder can't (measured) |
| T-E.3 | Branch-and-bound + cut bridge real→int (Layer 1) | Kremer & Ábrahám CASC 2016 | M | integer models recovered from real relaxation |
| T-E.4 | **`iand` first-class** (Layer 3): lazy UF + partial lemmas (bounds, idempotence, symmetry, all-0/all-1); eager sum/bitwise fallback. OR/XOR derived. | Zohar et al. VMCAI 2022 | M | `iand` constraints decided; int-blasting bridge usable |
| T-E.5 | Portfolio dispatch: run Layers 1–2 (UNSAT-oriented) and Layer 4 (SAT-oriented); first **sound** verdict wins | §6 of the NIA survey | M | measured decide-rate up on QF_NIA; DISAGREE=0 |
| T-E.6 | (later) route NIA branch-and-bound into Phase D CAC (Layer 5) | — | — | complete-real fallback wired once D exists |

## Soundness

- **SAT** ⇒ integer witness replays through the ground evaluator (hard rule).
- **UNSAT** ⇒ from Layer 1 (relaxation refutation) or Layer 2 (over-approximating
  abstraction UNSAT) — both sound; retain the certificate. **Layer 4 never emits
  UNSAT for unbounded integers.**
- **`unknown`** ⇒ branch depth / width ceiling / no refinement. Structural, not a
  failure.
- **Division caveat** (Jovanović 2026): be deliberate axiomatizing `div`/`mod` at
  the Int↔NRA boundary — non-constant div-by-zero can re-encode Hilbert's 10th.
  Keep the existing total-semantics encoding and stay `unknown` past the
  polynomial fragment.

## Exit criteria

- NIA decides UNSAT instances the width ladder structurally cannot (Layer 2),
  measured on public QF_NIA; SAT-finding unchanged or better.
- `iand` is first-class; the int-blasting bridge can route wide QF_BV into NIA.
- Portfolio dispatch is sound (first sound verdict wins); `nia_differential_fuzz`
  vs Z3 DISAGREE=0.
