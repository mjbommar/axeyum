# Prover Track — designing a proof-construction layer on axeyum

**Status: research and design only. Nothing here is committed work.**
No ADR has entered this rung. See [`DIARY.md`](DIARY.md) for how the question
arose and [`critique/`](critique/) for what is wrong with the current draft.

## The question

Axeyum has a **solver** (decision procedures across 24 measured fragments) and a
**kernel** (`crates/axeyum-lean-kernel` — a ~15k-line Rust port of the Lean 4
CIC kernel: universes, dependent `Pi`, inductives with recursors, WHNF,
definitional equality, a trusted admission gate).

It has nothing in between. There is no elaborator, no tactic framework, no goal
state, no specification language. The only producer of proof terms is
certificate reconstruction from the solver.

This track asks: **should there be a proof-construction layer, and if so, what
is it?**

## Why this is not obviously a good idea

Recorded up front so the rest of the track cannot quietly forget it:

1. **Mathlib and the LLM training corpus are network effects.** A new prover
   starts with neither. Targeting Lean as a tactic backend (P3.7) captures the
   automation value without paying for a library.
2. **The repo's own documents forbid or decline this.** See the contradiction
   below — it must be resolved by ADR, not by drift.
3. **SMT-backed proving is brittle.** Verus/Dafny/F* practitioner experience is
   the strongest evidence against an SMT-centric proof assistant, and an axeyum
   prover would be maximally exposed to it.
4. **Proof-term construction is the hard part**, and the plan documents already
   say so: `docs/plan/references/proof-and-lean.md:86-88` notes nanoda "does not
   give proof-term *construction* (the hard part)."
5. **The IR mismatch.** Solver goals live in `axeyum-ir` (first-order, sorted);
   prover goals live in CIC (dependent, higher-order). These are different term
   languages.

## The scope contradiction this track must resolve

| Document | Says |
|---|---|
| `docs/research/01-foundations/proof-assistant-lessons.md:6-19` | Purpose is to learn from proof assistants "**without turning Axeyum into a proof assistant**"; "**Implementing dependent type theory**" is out of scope. |
| `docs/research/00-orientation/mission-and-scope.md:60-65` | "A fully general / dependent-type proof assistant" is out of scope "**for the current phase**" — "*later destinations*, **not permanent exclusions**". |
| `docs/research/00-orientation/north-star.md:125` | "...and **eventually dependent-type proving**." |
| `docs/research/00-orientation/north-star.md:53` | "Out of scope: Commitments or schedules for any horizon rung (**each gets its own ADR**)." |

The first row is **stale**: axeyum *has* implemented dependent type theory —
that is what `axeyum-lean-kernel` is. Three documents gesture at a prover as a
destination; zero specify it; one forbids it on grounds overtaken by events.

`north-star.md:53` supplies the mechanism: entering a horizon rung requires an
ADR. That ADR was never written because the rung was never entered.

## Layout

| Path | Contents |
|---|---|
| [`DIARY.md`](DIARY.md) | Running log — decisions, dead ends, changes of mind. Append-only. |
| [`research/`](research/) | Evidence notes. Top-down (01-05, external landscape) and bottom-up (06-08, axeyum's actual code). |
| [`design/`](design/) | Architecture and identity: what the layer is, its trust boundary, its agentic surface. |
| [`plan/`](plan/) | The phased plan — tracks, phases, tasks, sizing, exit criteria. |
| [`critique/`](critique/) | Adversarial review rounds. Each round attacks the then-current plan; the plan is revised in response. |

## Research notes

| Note | Direction | Question |
|---|---|---|
| `research/01-itp-anatomy.md` | top-down | What is a prover, above the kernel? What did Lean/Rocq/Isabelle/HOL Light get right and wrong? What does it cost? |
| `research/02-ai-assisted-proving.md` | top-down | Where is AI-assisted proving going — and does it make a new prover pointless? |
| `research/03-atp-itp-seam.md` | top-down | How do automation and interaction join? How brittle is SMT-backed proof, really? |
| `research/04-software-ir-verification.md` | top-down | Where is software/IR verification going? Is there an unserved middle? |
| `research/05-education-and-agentic.md` | top-down | What do learners and AI agents actually need from a prover? |
| `research/06-kernel-gap-analysis.md` | bottom-up | What is missing from our kernel, and what does completing it cost? |
| `research/07-reconstruction-assets.md` | bottom-up | Is reconstruction reusable as a construction layer, or is a prover greenfield? |
| `research/08-solver-automation-assets.md` | bottom-up | What automation transfers — and how bad is the IR mismatch? |

## Reading order

Start with `DIARY.md` for the framing, then `critique/` for the strongest
objections, then `plan/`. The research notes are evidence, not argument.
