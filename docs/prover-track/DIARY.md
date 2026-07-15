# Prover Track — Diary

Append-only log. Newest entries at the bottom. Records what was decided, what
was wrong, and what changed — including dead ends, which are the most useful
part of a diary and the first thing a tidy-up would delete. Do not delete them.

---

## 2026-07-15 — How this question arose

Not from the roadmap. From reading someone else's code.

The session began with Microsoft's SymCrypt `feature/verifiedcrypto` branch
([README-VERIFIEDCRYPTO.md](https://github.com/microsoft/SymCrypt/blob/feature/verifiedcrypto/README-VERIFIEDCRYPTO.md)),
and the question "how well prepared is axeyum to address a project like this,
especially given our Rust/LLVM IR capabilities?"

**That framing turned out to be wrong twice over, and both errors were mine.**

**Error 1 — wrong altitude.** SymCrypt's pipeline is Rust → Charon → Aeneas →
Lean 4 → tactic proofs → Lean kernel. Charon lowers **MIR → ULLBC → LLBC**,
deliberately *not* LLVM IR: MIR retains the lifetime and borrow information that
LLVM lowering destroys, and Aeneas needs exactly that to build its functional
model ([Charon paper](https://arxiv.org/html/2410.18042)). So `axeyum-verify`'s
`reflect/llvm.rs` is at an altitude this class of project intentionally avoids,
and `reflect/mir.rs` is at the right altitude but the wrong shape — bounded
symbolic execution over *acyclic* CFGs, where refinement needs total functions
with loops and recursion.

**Error 2 — I underrated our own assets, badly.** I asserted this was "an
Aeneas/refinement-proof problem, not a solver problem," implying we had nothing.
Wrong. `axeyum-lean-kernel` is not a serializer — it is a real CIC kernel ported
from `nanoda_lib`, with `add_inductive` generating recursors *including induction
hypotheses* (`inductive.rs:45-53`). We also have genuine unbounded inductive
invariants via PDR/IMC (`pdr.rs`, gated by `verify_invariant`), which I had
written off as bounded-only. The correction came from the user pushing back:
*"don't we have a solver and a prover framework in axeyum?"*

**The precise answer to that pushback — and the reason this track exists:** we
have a solver and a **kernel**. Not a prover. A kernel *checks* proof terms
someone else built. The layer that *builds* them — elaborator, tactics, goal
state, spec language — does not exist. `grep tactic` across all crates returns
zero hits.

### The finding that made this a track rather than a note

The SymCrypt README names `bv_decide` as a trusted component. `bv_decide` is
BitVec goal → AIG → CNF → CaDiCaL → LRAT → verified Lean checker — which is
axeyum's Phase 4/5 pipeline, feature for feature. And **P3.7 is our plan to build
exactly that thing**: `docs/plan/track-3-proof-lean/P3.7-lean-reconstruction.md:8-11`
— "making axeyum a proof-producing solver usable as a **Lean tactic backend**."

So our plan of record is to be the *callee*. Lean owns the goal, the elaborator,
the proof state; axeyum returns a term. That is a coherent and defensible
position, and this track must beat it on the merits or not proceed.

### The contradiction

Searching the plans and the research corpus for a prover layer (two independent
sub-agent sweeps, one over `PLAN.md`/`docs/plan/**`/`docs/consumer-track/**`, one
over `docs/research/**` + all 163 ADRs) returned:

- Track 3 is **P3.0–P3.8 and it ends**. The capstone is P3.7. There is no P3.9.
- **Zero** hits for an axeyum-owned elaborator, goal state, or proof script.
- Two traps that look like a prover plan and are not: **P1.8 "strategy-tactics"**
  is Z3-style engine-selection combinators (`and_then`/`or_else`/probes), and
  **P5.2 contracts** is explicitly anti-deductive — "Contracts keep every
  obligation **finite and decidable** — which is what separates this from
  ghost-code deductive systems" (`P5.2-contracts-modular.md:16-18`), with Verus
  named and its "deductive lane explicitly **not** copied."
- `proof-assistant-lessons.md:19` lists "**Implementing dependent type theory**"
  as out of scope — **which we have already done.** The doc is stale.
- `mission-and-scope.md:60-65` and `north-star.md:125` both name a dependent-type
  proof assistant as a *later destination*, "not permanent exclusions."

Three documents gesture at it; zero specify it; one forbids it on stale grounds.
`north-star.md:53` says each horizon rung "gets its own ADR." That ADR was never
written because the rung was never entered.

**This track is the attempt to write it — or to conclude, on evidence, that it
should not be written.** Both outcomes are acceptable. A well-argued "no, P3.7 is
sufficient and here is why" is a successful result, and the plan must be
structured so that conclusion remains reachable to the end.

### Method

Eight parallel sub-agents, deliberately split by direction to avoid a single
narrative capturing the evidence:

- **Top-down (01-05)**: ITP anatomy; AI-assisted proving; the ATP/ITP seam;
  software+IR verification; education and agentic use.
- **Bottom-up (06-08)**: kernel gaps with sizing; reconstruction reusability;
  solver automation + the IR mismatch.

Each writes its own note and returns a ≤400-word summary, so the synthesis reads
evidence rather than 8× agent prose.

**Three prompts were written to attack the thesis rather than support it**, since
a design track staffed entirely by advocates produces a brochure:
- 02 must engage the counter-thesis that Mathlib + LLM-training-data network
  effects make any new prover pointless.
- 03 must quantify SMT brittleness (Verus/Dafny/F* instability) — the strongest
  known argument against an SMT-centric proof assistant, and the one an axeyum
  prover is *most* exposed to.
- 08 must treat the `axeyum-ir` (first-order, sorted) vs CIC (dependent,
  higher-order) mismatch as the single biggest technical risk.

### Priors going in (recorded now so they can be scored later)

Written before the evidence lands, so hindsight cannot quietly revise them:

1. The IR mismatch (CIC ↔ SMT-IR) will prove to be the dominant technical risk,
   and reconstruction will turn out to be **mostly not reusable** — a prover will
   be closer to greenfield than to an extension.
2. The Mathlib/LLM network-effect argument is **strong and probably decisive**
   for the "general mathematics prover" framing. If the track survives, it will
   be by finding a niche where Mathlib is not the moat.
3. The most defensible niche is where our actual assets are unique: **pure Rust,
   WASM-deployable, counterexample-first, agent-driven, over software/IR rather
   than mathematics** — not "a better Lean."
4. Kernel completion (`Proj`, `Lit` reduction, `Quotient`, mutual/nested/
   recursive-indexed inductives) will be smaller than the prover layer but is a
   hard prerequisite, and its absence from the plans is an oversight rather than
   a decision.
5. Honest guess at the headline: **the plan will recommend a narrow prover, not a
   general one** — and the narrow version may be close enough to P3.7 + P5.2 that
   the marginal case for a "prover" is weak.

If the evidence contradicts these, the diary records that it did.

---
