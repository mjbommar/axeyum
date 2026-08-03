# Consolidated risk register

Ranked by expected damage. Every entry names its phase and its structural
mitigation. Per CLAUDE.md, "this is soundness-critical" means *test it harder*, not
*punt it*.

## Tier 1 — can ship a wrong answer

| # | Risk | Phase | Structural mitigation |
|---|---|---|---|
| R1 | **Mis-declared edge direction.** The algebra faithfully composes a lie. | 1 | Per-instantiation witnesses over static labels wherever a guard exists; the direction-flip mutation gate must fail under *every* single-edge flip, or it is blind exactly where the `a946f925` lesson says fuzzes go blind. |
| R2 | **Replay against the wrong formula.** A chain replaying a lifted model against an *intermediate* query converts an under-approximation violation into a "pass." | 1 | `Chain::conclude` holds the source handle and is the only sat-emitting path. Audit for bypasses is an exit criterion, not a nice-to-have. |
| R3 | **Exhaustiveness bug in cube splitting.** A dropped branch yields per-cube proofs that all check while the composed claim is false. | 6 | The cube-tree tautology certificate must be *checked*, never trusted from the splitter, with a deliberate negative generator (drop / duplicate / mutate a cube). |
| R4 | **UNSAT has no universal backstop.** `Evidence::Unsat(None)` is a legal terminal; a licensing bug ships silently. SAT is protected by mandatory replay; UNSAT is not. | 1 | Policy: chains through any uncertified edge either produce a rechecked certificate or emit `Unsat` with `certified: false` prominently — never silently. |
| R5 | **Wrong shadow.** A mis-derived bounded shadow produces a confidently-labelled artifact about the wrong statement. | 8 | The `direction` field; the Lean `by decide` tie-back; negative fixtures; degenerate-parameter fuzz per shadow family. |
| R6 | **Trust laundering from external engines.** A kissat timeout must be `unknown`, never `unsat`. | 6 | Type-level: `ProofSource` required to construct an UNSAT verdict. |
| R7 | **`check_congruence` does not validate rule instances** — a wrong rule instance used as a premise passes. | 4 | Tier-0 procedural re-application is load-bearing; the negative test must corrupt a **rule instance**, not just the chain. |
| R8 | **Unsoundness via the agent hint channel.** | 7 | Hints proved admissible before use; the fuzz generator must deliberately emit malformed, dishonest, and adversarial proposals and assert rejection. |
| R9 | **Arena/kernel feature soundness.** Nat arithmetic, String literals, and K-like reduction are new soundness surface in a *checker*. | 9 | Degenerate-case fuzz (`Nat.div`-by-zero literals, `Char` out-of-range) plus differential gates against pinned real `lean` — fixture passes are not enough. |
| R10 | **Arena aliasing / fresh-symbol collisions across chained edges.** `Fpa2Bv`'s ±0-sign trick is over-approximating *only because* its minted symbol stays genuinely free; a later edge constraining it silently breaks the direction claim. | 1 | Chain-wide fresh-namespace discipline; `int_real_relax.rs` clones the arena deliberately — follow that pattern. |

## Tier 2 — can waste the effort

| # | Risk | Phase | Mitigation |
|---|---|---|---|
| R11 | **No learning signal.** Every pack instance decides in milliseconds; a policy trained on them learns noise. | 2, 3 | G1 runs before anything expensive; weight the eval set toward `progress_frontier` ladders and public corpora. |
| R12 | **The `auto.rs` refactor regresses silently.** 8,616 lines of order-dependent fast paths; the 829-commit `nia_unsat` bisect is precedent. | 3 | T3.5's byte-identical differential gate before any learning; full pre-merge gate set on every slice. |
| R13 | **Hand-transcription rot.** JSON mirroring code is stale on the next commit. | 0, 1, 3 | Generate from Rust, golden-test, make recorder labels registry consts so the compiler enforces coverage. |
| R14 | **Family leakage in evaluation.** Generated variants share templates; an instance-level split overstates policy quality massively. | 2 | Group k-fold at family level; hold out knob ranges for parametric families. |
| R15 | **Prior poisoning.** If reward counts any decided verdict, a buggy uncertified chain gets scheduled *more*. | 3 | Only checked results score; a check-failure is a soundness alarm, not a low score. |
| R16 | **Explanation-chain blowup.** Explain-to-LCA is unminimized; congruence premises expand recursively. | 4 | G2 measures before committing to Tiers 1–2; FMCAD-2022 greedy minimization is the known fix. |
| R17 | **Bridges with no traffic.** WZ, generating-function, spectral, permutation certify things the solver cannot express. | 5 | Each must show a measured frontier delta or be labeled CAS-surface capability. |
| R18 | **Gröbner / CAD / SDP blowups.** Lex-only Buchberger on i128; CAD doubly exponential; floating SDP → exact rounding fails on non-strictly-feasible instances. | 5 | Honest budgets; do not build CAD; LDLᵀ/DSOS before any SDP. |
| R19 | **Proof-scale blowup.** `check_drat` is in-memory with linear-scan deletion — roughly quadratic. Schur 5's conversion + checking cost 2.5× its solving. | 6 | Streaming + backward checking; native-LRAT engines; check-then-delete; on-the-fly checking. |
| R20 | **Split quality.** march-class heuristics embody years of tuning; naive splitters yield catastrophically unbalanced cubes. | 6 | Budget accordingly; AlphaMapleSAT shows a learned route can beat march and suits this codebase better. |
| R21 | **Low agent yield.** The gap is dominated by `Unsupported`, which no LLM converts. | 7 | If the pilot converts fewer than ~5 problems per $100, demote to decline-mining and shadow generation. |
| R22 | **Mathlib capability is 4–8 part-time months** whose unique payoff is largely reputational. | 9 | Explicitly ADR-gated optional capstone; the technical residue is captured earlier by the Arena ladder. |

## Tier 3 — process and credibility

| # | Risk | Phase | Mitigation |
|---|---|---|---|
| R23 | **Overclaiming.** The October 2025 Erdős retraction shows how fast credibility burns. Small-N evidence has famously reversed (Pólya false at ~906 million; Skewes; Mertens). | 8 | "No counterexample below N" is a bound on the search, never support for the conjecture. The CLAIM-LABEL-MATRIX do-not-claim columns are load-bearing. |
| R24 | **Determinism erosion.** Three separate phases threaten the public promise in different ways: online learning (3), parallelism (6), and an LLM in the loop (7). | 3, 6, 7 | Offline-learner/committed-policy split; two-tier verdict/trace determinism; proposal ledger with network-free replay. Keep the LLM out of `just check` and the pre-push hook. |
| R25 | **Duplicated effort.** Nexus-style proof search, Plausible-style testing, and AlphaEvolve-style construction search are all occupied. | 8 | The uncrowded work is triage + certificates + tie-back. If a task drifts toward "prove the conjecture," it is off-branch. |
| R26 | **Lineage dilution.** Axeyum's kernel ports nanoda's semantics; bug #14576 showed lean4lean inherited a bug nanoda rejects. | 9 | Market as independent code with shared lineage — never as fully independent derivation. |
| R27 | **Crate sprawl / dependency inversion.** A careless `axeyum-solver → axeyum-cas` edge drags 47k lines of search into the solver's audit surface. | 5 | T5.1 exists to prevent exactly this; ADR-0001 discipline. |
| R28 | **Multi-agent contention.** `auto.rs` is the hottest file; sweeps are hours of compute in a shared checkout. | all | New modules over `auto.rs` edits; sweeps foreground, in bench artifacts, never in pre-merge gates. |
| R29 | **Registry drift.** formal-conjectures flips solved problems in place; axeyum could end up "sweeping" solved problems. | 8 | Re-harvest per immutable `bench-v{N}` tag; retire flipped rows. |
| R30 | **Format flux.** lean4export calls format 3.1 "still in flux"; `exact_keys` strictness means any field addition breaks imports. | 9 | Fail-closed is correct; budget per-release maintenance. |
