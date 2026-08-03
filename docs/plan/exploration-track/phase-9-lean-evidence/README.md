# Phase 9 — the Lean evidence ladder and Comparator compatibility

Verdict from review, on the two sub-branches separately:

**(A) Independent re-checking — YES on the contract, NOT YET on the capability;
enter through the Lean Kernel Arena, not Comparator.**

**(B) Evidence ladder — YES, and it is mostly already built; the work is
consolidation, not construction.**

## (A) What Comparator actually is

Verified 2026-08-01. `github.com/leanprover/comparator`, Apache-2.0, Lean FRO. The
entire config schema is
`{challenge_module, solution_module, theorem_names, definition_names?,
permitted_axioms, enable_nanoda}` — one CLI argument, the config path.

Pipeline: landrun-sandboxed `lake build` + `lean4export` of challenge and solution
→ structural statement match (transitively byte-identical constants except declared
definition holes) → transitive permitted-axiom walk over the exported environment →
optional nanoda check → **unconditional** official-kernel replay. `enable_nanoda`
is additive, not a replacement.

**External kernels: no plug-in API.** nanoda is hardcoded except
`COMPARATOR_NANODA=<path>` (also `COMPARATOR_LEAN4EXPORT`, `COMPARATOR_LANDRUN`).
Its invocation is a temp JSON config
`{use_stdin: true, permitted_axioms, unpermitted_axiom_hard_error: true,
nat_extension: true, string_extension: true}` with the solution NDJSON piped to
stdin, sandboxed, exit 0 required.

**So a second kernel is a drop-in binary speaking exactly this contract** — an S/M
task over the existing `axeyum-lean-import::import_ndjson`.

**But Comparator is all-or-nothing**: it exports the full solution-module closure,
which for the ten challenges means mathlib at Lean 4.32, and it requires
`nat_extension: true` and `string_extension: true` — **exactly the two features
axeyum's kernel is missing.**

## The honest gap

| | Current | Target |
|---|---|---|
| Admitted declarations | 8–11 | mathlib, ~10⁵–10⁶ |
| Lean pin | 4.30, format 3.1.0 exact-string | 4.32, format 3.1.x range |
| Nat kernel arithmetic | literal succ-folding only; **general ops are TL2.8, deferred** | full `Nat.add/sub/mul/div/mod/pow/gcd/beq/ble/land/lor/xor/shift*` |
| String literals | **rejected fail-closed** (`lib.rs:582`, `literal-string-typing`) | typed + reducible |
| K-like reduction | `k` flag parsed and constrained (`lib.rs:1396-1402`) but **`Declaration::Recursor` stores no K flag and `tc.rs` has no K-reduction** | implemented |
| `max_records` | 2,000,000 default | mathlib-scale |
| Threading | single-threaded (`&mut Kernel` everywhere) | nanoda runs 4 threads: 353 s wall / 1,226 s CPU / 8.5 GB |

Arena mathlib timings (v4.29.1, 2026-08-01): zignodamus (Zig) 75 s, sokonanoda
86 s, still-nanoda 187 s, nanoda 353 s, official 4.32.2 1,502 s / 9.8 GB;
lean4lean currently *incorrectly rejects* mathlib.

**Estimate: features 2–4 person-months; scale/performance hardening 2–4 more;
realistically 4–8 months part-time to a mathlib-capable checker.**

## Why the Arena, not Comparator, is the entry point

`github.com/leanprover/lean-kernel-arena` (live at `arena.lean-lang.org`,
16 checkers) **explicitly welcomes incomplete kernels**: a checker is a YAML file
(build/run commands, NDJSON on stdin, **exit 0 accept / 1 reject / 2 decline**,
plus a `declines:` list). It provides the exact corpus ladder (init 1.1 min → std
1.9 min → cslib/cedar → mathlib 30 min) and 135 accept/reject conformance tests —
**a free soundness-negative suite** in exactly the style the project's methodology
demands, and a measured ratchet in the `progress_frontier` mold.

There is currently **no axeyum and no non-nanoda-lineage Rust kernel** in the Arena.

## The lineage caveat — state it honestly

ADR-0036 ports nanoda's `whnf`/`def_eq`/`infer` and inductive machinery. The live
external validation of the diversity thesis is also its caveat: kernel-soundness
bug #14576 (nested-inductive `False` proof, found 2026-07-25) — **nanoda rejects
it, lean4lean inherited it**, because lean4lean shares lineage. Six further
AI-found kernel fixes were all caught by nanoda.

**Market axeyum as independent code with shared lineage — never as fully
independent derivation.** The Arena's reject-tests partially mitigate.

Also note Comparator's own README warning: configs with `definition_names` holes
are only name/type-matched, so a second kernel **does not** close the
statement-auditing hole. Do not oversell what re-checking the ten challenges proves.

## (B) The evidence ladder — rungs

| Rung | Meaning | State |
|---|---|---|
| R0 | verdict + `TrustId` steps | built |
| R1 | DRAT | built; **upgrade to LRAT** for verified-checker compatibility |
| R2 | theory certificate (Farkas/SOS/Diophantine/eager-elim recheckers) | built |
| R3 | Alethe + Carcara crosscheck | built |
| R4 | Lean reconstruction accepted by the embedded kernel (`False` from prelude axioms only) | built per fragment (`reconstruct.rs` 2,793 + `int_reconstruct.rs` 3,489 lines) |
| R5 | official `lean` accepts the rendered module, `#print axioms` clean | built — `tests/lean_crosscheck.rs`, **70/70 under pinned Lean 4.30** |
| **R6** | **self-challenge artifact** — emitted solution module + a challenge module restating the proposition + permitted-axiom whitelist from `trusted-axioms-by-fragment.md` + official `lean4export` of both + re-admission through `axeyum-lean-checker` | **new** |

**R6 is the payoff and it needs only the small preludes, not mathlib.** It closes a
Comparator-shaped loop on axeyum's *own* artifacts and reuses deliverable (A).1
verbatim. This is where (A) and (B) genuinely share machinery.

**Bridge-search integration:** every search result's `EvidenceReport` records the
rung reached and the `TrustStep` set. Define "checkable evidence" as **rung ≥ R2
always, R4+ for any headline claim**, and forbid an R4+ claim that touches an
undischarged axiom-ledger row.

## The live governance debt

`docs/plan/lean-axiom-ledger-v1.json`: **65 assumptions (30 real, 34 integer,
1 string), all `unclassified`/`unreviewed`.** Discharging this is a prerequisite for
R4+ claims and is the cheapest task in the phase.

## Prior art

- **lean-smt** (CAV'25) — CPC per-rule replay, 71% verification rate, BV
  "experimental". <https://github.com/ufmg-smite/lean-smt>
- **Alethe + Carcara** — Rust, elaborates Alethe→Alethe, **no Lean backend — an
  open niche.** <https://github.com/ufmg-smite/carcara>
- **cvc5 CPC/Eunoia/Ethos** — calculus-as-data. **SMTCoq** — the reflection pattern.
- **lean4checker → in-toolchain `leanchecker`** (archived): *not* an external
  verifier — it replays the official kernel. **lean4lean**, **trepplein** (dormant).
- **Most load-bearing: Lean core's `bv_decide`** (v4.12.0+, OOPSLA'25) — verified
  bit-blasting + external CaDiCaL **LRAT** + a Lean-verified LRAT checker run via
  `ofReduceBool` (compiler in TCB). **Axeyum's BV→AIG→CNF→DRAT pipeline is
  structurally isomorphic**; emitting LRAT targets Lean's existing verified checker,
  and an artifact checkable by the kernel alone differentiates on the
  `ofReduceBool` TCB expansion. <https://dl.acm.org/doi/10.1145/3763167>

## Tasks

| id | title | size |
|---|---|---|
| [T9.1](T9.1-axiom-ledger-triage.md) | Axiom-ledger triage: classify all 65 rows | M |
| [T9.2](T9.2-lean-checker-binary.md) | `axeyum-lean-checker` nanoda-contract binary | M |
| [T9.3](T9.3-evidence-rung.md) | Evidence-ladder rung in `EvidenceReport` | S |
| [T9.4](T9.4-r6-self-challenge.md) | **R6 self-challenge artifact for one fragment** | M |
| [T9.5](T9.5-arena-submission.md) | Arena submission + local harness | M |
| [T9.6](T9.6-nat-kernel-arithmetic.md) | TL2.8 Nat kernel arithmetic | L |
| [T9.7](T9.7-string-literals.md) | String-literal typing/reduction | M |
| [T9.8](T9.8-k-like-reduction.md) | K-like reduction | M |
| [T9.9](T9.9-export-pin-limits.md) | Export-pin range 4.30→4.32 + limits/memory audit | S |
| [T9.10](T9.10-corpus-ladder.md) | Corpus ladder: `Init` then `Std` | L |
| [T9.11](T9.11-mathlib-comparator.md) | Mathlib + ten-challenges Comparator run (optional capstone) | L |
| [T9.12](T9.12-lrat-emission.md) | LRAT emission alongside DRAT | M |

## Sequencing recommendation

1. **(B)-consolidation first** — T9.1, T9.2, T9.3, T9.4, T9.12 are S/M, reuse
   existing machinery, serve the track's checkable-evidence goal directly, and
   produce the Comparator-compatible binary as a side effect.
2. **Arena next** (T9.5) — the honest, incremental venue; free conformance and
   soundness-negative coverage; turns kernel-breadth work (T9.6–T9.9) into measured
   ratchets instead of a monolithic bet.
3. **Mathlib capability and the ten-challenges run (T9.10–T9.11) are an explicitly
   optional, ADR-gated capstone** that must not starve the other lanes: 4–8
   part-time months whose unique payoff is largely reputational. Its genuine
   technical residue — a hardened, fast importer and kernel — is captured earlier
   and more cheaply by the Arena ladder.

**The synergy claim is true at the bottom of the ladder and honestly weak at the
top.** T9.2 and T9.4 serve both sub-branches; nothing in (A) advances Destination-2
solver performance.

## Risks

- **Lineage dilution of the diversity claim** (see above).
- **Comparator has no plug-in API** — `COMPARATOR_NANODA` is an impersonation seam,
  not a contract, and the hardcoded config shape can change without notice (HEAD
  already moved to 4.33.0-rc1). Track upstream; consider proposing a real
  multi-kernel config. Note `hanwenzhu/nanocomparator`, a pure-Rust reimplementation,
  as an alternative harness.
- **Format flux** — lean4export calls format 3.1 "still in flux"; the importer's
  `exact_keys` strictness means any field addition breaks imports. Fail-closed is
  correct; budget per-release maintenance.
- **Scale unknowns** — `max_records` below mathlib size; `ExprId`/`NameId` are
  `u32` (4.29B-node cap); the whnf cache keyed by `(ExprId, env-size)` strands
  entries per declaration; single-threaded vs nanoda's 4 threads; RSS band 6–13 GB.
- **Wrong-verdict exposure in new kernel features** — TL2.8/String/K-reduction are
  soundness surface. Each needs degenerate-case fuzz generators (`Nat.div`-by-zero
  literals, `Char` out-of-range) and differential gates against pinned real `lean`,
  not just fixture passes.
- **Prestige-race risk** — the Arena already has faster Rust/Zig kernels (75–187 s
  mathlib). Being "another nanoda-lineage Rust kernel" wins little unless it feeds
  the repo's own trust story, which it does via T9.4/R6.
