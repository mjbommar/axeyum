# Lane E — Lean parity & certified evidence

**Ranked-program anchor:** Rank 7 — *parity's other axis, and the actual
differentiator.*
**Gaps:** G5 (proof denominator), G6 (external Lean gate), G7 (kernel profile).
**Phases:** P3.1–P3.7, TL0.x / TL1.x / TL2.x.
**Worktree / branch:** `~/projects/personal/axeyum-lean` / `agent/lean/evidence-closure`.
**Owns:** `crates/axeyum-lean-kernel/`, `crates/axeyum-lean-import/`,
`crates/axeyum-alethe/`, `crates/axeyum-solver/src/evidence.rs`.
**Blocks on:** nothing — **start immediately.**

---

## The measured state

**Lean parity = every unsat/valid carries a machine-checkable proof.** Today:

| Quantity | Value |
|---|---|
| Baseline UNSAT decisions | 327 |
| → evidence-audit UNSAT outcomes | 325 |
| → certified **and** genuinely independently checked | 267 |
| → Lean-checked | 260 |
| **Full conjunction** | **259 / 327** |
| Residual: uncertified audit-row occurrences | 58 (dedup: **56 paths / 51 exact contents**) |
| Residual: reconstruction-only gaps | 8 |
| Residual: declared trust holes | 0 |
| Residual: QF_NIA `IntPow2` proof-production errors | 2 |
| Official-Lean fail-closed gate | **70 / 70** accepted, 0 skipped, 0 failed (local, pinned Lean 4.30) |

**The 58, attributed** (parser-backed census): split **25 arithmetic / 26
string-sequence**, with 31 / 15 / 12 occurrences attributed to the **string front
door**, **`auto-solve`**, and the **NRA fallback** respectively.

**The v2 refresh mattered.** The affected v1 rows historically had 28 vacuous
`bare-unsat` check booleans; v2 records **zero** and attributes all 58 residual
bare outcomes to a decision backend. Four stale QF_SEQ rows created before the
string evidence soundness fix lost source-invalid DRAT credit without verdict
changes.

**Dominance is not publication-ready:** 23/35 audited rows are fully dominant and
594/753 decisions are dominant *candidates*, but the v2 proof refresh changed 22
timing-derived flags, so paired timing cells must be refreshed before that count
supports any public claim.

---

## E0 — What the outside world actually validates (context, read once)

From [`smtcomp-2025-parity-targets-2026-07-28.md`](../smtcomp-2025-parity-targets-2026-07-28.md):

**SMT-COMP 2025 has no proof-production or proof-checking track**, and the rules
contain no proof-certificate requirements. The two nearest analogues:

- **Model-Validation Track** — validates *sat* answers mechanically via
  **Dolmen**: the model must satisfy the input and define all and only the
  user-declared symbols; INVALID scores as an error. This is exactly our hard
  rule *"every `sat` must be checkable by evaluating the original term against
  the lifted model,"* externalized as a competition track. **We should be able
  to enter it on the fragments we already support** — it is the one piece of
  concrete external validation available to this program today, and it would
  convert an internal invariant into a third-party result.
- **Unsat-Core Track** — core *minimization*, not proof checking. A core is
  validated if strictly more cross-checking solvers say unsat than say sat.

So: the community validates *models* mechanically but validates *unsat* only by
**solver-majority vote**. Two consequences, and they point in opposite
directions:

1. Our Lean/Alethe evidence axis is a genuine differentiator, not a catch-up
   item — and by the same token **no external number exists to measure it
   against.** Any claim we make here is ours to justify from first principles.
2. Note the direct tension: the Unsat-Core track's validation rule *is* "two
   untrusted searches agreeing." We rejected precisely that standard for our own
   QF_AUFLIA route in P0-B (unchecked scalar refutations now return `unknown`).
   We hold the stricter line deliberately — record it as a choice, not an
   oversight, whenever the comparison comes up.

For the cost side of the argument, the best external datum is Lean's
`bv_decide` in SMT-COMP 2025 QF_BV: the kernel-checked variant solved **224
fewer** benchmarks than the unchecked one (8,638 vs 8,862 of 10,703) — about
2.1 points of decide-rate as the price of checking.

---

## E1 — Route-provenance P1 and the QF_SEQ boundary (W1, first)

**Goal.** Trace the QF_SEQ source-to-lowered boundary and land route-provenance
P1 — **before** choosing a proof mechanism for the 58.

**Why this order.** STATUS states the sequencing directly: *"trace the QF_SEQ
source-to-lowered boundary and route-provenance P1 **before choosing a proof
mechanism**."* Picking a mechanism first means picking it for a route you cannot
attribute. The design is already written:
[`evidence-route-provenance-design-2026-07-21.md`](../evidence-route-provenance-design-2026-07-21.md).

**Steps**
1. Implement route provenance so every definitive result records *which* route
   produced it and *what* evidence that route can emit.
2. Trace the QF_SEQ source→lowered boundary specifically — it is where the four
   stale rows lost DRAT credit and where the string front door's 31 occurrences
   concentrate.
3. Re-derive the 58-occurrence census from provenance data rather than from a
   parser pass over audit rows, and confirm the 56/51 dedup reproduces.

**Exit criteria:** every one of the 58 occurrences is attributed to an exact
route with a named reason it lacks evidence; the census regenerates
deterministically; the provenance field is in the committed evidence schema.

**Size:** M–L. **Everything else in the lane keys off this attribution.**

---

## E2 — Close the string front-door gap (31 of 58)

**Goal.** The largest single evidence bucket. Give string-route UNSAT results
serializable, independently checkable evidence.

**Coordination:** this is jointly owned with **Lane B**. Lane B's B2 (concat
emptiness) will *create* new string UNSAT routes — those must be born with
evidence rather than added to this backlog. Agree the evidence contract with
Lane B before B2 lands.

**Note the paused work:** P3.6/TL2.9 *Checked String-literal semantics* is
**PAUSED after a pushed P0, with no product or parity credit**. Resume only from
its authoritative handoff — do not restart it from scratch.

**Exit criteria:** the string-front-door occurrence count drops from 31 with a
named mechanism per closed occurrence; each closed occurrence is either
independently rechecked in-tree or explicitly ledgered under P3.0's trust ledger.

**Size:** L.

---

## E3 — `auto-solve` (15) and NRA fallback (12)

**Goal.** The other two attributed buckets.

- **`auto-solve` (15):** the dispatcher chooses a route; the evidence must follow
  the chosen route. Largely a plumbing problem once E1's provenance exists.
- **NRA fallback (12):** the open arc is **per-cell Positivstellensatz proof
  reconstruction** (ADR-0044/0045/0046). The CAD decision side is complete; the
  proof side is not.

**Also here:** the **2 QF_NIA `IntPow2` proof-production errors**. These are
errors, not gaps — a proof route that *fails* is worse than one that declines.
Fix or convert to an honest decline.

**Exit criteria:** both buckets attributed to a mechanism with a landed slice or
an explicit, dated deferral note; zero proof-production *errors* remain.

**Size:** L (NRA Positivstellensatz is the heavy half).

---

## E4 — Remote attestation of the official-Lean gate

**Goal.** Convert the local 70/70 into a remote-attested gate.

**History — read it before touching the workflow.** The gate has failed in three
distinct ways already:
1. A Lake-only action failed setup → replaced by a checksum-pinned non-Lake
   elan installer, fail-closed on a missing binary (`AXEYUM_REQUIRE_LEAN=1`).
2. Its first real run rejected four modules (67/71): three lost Bool/BV iota
   rules under opaque-inductive export, one hit Lean's default elaborator
   recursion depth. Narrow export corrections + one elaborator-depth option
   reached 71/71.
3. The first corrected **remote** job failed *before* the representative sweep:
   `AXEYUM_LEAN_BIN` resolved to an unconfigured elan shim outside the
   repository working directory. The workflow now exports the versioned
   executable from `elan which lean` and preflights it from a temporary
   directory — **locally verified, remotely unconfirmed.**

The current fail-closed population is **70/70** (the FP soundness repair revoked
uncertified `Fpa2Bv` proof credit from one QF_FP row and the QF_BVFP family).

**Do not promote timing.** The first corrected run's Lean-worker phase took
6.8 s; a same-shape confirmation under different load took 53.3 s. Neither is a
performance claim.

**Exit criteria:** a remote job that accepts 70/70 with zero skipped and zero
failed, with archived duration and RSS. Only then size the scheduled exhaustive
tier. **Do not convert representative local source acceptance into full
proof-family or Lean parity** — that conversion is the specific error the parity
reset was written to prevent.

**Size:** M.

---

## E5 — Kernel compatibility (G7 / TL2.x), independent track

**Goal.** Continue the independent Rust Lean kernel toward the K-profile ladder.
This proceeds **independently of solver proof coverage** — do not couple them.

**Landed:** TL2.2–TL2.7 (projection representation / inference / reduction /
exact K1 import / structure eta / canonical arbitrary-precision `Nat`),
TL1.3 (owned completed-import publication), TL1.4 (226-case mutation corpus),
TL1.7 (canonical declaration + dependency identity), TL2.12 (recursive indexed /
reflexive induction hypotheses), TL2.13 (mutual inductive groups), TL2.14
(nested-inductive kernel elimination).

**Open:**
- **TL2.10** fixed quotient package and reduction — offline M1–M3 complete;
  **M4 differential and acceptance open.**
- **TL0.6.4** U2 native-surface classification — WIP.
- **TL0.6.5** U2 matched official/Axeyum execution — WIP; comparison contract,
  terminal schema, and typed normalization/axis projection landed.
- The four-root official blocker census (projection ✓ closed, Nat ✓ closed,
  **String** — 290-declaration closure, reaching Nat literals and recursive-
  indexed inductives — and **quotient** open).

**Scope discipline.** Current credit is *exact flat and direct-recursive fixture
credit* — not `Init`/`Std`/mathlib, not general kernel credit. A direct `.olean`
reader and full native ecosystem compatibility are late untrusted-adapter
phases, **not checker prerequisites**. Keep them late.

**Exit criteria per sub-task:** the pinned bounded kernel gate stays green
(179 unit tests, 35 integration cases across twelve binaries at the last
checkpoint) and each new construct ships with its mutation controls.

**Size:** XL, ongoing. Take one TL task per wave; TL2.10 M4 first.

---

## E6 — Make proof coverage a first-class denominator (G5)

**Goal.** Every decided-`unsat` anywhere in the program becomes a candidate for
the evidence pipeline, and the coverage number is generated, not narrated.

**Coordination:** Lane D's D4 publishes the coverage-weighted parity matrix;
this task adds the **evidence column** to it — for each logic, what fraction of
decided-UNSAT carries a checked proof.

**Exit criteria:** a generated proof-coverage denominator per logic, bound by
`check-parity-docs.py`, so a decide-rate gain that ships without evidence is
*visible* rather than silently uncounted.

**Size:** M. **Gated on:** D4 and E1.

---

## Lane E rolling exit

> The 58 uncertified occurrences are each closed or explicitly ledgered with a
> mechanism; zero proof-production errors; the official-Lean gate has a remote
> attestation with archived resource data; proof coverage is a generated
> per-logic denominator.

## In-flight declarations

- _(none yet)_
