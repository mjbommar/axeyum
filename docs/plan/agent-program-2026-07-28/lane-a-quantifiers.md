# Lane A — Quantifiers (the capability gap)

**Ranked-program anchor:** Rank 3 — *the biggest capability gap in the library.*
**Phase:** [P2.6 Quantifiers](../track-2-theories/P2.6-quantifiers.md) (MAM
e-matching, trigger inference, MBQI, QE/MBP).
**Worktree / branch:** `~/projects/personal/axeyum-quant` / `agent/quant/mbqi-sat-direction`.
**Owns:** `crates/axeyum-solver/src/quant_*.rs` (~35 modules), `crates/axeyum-egraph/`,
quantifier test files.
**Blocks on:** Phase 0. A3+ additionally wants Lane F's F1 (CDCL(T) default
dispatch) — *"e-matching walks the e-graph"*
([`01-dependency-dag.md`](../01-dependency-dag.md)).

---

## The gap, stated honestly

Competitive anchors refreshed to **SMT-COMP 2025** — see
[`smtcomp-2025-parity-targets-2026-07-28.md`](../smtcomp-2025-parity-targets-2026-07-28.md).

| | benchmarks in library | axeyum | winner @ SMT-COMP'25 | Δ vs '24 |
|---|---:|---|---|---:|
| UFLIA | 10,128 | ~1 % on the s4 run; **0/5** on the curated SCOREBOARD row | **cvc5 58.1 %** (1,656/2,849) | +0.98 |
| UF | — | not measured | **cvc5 40.5 %** (1,158/2,857) | −0.67 |
| UFNIA | 13,464 | partial | cvc5 59.8 % (3,772/6,313) | +1.01 |
| AUFLIRA | 20,011 | 0 % | cvc5 93.6 % (1,575/1,683) | +0.36 |
| AUFDTLIRA | 11,043 | 0 % | cvc5 88.1 % (4,158/4,721) | −0.76 |

That is >54k benchmarks in those four alone, >100k across the quantified block,
and the champions decide a real fraction — so this is a **capability** gap, not
"everyone declines these."

**Three things the 2025 data changes about this lane's plan:**

1. **Start with UF, not UFLIA.** cvc5 wins UF with only **40.5 %**, the
   runner-up (iProver) is 410 behind at 748, and **59 % of the division is
   unsolved by anyone**. It is the quantified division where a new entrant can
   become non-embarrassing fastest. UFLIA is the headline gap; UF is the
   cheaper first proof that the sat-direction machinery works.
2. **Do not start with AUFLIRA/AUFDTLIRA** (task A5's ordering is revised
   accordingly). At 93.6 % and 88.1 % there is little headroom and cvc5 is far
   ahead — they are volume, not opportunity.
3. **The frontier is nearly static.** Across all five quantified logics the
   2024→2025 movement is between −0.76 and +1.01 points, and cvc5 is
   uncontested in every one. The gap will not close on its own while we work
   elsewhere, but neither is it running away from us.

**What is already landed.** Finite expansion, E-matching, and narrow MBQI are in
(ADR-0016, ADR-0095–0141, ADR-0357–0359). On the fixed 765-row cvc5-UNSAT gap
selection at 250 ms / one worker, the deterministic retained frontier is
**133 UNSAT with zero retained loss**, built from: the +82 bounded strict-ground-
core probe (59 Tokeneer / 17 Simplify2 / 6 Sledgehammer), the predecessor-
recurrence sign route (+1), and top-level theorem-counterexample normalization
(+4).

**What is not landed — the actual hole.** The **general sat direction**. Every
decision above is an UNSAT route. Nothing constructs a checked model for a
satisfiable quantified formula outside the one-binder almost-uninterpreted
`Int`/`Real` UF slice of ADR-0357.

**Parity here means honest `unknown` plus a competitive decided fraction — not
100 %.** Even cvc5 tops out near 57 % on quantified UFLIA.

---

## A1 — Census the residual (W1, do this first)

**Goal.** Stop choosing mechanisms from estimates. Classify what the 765-row
selection still declines, by *shape*, and commit the census as an artifact.

**Why.** STATUS's own next-step text says it twice: *"census the remaining large
ground-core residuals before widening the probe"* and *"scope T2.6.5/T2.6.1
against the measured quantified-logic residual shapes … not from estimates
(G4 discipline)."*

**Steps**
1. Re-run the 765-row selection off the post-Phase-0 `main` at 250 ms internal,
   one worker. Confirm 133 UNSAT retained.
2. For each of the ~632 non-decisions, record: declared status, quantifier
   prefix shape, binder count and sorts, trigger availability, whether the
   ground core is nonempty, which route declined and why, and the terminal
   result class (`unknown` vs `unsupported` vs outer timeout).
3. Bucket by mechanism that would decide it: MAM/trigger, multi-binder MBQI,
   model repair, interpreted-occurrence MBQI, QE/MBP, ground-core widening,
   arithmetic strength, "genuinely hard."
4. Split declared-`sat` from declared-`unsat` rows — the sat rows are the
   T2.6.5 target population and should be sized separately.

**Deliverable:** `docs/plan/quantifier-residual-census-2026-07-XX.md` plus a
machine-readable JSON under `bench-results/`, with per-bucket counts and three
named representative rows per bucket.

**Exit criteria:** every non-decision is in exactly one bucket; the top three
buckets by count are named with their exact row counts; A2's population is
selected *from* this census, not from this document.

**Size:** M (measurement-heavy, no solver change).

---

## A2 — T2.6.5: general model-based instantiation (the sat direction)

**Goal.** Extend checked MBQI beyond the ADR-0357 one-binder almost-
uninterpreted `Int`/`Real` UF slice to the residual sat shapes A1 identified.

**Open sub-arcs, in dependency order:**
1. **Multi-binder profiles** — the current slice is one-binder. Multi-binder
   quantifiers need a candidate-model representation over tuples and a
   termination bound on the instantiation round.
2. **Model repair** — when a candidate model falsifies an instance, repair it
   locally rather than restarting the round.
3. **Broader interpreted occurrences** — arithmetic and array terms under the
   binder, not just uninterpreted applications.

**Soundness stance (non-negotiable).** Broaden the *search* (instantiation is
untrusted); keep the *check*. Every reported quantified `sat` must replay the
candidate model against the **original** assertions through the source
evaluator, exactly as the Noetzli source-witness route does. No model, no `sat`.

**Bounds.** Instantiation rounds, candidate-tuple count, and per-round term
generation each need an explicit deterministic cap that degrades to `Unknown`.
Precedent: the 20,000-assignment cap in the string source-witness route and the
`MAX_CROSS_PRODUCTS` NRA admission bound.

**ADR required** before the public surface changes. Preregister the admitted
shape class, the caps, and the replay contract — follow the ADR-0357/0367/0370
pattern (freeze the admitted class *before* observing gains).

**Exit criteria**
- A named subset of A1's declared-`sat` bucket decides `sat` with model replay
  against the original source, 100 % replay success.
- Zero retained UNSAT lost; zero verdict flips on the 765-row selection.
- A mutation control set (perturbed models, malformed bindings, cap exhaustion,
  unsupported syntax) all decline to `Unknown`.
- Cross-checked against cvc5 and Z3 in both verdict directions on the gains.

**Size:** L. Slice it: multi-binder profiles first as an independent increment,
then repair, then interpreted occurrences. Each slice lands green on its own.

---

## A3 — T2.6.1: the MAM (bytecode e-matching abstract machine)

**Goal.** Replace the current e-matching with a compiled bytecode abstract
machine with generation-cost scheduling. Explicitly open in the support matrix.

**Why now:** it is the throughput lever under both A2 and the UNSAT routes —
the 133 decisions are all budget-sensitive (the shared 250 ms deadline gates
them), and load-sensitive rows have already shown up as non-credited noise.

**Reference reading:** Z3's `mam.cpp` and cvc5's inst-match generators under
`references/`. Read them before designing.

**Gated on:** Lane F1 (CDCL(T) default dispatch) if the MAM is to walk the live
backtrackable e-graph rather than a snapshot.

**Exit criteria**
- Same decisions as today on the 765-row selection at the *same* deadline, with
  measured lower time-to-decision — or more decisions at the same deadline.
- Zero retained loss. Report the conservative floor across ≥3 runs, not the
  best run.
- Deterministic: identical output across repeated runs at fixed seed and
  worker count.

**Size:** L.

---

## A4 — T2.6.2: trigger inference and multi-triggers

**Goal.** General trigger inference, including multi-triggers, replacing
whatever narrow inference is in place.

**Exit criteria:** a measured decide-rate delta on A1's trigger bucket with zero
retained loss; the inference is deterministic and its choices are inspectable in
the evidence artifact.

**Size:** M–L. **Gated on:** A3 (the MAM is the natural consumer).

---

## A5 — Extend beyond UFLIA: AUFLIRA / UFNIA / AUFDTLIRA

**Goal.** Move the 0 %-decide quantified logics off the floor. AUFLIRA alone is
20,011 benchmarks — larger than UFLIA.

**Prerequisites:** these need quantifiers *combined* with arrays (P2.2),
mixed int/real arithmetic, and datatypes (P2.9). Confirm each combination is
live on the CDCL(T) spine before claiming a fragment.

**Steps**
1. Build a curated slice per logic from the staged library, on the model of the
   existing cvc5-regress rows, so each gets a SCOREBOARD row.
2. Measure the honest baseline first (expect near-0 %) and commit it — a
   measured 0 % row is worth more than an unmeasured absence.
3. Attack in library-volume order: AUFLIRA → UFNIA → AUFDTLIRA.

**Exit criteria:** each logic has a committed SCOREBOARD row with DISAGREE = 0,
and a measured, nonzero decide-rate for at least AUFLIRA.

**Size:** XL — this is a multi-wave arc, not one task. Do not start before A2
has landed at least one slice.

---

## Lane A rolling exit (the Rank 3 exit criterion)

> Quantified UFLIA/AUFLIA/AUFLIRA decide-rate off the floor — a measured
> fraction approaching cvc5's on the same selection — with zero wrong verdicts.

## In-flight declarations

*(Each agent appends the function-level regions it is editing here before its
first commit touching a shared file. Keep newest at top.)*

- _(none yet)_
