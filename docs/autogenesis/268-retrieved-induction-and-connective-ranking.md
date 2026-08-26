# Retrieved induction and connective ranking

Date: 2026-08-26

## Result

The first held-out-safe retrieved-induction census converts one of the 51
remaining open-population rows: `Nat.choose n 1 = n`. The independent imported
kernel admits the generated proof with one binder, one structural induction,
an empty axiom footprint, and direct theorem dependencies on
`Nat.choose_succ_succ`, `Nat.choose_zero_right`, `Nat.succ_add`, and
`Nat.add_comm`.

This is the first positive construction result on this immutable open
population. It is not yet an authoritative fact transition or autonomous
production credit. The measurement route deliberately performs no operation
registration and no ledger mutation.

The full result is
[`open-ranked-transport-induction-census-v1.json`](../../artifacts/autogenesis/open-ranked-transport-induction-census-v1.json):

- 51 rows measured, with zero held-out access;
- one positive target accepted and 23 declined after import;
- 27 statement capsules rejected before proof search;
- zero of six independently checked false controls accepted;
- 262 candidate theorems composed, 119 reused from capsules, and 99 transport
  attempts declined independently;
- seven equality goals reached the terminal grammar but did not close, one
  exceeded the binder budget, and fifteen had a non-equality terminal shape.

The companion
[`open-lemma-rewrite-support-ranking-v1.json`](../../artifacts/autogenesis/open-lemma-rewrite-support-ranking-v1.json)
contains the untrusted retrieval context. Its generator first retains four
topical anchors from the existing held-out-safe ranking, then ranks up to eight
axiom-free connective lemmas whose names expose non-goal operator vocabulary
introduced by those anchors, then retains the remaining topical candidates.
It uses canonical theorem types, direct type dependencies, and graph
centrality. It does not read a target proof, producer outcome, held-out
statement, or per-target override.

## What changed in the producer

`propose_bounded_induction_with_rewrites` is an additive API. The legacy
no-retrieval entry point delegates with an empty declaration list and retains
its existing authority boundary.

The new route:

1. receives exact caller-ranked declaration handles and never scans the
   environment for topical lemmas;
2. builds a bounded typed specialization closure from current local variables,
   terminal terms, and the induction hypothesis;
3. gives every retrieved declaration a fixed-width beam so one branching
   theorem cannot starve every later premise;
4. canonicalizes only closed constructor-valued subterms, allowing imported
   `OfNat` numerals to meet native constructor statements without unfolding a
   stuck recursive goal;
5. performs one exact forward equality rewrite at a time, restarts the stable
   ranking after every step, rejects cycles, and stops at a fixed rewrite
   count;
6. permits a whole-term definitional match only after an exact rewrite has
   already made progress, bridging transparent notation wrappers without
   launching recursive residual search; and
7. returns an untrusted proof term that earns credit only after same-kernel
   inference, theorem admission, dependency measurement, and axiom-footprint
   measurement.

The earlier experimental implementation was rejected: it passed the local
example but recursively launched residual proof search for every retrieved
equation and failed to finish the 51-row census in ten minutes. The landed
design never delegates retrieved premises into that broad residual path.

## What this proves—and what it does not

The result proves that the retrieval, transport, induction, reconstruction,
and checking seams can compose a previously open Mathlib-derived proposition
without per-target proof code. The exact proof dependency closure also proves
that retrieved library facts materially participate in the term; this is
stronger than a scheduler merely selecting a target after another fact became
available.

It does not prove broad autonomous yield. The measured conversion is 1/51
(2.0%), or 1/20 among importable positive targets. Twenty-seven rows never
reach the producer, and fifteen of the remaining declines are outside its
equality-only terminal grammar. The full run is also expensive because each
row independently rebuilds a proof-isolated capsule and transports up to
twenty candidate closures.

## Sequence from here

1. Register this exact producer/ranking/receipt tuple as a multi-target
   operation only after the agent episode and crash-safe transaction schemas
   carry the retrieved candidate identities and ranking digest. Then rerun the
   selected open fact through a clean authoritative episode; do not convert the
   measurement artifact into ledger status by hand.
2. Cache independently checked transported candidate closures by exact source
   identity and target-kernel compatibility. Measure import, transport,
   specialization, and kernel-check time separately before raising any search
   budget.
3. Route the 27 import rejections through the existing type-slice
   generalization boundary. Keep that denominator separate: no producer grammar
   change can improve rows that never reach it.
4. Add producer families for the fifteen non-equality terminal shapes based on
   their parsed heads and obstruction clusters. Do not widen this equality
   grammar until a repeated equality decline demands it.
5. Mine the seven `TerminalNotDefEqNoRewrite` traces into missing connective
   edges and minimal premise sets. Evaluate any ranking change on the frozen
   train/development population while continuing to exclude held-out rows
   before capsule access.
6. After one clean transition, recompute the frontier and require a later proof
   to consume the newly admitted theorem. That closes the stronger
   proof-compounding arrow; one isolated conversion does not.

Over the horizon, this two-stage retrieval should become a typed proof-plan
graph: topical lemmas introduce operators and intermediate propositions;
connective lemmas normalize or transport them; solver/CAS certificates discharge
decidable leaves; and the kernel checks the assembled plan. Retrieval remains
untrusted policy throughout. Only replayed evidence changes durable knowledge.
