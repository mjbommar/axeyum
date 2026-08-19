# Authoritative B admission result

Date: 2026-08-18

Implementation commit: `f4dc0d4f18a816ba9f468e3c3b8a68fdcd349859`

## Result

An isolated clean worktree reconstructed both facts in the qualified primary
chain as valid open ledger rows. The machine frontier selected
`F:nat-zero-add` alone while `F:nat-mul-one` was blocked on it. The registered
kernel operation then:

1. attempted exactly two catalog-only induction plans;
2. accepted plan 2 with the exact source-bound `Nat.zero_add` type;
3. reported an empty axiom footprint and no retained-answer dependency;
4. prepared one authoritative transaction without caller-authored admission
   metadata;
5. stopped after durable intent with the fact byte-identical;
6. recovered the compare-and-swap transaction to a durable admission event;
7. replayed the settled fact operation and validated the resulting ledger; and
8. derived `newly_ready: [F:nat-mul-one]` from the before/after frontiers.

The scheduler then refused to execute A because A has no authoritative
operation. That refusal is part of the result: B authority cannot leak into its
consequent.

## Retained evidence

The complete external bundle is:

`/nas3/data/axeyum/autogenesis/chains/f4dc0d4f1/b-admission/`

Its `experiment.json` has SHA-256
`48d82a4b46b4dec38d022172219125c503000af3989b117b4b337567a65e14f2`.
The bundle includes both frontiers, execution, transaction, durable intent and
event, readiness delta, exact open input facts, and a complete Git bundle of the
synthetic pre-state. `git bundle verify` reports a complete history at
`80462281a61debb138043532355b93a630aa6524`.

Key content identities are:

| Artifact | SHA-256 |
|---|---|
| Frontier before | `8f7a53699068ba990bb978a616203ccb3bcfc1ce26163bfb1b28b3a26fa4ce39` |
| Execution | `86f7ea3dfcedebcbdd21adf487911d08a68e30b324bcadcb8f8e603862b4b509` |
| Transaction | `4e3dc8979b2a5fb076e8826855873d85bd44307ed8a3c4e408f3e5b384d2398d` |
| Admission event | `8b2b2045119eb8ceaa59cba8a2df7b4e3fb1d4fde73a735bdf91f9e38af0c264` |
| Frontier after | `be02c24f87574ca04ebf4724b07855bd5fc13e731f3046deb2b22d2a5692b91a` |
| Readiness delta | `cc2fdaf49b8f5c29f6ff83789543272af48f04dda830322afa17118a8528685b` |

## Negative controls and scope

- A journal on a different filesystem was rejected before mutation; the valid
  attempt used a same-filesystem journal and archived it afterward.
- The injected post-intent fault exited 75 and left B unchanged.
- Exactly one authoritative write and zero fixture writes were recorded.
- A became dependency-ready, but remained unselected because it has no exact
  registered operation and its fixture gate mentions are unreviewed for A.

This earns authoritative B-admission and event-derived A-readiness credit. It
does **not** earn an A proof, A admission, or Autogenesis-1 production credit.
The next critical path is the episode-local `Nat.mul_one` apply operation.
