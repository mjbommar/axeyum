# Autogenesis-1 result

Date: 2026-08-18

## Verdict

**Passed, within the preregistered bootstrap scope.** From exact source commit
`cf998788b96ad0ef3fbcc26108a032e34e6d7fa5`, two isolated runs independently
reproduced the complete acquisition:

```text
pre-B A, budget 1 -> no proof
B, budget 2       -> proved -> checked -> crash-recovered -> recorded
durable B event   -> exactly A newly ready
A, budget 1       -> proved using episode-local B -> checked -> recovered -> recorded
```

The result satisfies the programme definition: fixed inputs and budgets,
machine selection, two separate authoritative ledger transitions, a causal
unlock, the same-target and same-budget counterfactual, no human-written or
repaired proof after launch, no retained-answer dependency, no axiom footprint,
no trusted-base change during either run, and clean-room repetition.

## Retained identity

The large receipts are external by design. Git retains only the small
content-addressed [result index](../../artifacts/autogenesis/autogenesis-1-result.json).
On the measured host, the receipts are under
`/nas3/data/axeyum/autogenesis/chains/cf998788b/`.

| Object | Identity |
|---|---|
| source commit | `cf998788b96ad0ef3fbcc26108a032e34e6d7fa5` |
| reconstructed prestate | `a65e95fff849edd58ed9b4d708c2a68d029bcc01` |
| deterministic pre-A state | `a17ef4fa54581245325e7edff1fee385db0baaf5` |
| operation registry | `b59187a9951fba7f17d8558ff78f5358c6dd9c00484dc216112ed90914220893` |
| each run | `d6e7b20dfeadd6750cd6080d36425db58565749f2f381b741f17b0534b536102` |
| semantic identity | `1e0107d6496b9101c4292c1b39ba0ae5b8c4c2212ed6a49427b37204a6fbccd3` |
| reproduction | `60c6dec66eff79f5dc4192c18f038ed06356a64435129ba0a01b179f612342aa` |
| thin pre-A state bundle | `f551a087de33dc748908c043bd6267e0dfc0b9241730fad75fb7f2c6980bfc55` |

The thin bundle is 3,089 bytes and declares the exact source commit as its
prerequisite. The earlier full-history prestate bundle was about 319 MB. This
keeps Git history out of experiment storage while still retaining the otherwise
unreferenced intermediate state.

## Causal and assurance audit

The pre-B control and credited A execution both used budget 1. This matters:
an earlier automated attempt correctly failed the completion audit because its
counterfactual used budget 20. That run is retained as engineering evidence but
receives no Autogenesis-1 credit.

The credited B receipt is
`23333a458f7a0aa9defdead7fc86269427cf1ea82e7cb4e8199ce7f1872d52fe`.
Its durable event produced exactly one authoritative write, zero fixture writes,
and `newly_ready: [F:nat-mul-one]`. The credited A receipt is
`0d0ee2980087ed5aab4282f351410077afd474a537338c3317315a08b7ea74bf`.
Its kernel observation names an `Autogenesis.Authoritative.E...premise`, not the
retained `Nat.zero_add` theorem. Both observations report empty axiom footprints
and empty retained-answer dependency lists.

Both writes intentionally stopped after durable intent with exit status 75,
left the target fact unchanged, and then recovered. The final frontier removed
A and selected no remaining registered candidate. The two runs matched all 56
retained artifact files byte for byte, including the pre-B negative-control
receipts, executions, transactions, durable events, readiness deltas, final fact
rows, and thin Git bundle.

## Reproduction

From a clean checkout of the exact source commit:

```sh
just autogenesis-authoritative-chain /external/path/run-1
just autogenesis-authoritative-chain /external/path/run-2
just autogenesis-authoritative-compare \
  /external/path/run-1 /external/path/run-2 /external/path/reproduction.json
python3 scripts/check-autogenesis-1-result.py
```

The runner refuses a dirty source, in-repository or existing output, ambiguous
frontier selection, unreviewed gate mention, mismatched trigger, failed checker,
cross-filesystem transaction journal, compare-and-swap drift, non-empty
footprint, retained answer, unexpected changed path, or incomplete semantic
audit. It publishes the retained directory only after all checks pass.

## What this does not prove

Autogenesis-1 is one exact, deliberately small Nat chain. It does not establish:

- a generic theorem-application operation;
- broad autonomous theorem yield;
- a dense or held-out nursery;
- heterogeneous proof-plan composition;
- learned search policy improvement;
- useful conjecture generation; or
- generalization beyond this preregistered proof shape.

The next programme work should therefore preserve this result as a longitudinal
regression and let held-out failure distributions pull Phase 3 interfaces. The
correct horizon is typed heterogeneous proof planning, but the immediate next
artifact is a nursery/evaluation slice capable of showing which composition
seam actually dominates.
