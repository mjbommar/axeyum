# Family: SMT-COMP tracks other than single query

The parity board measures the equivalent of the Single Query track. SMT-COMP
runs four tracks; we have never measured the other three.

| Track | State | Note |
|---|---|---|
| Single Query | this is the parity board | eleven divisions |
| **Model Validation** | **not entered; rank 5** | we already replay every `sat` against the original term |
| Parallel | not entered | out of scope for now |
| Cloud | not entered | out of scope for now |
| ~~Proof Exhibition~~ | **does not exist** | introduced 2022, unranked 2023, discontinued 2024 |

## Model validation is the cheap one

Every `sat` we return is already checkable by evaluating the original term
against the lifted model — that is a hard rule in this repository, not a
feature. What is missing is the track's own output conventions and its official
validator, not the capability.

## On proof exhibition

The track was discontinued, so **"we would win proof exhibition" is not a claim
anyone can make.** The 2024 rules give the reason verbatim: the organizers
could not find a way to turn it into a competition. This strengthens rather
than weakens the argument that certificate production is an uncontested axis —
it is uncontested because adjudicating it was judged too hard, not because it
is not valued.

The honest external framings that remain are an entry in the SAT competition,
a trusted-base comparison, or a head-to-head against a kernel-checked pipeline
on QF_BV, for which a public reference cost now exists.

## Owning document

[The survey](../../../research/02-ecosystems/competition-landscape-2026-09/smt-lib-and-smt-comp.md)
