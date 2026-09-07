# Lane: evidence-preprocessing — the certificate chain's one open hole

<!-- plan-section: lane-status -->

**Lane block (`WIP`, evidence-preprocessing, 2026-09-06).** Task 1 of the
evidence family's next-actions list is done: ADR-1704 now carries a Prior art
section citing eDRAT (Hitarth, Codel, Lachnitt, Dutertre, FMCAD 2024,
DOI 10.34727/2024/isbn.978-3-85448-065-5_8), read from the open-access PDF
rather than summarized from the abstract. The comparison is convergence on the
two-stream shape and five recorded differences; the load-bearing one is **RAT**.
eDRAT restricts its propositional checker to RUP additions and rejects RAT;
ADR-1704 hands the unchanged `check_drat`, which accepts both. The hazard does
not reach ADR-1704 as decided — the extended formula is fixed before checking
and *every* lemma is discharged or counted — but it would the moment we adopted
eDRAT's core-pruning optimization, so that pairing is now recorded as a
constraint in the ADR. `check_lrat` already rejects RAT
(`LratError::RatNotSupported`), so the LRAT arm of §2's composition already
agrees with them by accident.

Next: ADR-1721, the preprocessing certificate obligation for `axeyum-rewrite` —
what a denotation-preserving rewrite owes versus a satisfiability-preserving
one, which existing rewrites can discharge cheaply, how a preprocessing
obligation composes with ADR-1704's two streams into one input-to-CNF artifact,
and the smallest end-to-end slice.

<!-- plan-section: landed-changes -->

| 2026-09-06 | evidence-preprocessing | ADR-1704 gains a Prior art section: eDRAT (FMCAD 2024) cited, five differences recorded, and the RAT/core-pruning pairing named as a constraint |
