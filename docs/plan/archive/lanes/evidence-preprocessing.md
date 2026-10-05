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

**ADR-1721 landed, and so did its slice.** A preprocessing step owes one of
three obligations, chosen by what it does to the model set: a **replacement**
owes a denotation equality, a **relaxation** owes nothing for `unsat`, a
**strengthening** owes a per-constraint discharge. An obligation is discharged by
a certificate, a structural check, or the route declining to conclude in that
direction — a decline is a discharge (`blast_integers` already contains one), a
**re-derivation is not**.

The family page's premise was wrong and is corrected: preprocessing is not
evidence-free. Four of the trust ledger's 14 ids are preprocessing steps, and
two carry real re-checkable artifacts. What is open is which half they check —
both discharge the strengthening half and **re-derive** the replacement half.

Measured, then closed. Swapping read-over-write's `ite` branches made
`ArrayElimUnsatCertificate::recheck` return `Ok(true)` over a wrong `unsat` on a
satisfiable query. `witness_read_over_write` now interprets both sides under
sampled concrete assignments rather than re-running the transform; `recheck`
calls it as step 2 of five; the same mutation yields `Ok(false)` and kills
exactly one of the witness suite's four tests. It is sampled, so
`TrustId::ArrayElim` stays uncertified — evidence, not proof.

Gates: `cargo test -p axeyum-solver --lib --features full` — **1460 passed, 0
failed** (nonzero count confirmed, 1106 s); the array-elim certificate suite at
8; the new witness suite at 4; workspace clippy `-D warnings`, workspace
`check --all-targets --all-features` and `cargo fmt --all --check` clean;
`check-links.sh` ok. NOT run: the workspace test sweep and `just check`.
`check-merge-hygiene.sh` fails only on `gen-plan.py --check`, because this lane
added a status file and was told not to regenerate `PLAN.md` — the
coordinator's regeneration clears it.

Next for whoever picks this up: the same witness for `eliminate_functions`
(identical shape); `eliminate_int_divmod`, the only `unsat`-feeding transform
with no artifact of any kind and an unreported soundness-mode change at
`MAX_CONGRUENCE_GROUPS = 48`; and retaining the ADR-0408 denotation guard's
verdict past the pass, since `auto.rs:1744` currently swallows its refusal as an
ordinary decline.

<!-- plan-section: landed-changes -->

| 2026-09-06 | evidence-preprocessing | `witness_read_over_write` + `recheck` step 2: the array-elim certificate stops re-deriving its replacement half; mutation kills exactly one test |
| 2026-09-06 | evidence-preprocessing | ADR-1721: three obligations chosen by the direction a step can break; a re-derivation is not a discharge |
| 2026-09-06 | evidence-preprocessing | ADR-1704 gains a Prior art section: eDRAT (FMCAD 2024) cited, five differences recorded, and the RAT/core-pruning pairing named as a constraint |
