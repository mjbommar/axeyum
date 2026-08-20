# Lane: string-cert — the string family's UNSATs carry no artifact

<!-- plan-section: lane-status -->

**Three of the 26 uncertified string UNSATs now carry a re-derivable
certificate; the other 23 need regex/`replace`/`contains` reasoning, not
lengths** (`WIP`, string-cert, 2026-08-20).

The refreshed dominance audits
(`bench-results/dominance/qf-{s,slia,seq}-cvc5-regress-clean-dominance-audit.json`)
list 26 rows at `evidence_kind = bare-unsat`, every one decided by
`smtlib-string-front-door` with `certified=false checked=false`. A length /
code-point abstraction plus a Farkas-style linear refutation closes the three
that are arithmetic once the strings are abstracted away (`str004`, `str005`,
`str-code-unsat-2`). The remaining 23 are regex membership, `str.replace`,
`str.contains`, lexicographic order, `seq.nth` congruence, and one pigeonhole
over `str.to_code` — none of them a length argument, and none of them silently
approximated.

Next: the `str.to_code` **injectivity** lemma
(`code(y) = code(z) ∧ code(y) ≥ 0 → y = z`) would take
`r1_QF_SLIA_str-code-unsat`, whose refutation is linear right up to the final
`distinct`; its sibling `-3` additionally needs pigeonhole over seven pinned
code points and is a different argument.

<!-- plan-section: landed-changes -->

| 2026-08-20 | (pending) | The string family's first re-derivable UNSAT artifact beyond word-clash/regex-emptiness: `Evidence::UnsatStringLength` abstracts every string term to an integer length keyed on its SOURCE NAME, names the five theory lemmas the argument uses, and closes with one nonnegative combination per case-split branch. The checker is two stages — bind each lemma to the conjunct that licenses it, then re-derive the arithmetic — and is arena-free, because a string script's flat view is the bounded packed-BV encoding rather than the query. 23 guards mutation-checked; two killed nothing and were fixed rather than kept (one was dead code the command allow-list already covered, one had no multi-`check-sat` fixture). Also: `diagnose_evidence` reported the ARENA front door for string files, i.e. a query nobody solves — it now reports the text front door too, and agreed with the dominance audit for the first time. |
