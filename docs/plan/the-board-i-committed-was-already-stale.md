# The board I committed was already stale when I committed it

Recorded 2026-09-09. Three hours after I appended three parity rows and reported
"+17 files, zero disagreements", a re-cut lane showed the picture was
substantially better than the ledger said and that the ledger cannot show it.

## The loss population was 33% wrong

| division | was (2026-09-05) | now | recovered |
|---|---:|---:|---:|
| QF_RDL | 47 | **9** | 38 |
| QF_IDL | 54 | **19** | 35 |
| QF_UFLIA | 58 | **23** | 35 |
| QF_UF | 38 | **6** | 30 |
| QF_ABV | 19 | **12** | 7 |
| QF_LRA | 54 | **49** | 5 |
| QF_LIA | 27 | **22** | 3 |
| QF_NIA | 61 | **58** | 3 |
| QF_NRA | 77 | **75** | 1 |
| QF_BV / QF_SLIA / UF | 6 / 7 / 32 | unchanged | 0 |
| **total** | **480** | **318** | **157** |

Three divisions carry 103 of the 157. **A QF_RDL brief was aimed at a list five
times longer than the truth**, and several of mine were aimed at files we had
already won.

## The ledger is stale too, and a date cannot show it

`PARITY.md`'s newest entry for any division sits **72 `crates/` commits behind
HEAD**. Worse, its QF_UFLIA row — the one I committed, timestamped
`2026-09-08T20:27` — records **129/200**, measured at `f24c61f91`, which is
**not an ancestor of** `26d9d80e3`, the interface-caps fix another lane measured
at **151/200 on the same list the same day**.

**Two entries, one division, one day, 22 files apart**, and nothing in either
row says which tree it describes relative to the other. A timestamp orders them;
it does not tell you that one predates a fix the other contains.

So the "+17, zero disagreements" I reported was true of the commit it measured
and already understated by the time I wrote it.

## Four divisions decide FEWER files than their ledger row implies

Each survived a second pass: **QF_UF +3, QF_BV +2, QF_LIA +1, UF +1**. One
QF_UF file is named exactly
(`QG-classification/qg7/iso_brn_repgen041.smt2`). For QF_LIA (1 in 60) and UF
(1 in 84) the lane emitted **no candidate list at all**, on the grounds that a
file that is 98% `neither` is a worse artifact than none — which is the right
call and the opposite of the one that produces a confident wrong list.

These are the rows to check before quoting any division as improved.

## What now stops this recurring

`scripts/check-loss-list-freshness.py`, registered in `check.sh` and the
justfile. Its authority is **per division, not per directory** — the first
version was per-set and was wrong on its first real run, because
`parity-losses-20260906` is a QF_NRA-only *addition*, not a replacement.

It fails on an unmarked superseded set, a `SUPERSEDED-BY:` naming nothing or
itself, a division past 14 days, an incomplete manifest, and an empty scan.
`behind=` is printed and never fatal — the 2026-09-05 set reads **606**.

12 guard mutations, all 12 killed, and the table was **recorded rather than
predicted**: two predictions were wrong, and it then *changed when the re-cut
landed*, which is kept rather than tidied because that sensitivity is a property
of the tree, not of the checker.

## The rule

**A measurement's commit matters more than its timestamp.** Every board row
already carries a solver commit; nothing yet checks whether a newer row's commit
is an ancestor or a descendant of an older one's. Two rows a day apart can
describe trees that differ by a fix worth 22 files, and the dates will not say
so.
