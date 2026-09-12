# The four datatype divisions — what actually blocks them

**2026-09-12.** 160 files: 40 from each of `UFDT`, `UFDTLIRA`, `AUFDTLIRA`,
`UFDTNIRA`, sampled at a fixed stride **through** each division rather than as a
path-sorted prefix. Budget 3 s, `--trace`, one core, competition CLI at
`dcbfc6292`. Raw rows in `census.tsv`.

## This corrects `coverage/blockmap.txt`

That file sampled **3 files per division** and attributed all four divisions —
27,785 files — to `term error: sort mismatch: expected Bool, BitVec`.

**That error does not appear once in 160 files.** It is not the blocker for any
of these divisions. Read the table below instead; the blockmap row is wrong and
should not be quoted.

## What we already decide

| division | sampled | unsat | unknown |
|---|---:|---:|---:|
| UFDTLIRA | 40 | **19** | 21 |
| UFDTNIRA | 40 | 5 | 35 |
| UFDT | 40 | 1 | 39 |
| AUFDTLIRA | 40 | 0 | 40 |

`UFDTLIRA` is not blocked — it is **unmeasured**. It decides just under half of a
spread sample with no code change at all.

## What blocks the rest

Term ids normalized (`term #N`, `(Uninterpreted K)`); these differ per file and
are one blocker, not twenty-eight.

| blocker | files | share |
|---|---:|---:|
| eager Ackermann elimination does not admit array-valued … | 33 | 21% |
| `term #N has sort (Uninterpreted K)` — uninterpreted sort, pure-Rust backend | 28 | 18% |
| an uninterpreted function applied to a datatype argument | 26 | 16% |
| `is`/`select` over a non-variable datatype term | 13 | 8% |
| native datatype solving supports scalar (Bool/BitVec/Int) only | 10 | 6% |
| quantified budget exhausted after valid-universal elimination | 10 | 6% |
| quantified budget exhausted after e-matching | 8 | 5% |
| a datatype-sorted term survives tag/field expansion | 2 | 1% |
| nested array element sort | 2 | 1% |

**Four blockers are 62% of the sample.** All four are capability gaps in the
datatype / UF / array backend, not timeouts — the quantified-budget rows are the
only clock-bound ones and they are 11% together.

Note the third row is the residue of ADR-1920, whose title says the capability
gate *moves downstream* rather than disappears: the arena now admits
datatype-sorted UF signatures and a backend still refuses them.

## Caveats

- **40 files is a sample of divisions averaging 6,946 here.** Shares carry a
  real error bar; the ordering of the top four is what this supports, not the
  percentages to the point.
- A 3 s budget inflates the two quantified-budget rows relative to a 24 s
  competition run. They are a ceiling, not a floor — every other row is a
  capability refusal that no budget changes.
