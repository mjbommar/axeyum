# The A/B: one binary, three environments, five divisions

## Protocol

One binary (`smtcomp_cli-lever`, built from an EMPTY target dir by `build.sh`,
which refuses unless the binary is newer than every `crates/**/*.rs`), three
environments:

- **base** — `env -u AXEYUM_QUANT_VALID_UNIVERSAL_RESERVE`, literally an
  environment with no lever in it. Under the lever's *original* default this was
  the historical `WholeBudget` code, which is what every number below is
  measured against.
- **ceiling** — `=1`: the pass gets `MIN_LADDER_SLICE` (1 ms) and the ladder
  below gets essentially the whole clock. Strictly more than any real reserve
  can give, so this is a ONE-WAY sizing: a file the ceiling arm does not decide
  is out of reach of every reserve.
- **reserve4** — `=4`: the pass gets 18 s of a 24 s budget, the ladder keeps 6 s.
  **This is the value that ships.**

That the arms come out of ONE binary is the point: an A/B over two builds cannot
tell a lever's effect from anything else that changed. The negative control on
the binary itself is that `strings` finds `AXEYUM_QUANT_VALID_UNIVERSAL_RESERVE`
twice in `smtcomp_cli-lever` and **zero** times in `smtcomp_cli-base`, the
pre-lever binary the census ran on.

The two arms of each pair run **back to back on the SAME file on the SAME pinned
physical core**, with the arm that goes first **alternating per file**, so
ambient load — which has moved 23 verdicts in one division at fixed code on
these boxes — cancels in the DIFFERENCE rather than landing on whichever arm ran
second. The `first=base` / `first=arm` halves are printed separately so a reader
can see the order did not matter rather than taking the protocol's word for it.

Envelope: **24 s wall, 8 GiB `ulimit -v`, one pinned physical core** on
`s5`/`s6`/`s7` — the same envelope as the pinned boards and this lane's census.
The **full pinned 200** per division, not the winnable subset, so a LOSS outside
the winnable set is visible.

Runner `ab-run.sh`, placement `launch-ab.sh`, scoring `ab-summarize.py` (which
prints FLIPS first and exits non-zero on one). Every table below re-derives from
the committed `ab/ceiling/*.tsv` and `ab/reserve4/*.tsv`.

## The noise floor, measured on this lane's own arms

**Before believing an effect, measure the band.** ADR-1970 declined to ship on
exactly this check: its base arm read 73 in the A/B and 76 in the census sweep
at the same commit, a 3-file band around a +2 effect.

Here the base arm and the single-arm census sweep are independent runs of the
same code at the same commit on the same boxes:

| division | census sweep | ceiling A/B base | reserve4 A/B base | band |
|---|---:|---:|---:|---:|
| UFDTNIRA | 74 / 200 | 74 / 200 | 73 / 200 | **1** |
| UFDTLIRA | 105 / 200 | 105 / 200 | 105 / 200 | **0** |
| UFDT | 31 / 200 | 31 / 200 | 31 / 200 | **0** |
| AUFDTLIRA | 96 / 200 | 96 / 200 | 96 / 200 | **0** |

**Three independent runs of the base arm over 800 files disagree on exactly one
file**, and that file is named:
`R509-011__higher_order_proof__why_cff6fc_…` decides `unsat` in 2,714 ms on the
quiet run and times out at 24,132 ms on the run that overlapped twelve other
shards. It is an ambient-load flip on a file that decides near the budget, not
a lever effect. **A band of 0–1 files against a +19 effect.**

## The ceiling arm — the sizing

| division | base | arm | GAIN | LOSS | sat↔unsat flips |
|---|---:|---:|---:|---:|---:|
| **UFDTNIRA** | 74 / 200 | **93 / 200** | **+19** | **0** | **0** |
| UFDTLIRA | 105 / 200 | 105 / 200 | 0 | 0 | 0 |
| UFDT | 31 / 200 | 31 / 200 | 0 | 0 | 0 |
| AUFDTLIRA | 96 / 200 | 96 / 200 | 0 | 0 | 0 |
| **UF (control)** | 90 / 200 | 88 / 200 | 0 | **2** | 0 |

`UF` is the control: an established quantified division, already on the parity
board, where this lane expected the lever to cost nothing. **It costs two
files**, and both are reproducible — see the re-check below. That is the finding
that decided the shipped value, and it is the same shape ADR-1970's `UFLIA`
control found.

## The shipped arm — `share = 4`

| division | base | arm | GAIN | LOSS | sat↔unsat flips |
|---|---:|---:|---:|---:|---:|
| **UFDTNIRA** | 73 / 200 | **92 / 200** | **+19** | **0** | **0** |
| UFDTLIRA | 105 / 200 | 105 / 200 | 0 | 0 | 0 |
| UFDT | 31 / 200 | 31 / 200 | 0 | 0 | 0 |
| AUFDTLIRA | 96 / 200 | 96 / 200 | 0 | 0 | 0 |
| **UF (control)** | 90 / 200 | 90 / 200 | 0 | **0** | 0 |

**The two arms gain the IDENTICAL set of 19 files** — checked as a set, not as a
count — so the gain is not an artefact of an extreme setting. And the control
separates them: the ceiling loses 2 files on `UF`, `share = 4` loses none.

**The ceiling arm was the right sizing instrument and the wrong thing to ship.**
A one-way ceiling answers "is anything reachable?", which was the question; it
does not answer "what should the constant be", which the control does.

**0 sat↔unsat flips in 4,000 solves** across both arms and all five divisions.

## The re-check of every moved row

Every row either A/B moved is re-run **three times per arm** at the board budget
on one pinned core, and against z3 4.13.3 (`z3 -T:24`, SECONDS) and cvc5 1.3.4
(`cvc5 --tlimit 24000`, MILLISECONDS — the units differ and mixing them silently
corrupts a board). `confirm-moved.sh` measures; `confirm-summarize.py`
classifies and carries the finding-dependent exit status.

    rows re-checked: 21   GAIN 19   LOSS 2   UNSTABLE 0   CONTRADICTED 0
    NO INDEPENDENT CHECK AT ANY BUDGET (ADR-1957): 0 of 21

    the 19 gains:  vs :status 18/18   vs z3 18/18   vs cvc5 19/19   DISAGREEMENTS 0

**55 independent comparisons behind the 19, 0 disagreements, and 0 rows with no
opportunity for one** — the zero is not vacuous. Every one of the 19 reads
`base=[unknown,unknown,unknown] arm=[unsat,unsat,unsat]`: not one is the
~1–1.5 % of files that flip on ambient load at a 24 s budget.

**The two `UF` losses are equally stable** — `base=[unsat,unsat,unsat]
arm=[unknown,unknown,unknown]`, both with independent agreement that `unsat` is
the right answer. They are reported as a real cost of the ceiling arm, not
explained away, and they are the reason `share = 1` does not ship.

## The shape of the gain

Under the ceiling arm 16 of the 19 are decided in **106–109 ms**; the slowest is
2,409 ms. Under `share = 4` the same 19 land at **18,116–19,023 ms** — the pass
spends its 18 s slice first and the ladder's 6 s reserve then refutes in about a
tenth of a second.

Every one of them is a file on which the base arm spends the full 24,000 ms
inside valid-universal elimination and then declines.

**The pass was spending twenty-four seconds to prevent a hundred-millisecond
refutation.**
