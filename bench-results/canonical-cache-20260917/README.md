# ADR-2144: the canonical constraint cache on `QF_BV` (one binary, two env values)

The regression control behind
[ADR-2144](../../docs/research/09-decisions/adr-2144-the-canonical-constraint-cache-is-a-library-feature-of-the-warm-engine.md):
`AXEYUM_CANONICAL_CACHE=on` against the shipped default (off) on the 200-file
`QF_BV` pinned list, one-shot files, so the ADR can say the lever changes no
verdict and costs nothing where there is nothing to reuse. The measurement of
what the cache DOES is the replayed DptfDevGen session in the ADR, not this.

- **Arms.** A = the variable unset (cache off, the shipped default); B =
  `AXEYUM_CANONICAL_CACHE=on`. One binary,
  `target/release/examples/smtcomp_cli` built on s7 from this lane's tree
  (`c1d88769b`), hash `840e29c9…` in `half*.log`.
- **List.** [`../parity-lists/QF_BV.txt`](../parity-lists/QF_BV.txt), two
  halves of 100 files run concurrently on s7, pinned to core pairs `1,9` and
  `3,11`.
- **Envelope.** 24 s wall, 8 GiB `ulimit -v`, arms interleaved per file and
  alternating in order (`ab-env.sh`, ADR-2140's script with the variable
  renamed; `$EPOCHREALTIME` timing with the 200 ms sleep self-check, which
  read 205 / 203 ms).
- **Summary.** `summarize.py half1.tsv half2.tsv > summary.md`; its exit
  status is 1 on any `:status` disagreement and 2 on a timing-unit failure.

| measure | A = cache off | B = cache on |
| --- | ---: | ---: |
| decided | 187 | 187 |
| sat / unsat | 58 / 129 | 58 / 129 |
| PAR-2 (ms, 24 s) | 3852 | 3851 |
| wall, 187 both-decided files (ms) | 146 317 | 146 201 |
| other arm >10 % + 50 ms slower | B slower on 1 | A slower on 1 |

Gains 0, losses 0, flips 0, `:status` disagreements 0, nonzero exit rows 0,
timing-unit failures 0. The one-shot front door never reaches the warm
engine on these files, so the lever is inert here by construction; the table
is the evidence that it is inert, not a speed claim.
