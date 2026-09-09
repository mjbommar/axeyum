# `euf-online` arithmetic-atom policy A/B, 2026-09-08

Data for the `euf-online-admission` lane. The writeup — what was measured, why,
and what it decides — is
[`docs/research/12-performance/euf-online-arith-atoms-2026-09-08.md`](../../docs/research/12-performance/euf-online-arith-atoms-2026-09-08.md).
Read that first; this directory is data, not narrative.

## The question

`euf-online` decides five `QF_UFLIA` files `unsat` in 2–13 ms when run alone and
the front door loses them at 24 s and at 120 s. The route is reached; it declines
in 1.3 ms with *"boolean skeleton outside the online CDCL(T) encoder"*, because
`check_auto_dispatch`'s own `lift_arith_ite` moves an arithmetic comparison to
Boolean position where the skeleton encoder has no arm for it.

The fix abstracts such a subterm to an opaque skeleton variable. **That is sound
in one direction only** (`unsat` transfers; `sat` is replay-gated), and it turns a
1 ms decline into a route that spends time. So the question this data answers is
not "does it fix the five" but **what it does to the whole division**.

## Contents

- `QF_UFLIA.<arm>.tsv` — one row per file. `arm` is the
  `AXEYUM_EUF_ONLINE_ATOMS` value: `refuse` (the pre-2026-09-08 behaviour),
  `sliced` (the shipped default), `whole` (abstraction with no budget slice).
  Columns: `file`, `verdict`, `wall_ms`, `euf_online_outcome`, `euf_online_ms`,
  `decided_by`, `bound_by`, `atoms_line`.
- `compare.txt` — `scripts/euf-online-atoms-compare.py` over the three.
- `QF_UF.refuse.tsv` / `QF_UF.sliced2.tsv` — the neighbour division, both arms on
  the SAME host and cores. `compare-QF_UF.txt`.
- `QF_UF.sliced.tsv` — **a confounded first run, kept deliberately.**
  `compare-QF_UF-confounded.txt`.

## Result

| arm | decided / 200 | vs `refuse` |
|---|---:|---|
| `refuse` | **151** | baseline |
| `sliced` (shipped) | **156** | **+5 / −0** |
| `whole` | **156** | +5 / −0 |

The five gained are `medium9`, `medium10`, `medium13`, `medium16`, `medium19`
(`mathsat/EufLaArithmetic/medium/`), each `unsat`, each `decided_by=euf-online`,
the route itself costing 2–9 ms. **No file was lost, and no two arms disagree on
any verdict** (`euf-online-atoms-compare.py` exits 2 on a disagreement and 1 on a
loss; it exited 0).

`sliced` and `whole` decide the same set, so the budget slice costs nothing on
this population — which is the finding that lets it ship as the default rather
than as the arm that has to be justified.

## The neighbour division, and a −3 that was the host

`QF_UF` is the division this route owns. First run: `refuse` 195/200 (s7, cores
0–7), `sliced` **192**/200 (s5, cores 8–15, beside another sweep on cores 0–7).

The three files (`gensys_brn838`, `gensys_icl591`, `iso_brn_nogen005`) are ones
`euf-online` decides at ~21.2 s of a 24 s budget, so a busier host loses them.
**The counter settles it rather than an argument**: on all 198 `QF_UF` queries the
route was entered on, `abstracted_queries=0` — nothing was abstracted, so
`route_timeout` returned the caller's timeout unchanged and the two arms executed
identical code.

Re-run of `sliced` on the SAME host and cores as the baseline: **195/200,
+0 / −0** (`compare-QF_UF.txt`, exit 0).

The confounded run is committed as `QF_UF.sliced.tsv` and labelled here rather
than deleted: a measurement that moved for a reason other than the change is
worth more in the record than out of it, and this one is the reason the matched
re-run exists.

### What the abstraction costs

The route abstracted on **68 of 200** files. Of those it decided 6 (1–9 ms) and
declined 62 after a median of 8 ms and a maximum of **1,159 ms**. Under `refuse`
the same 68 declined after at most 6 ms. So the change buys 5 files and spends up
to ~1.2 s on the worst single file, out of a budget the routes below it did not
need on any file here.

## Three things to know before quoting a number from here

1. **`unsolved` is the denominator rule, not a category.** Timeout, `unknown`,
   crash, OOM and parse failure all count as not solved, exactly as
   `scripts/parity-run.sh` fixes it.

2. **Neither new bound actually fired.** `min(remaining/4, 2 s)` yields 1.5 s at
   the 24 s budget and the largest observed spend was 1,159 ms. The bounds are
   insurance against a query outside this population; nothing here measured them.

3. **The hosts were not idle and these are not timing numbers.** `s4` carried 14
   other `smtcomp_cli` processes from sibling lanes at load 13–17 of 16 cores
   throughout. The arms ran on `s5` (`whole`), `s6` (`refuse`) and `s7`
   (`sliced`), load 3–4 of 16 at launch, `taskset -c 0-7`, 6 slots, 24 s wall,
   8 GiB `ulimit -v`. The **decide / not-decide bit** is what the conclusions rest
   on; every millisecond figure is advisory. In particular the five gained files
   land at ~18.3 s of wall, and that is `uf-arith-lazy-overbound` spending
   `24000 × 3/4` before the ladder below it runs — a separate budget question
   with its own policy, not this change.

## Reproducing

```sh
cargo build --release -p axeyum-bench --example smtcomp_cli   # no --features full
scripts/euf-online-atoms-sweep.sh refuse \
  bench-results/parity-lists/QF_UFLIA.txt \
  target/release/examples/smtcomp_cli /tmp/QF_UFLIA.refuse.tsv 6 24
scripts/euf-online-atoms-sweep.sh sliced …
scripts/euf-online-atoms-compare.py /tmp/QF_UFLIA.refuse.tsv /tmp/QF_UFLIA.sliced.tsv
```

Measured with the binary built at lane commit `a962cb307`; the `refused` counter
landed one commit later (`91389a959`) and changes no verdict — it lives inside the
stats guard — so every verdict here is current while the `atoms_line` column is
the pre-`refused=` format.

**That older format is itself visible in the data, and it is the finding the
counter fix came from.** `QF_UFLIA.refuse.tsv` has `atoms_line` EMPTY on all 200
rows, including the 68 files where the route was entered and gave up, because the
first version of the instrument recorded only after the encoding *finished* — so
the arm it exists to expose published nothing. `QF_UFLIA.sliced.tsv` carries
`abstracted_queries=1` on 49 rows. Re-running these sweeps with a binary at
`91389a959` or later fills the refuse column in with `refused=1`.
