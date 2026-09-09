# UF — what actually stops the 32 files we lose (2026-09-09)

`UF` is the only **quantified** division on the parity board and the only one
that did not move on 2026-09-08: 32 losses before the re-cut, 32 after, while
the whole loss population fell 480 → 318. Every other division examined that
day was quantifier-free and every finding came from the quantifier-free
dispatch ladder, so nothing that moved them could have moved this.

This note is the attribution. It answers one question — *what returns first* —
and it answers it with the branch that returns, not the string that gets
printed.

## Population and protocol

- **Population**: `bench-results/parity-losses-20260908/UF.txt`, all 32 files.
  30 declare `:status unsat`, 2 declare `unknown`.
- **Protocol**: byte-identical to the SCORED path of `scripts/parity-run.sh` —
  `MEM_LIMIT_GB=8 timeout 29 scripts/mem-run.sh smtcomp_cli <file>
  --timeout-ms 24000` — plus `--trace`, `AXEYUM_QTRACE=1`, `AXEYUM_QPROBE=1`,
  which change no verdict and add only stderr/`;` lines.
- **Host**: s4, 16 cores, `taskset -c 0-7` (P-cores). **Not idle**: load average
  ran 0.6 → 11 across the sweep, with another lane's `QF_NRA` `--trace` sweep
  and this lane's own builds on the box throughout. Wall times below are upper
  bounds; the bucket a file lands in is not load-sensitive except at the
  23–24 s boundary, and the four files there are called out.
- **Denominator**: the ledger's last `UF` entry (`bench-results/PARITY.md`,
  2026-09-06) is **85/200 for axeyum, 93/200 for cvc5 — a 91.4 % ratio, the
  highest of the twelve divisions**. `both / axeyum-only / reference-only` is
  `61 / 24 / 32`, and those 32 are exactly this list. The re-cut's complement
  pass measures us at 84/200 today (the "+1" the re-cut README records), and
  the reason it emitted **no** regression-candidate list for `UF` is that its
  superset is 1 real file in 84. **The effective population for this lane is
  32 files and nothing else.**

## The split

| bucket | files | what it means |
|---|---:|---|
| (a) declines before trying | **0** | no admission refusal anywhere in the division |
| (b) tries and times out | **13** | ≥ 24 s wall, or a watchdog kill |
| (c) memory bound | **3** | `SIGABRT` under the 8 GiB `ulimit -v` |
| (d) `unknown` with budget left | **16** | the ladder ran out of rungs before it ran out of clock |

The dominant bucket is **(d)**, which is not the shape any other division
showed. `QF_UFLIA` was 40-of-44 admission refusals in fractions of a
millisecond; `QF_LRA` was 97 % of the budget in a 0 %-success method. Here
**19 of 32 files return before the budget expires**, and across the whole
population we spend **615 s of the 768 s available (80 %)**. The median unspent
remainder on those 19 files is **7.8 s of 24 s**; the largest is 17.1 s.

There is no rung after the last one. `finish_quantified_solve` is a fixed
sequence — witness search, finite expansion, the UF finite-model probe, the
first-refusal MBQI rung, the e-graph fallback, full MBQI, the full UF finite
model finder — and when the last of them declines, the remaining wall clock is
discarded.

## Where each file stops

Read from `AXEYUM_QPROBE`'s `egraph-fixpoint round=… ground=…`, which fires
when an instantiation round admits nothing new:

| stop | files |
|---|---:|
| fixpoint at **exactly `ground=8192`** — the accumulated-ground ceiling | **24** |
| genuine fixpoint **below** the ceiling (`ground` = 273, 424, 656, 4158) | 4 |
| 8 GiB abort before or at a fixpoint | 3 |
| loop entered, no fixpoint reported | 1 |

`8192` is `qinst_egraph::MAX_GROUND_TERMS`. Until this note it was a bare
`usize` with `env_override: None` and an undated `doc comment` justification in
the configuration registry — the operative stop for a whole division, with no
way to ask what a different value would do short of editing the source.

## The printed reason is not the operative one

**Measured on the binary as it stood before this note's fix** (solver commit
`0c8afe970`), 21 of the 32 files print

```
; give-up kind=Incomplete detail=query has quantifiers instantiation does not
  reach (nested, existential, or non-top-level)
```

which is a claim about the query's **shape**. It is wrong on all 21.
`AXEYUM_QPROBE` reports **zero `skolem-bail` events across all 32 files**: the
polarity-aware NNF + Skolemization + prenexing pass (`quant_skolemize`) reached
every quantifier in every file, and its documented give-up case — a quantifier
under a non-Bool mixing position — never fired once. The residual-shape message
came from `decide_instantiation`, which runs *after* the e-matching loop has
already declined, and it overwrote the loop's own reason.

That is now fixed: `prove_unsat_by_ematching` carries the loop's
`UnknownReason` past `decide_instantiation`. The shape message is kept for the
case where the loop never ran (no remaining budget, no residual quantifier to
hand it) — there the shape genuinely is the reason.

This mattered practically. A reader of the old message would have gone looking
at the skolemizer, which is the one part of this pipeline that is working
perfectly on this population.

## Would a bigger ceiling help? No — and the census says why

`AXEYUM_FLOODPROBE=1` prints a census of the admitted instance pool at each of
the loop's two exits. A second sweep of all 32 files at the same protocol
(2026-09-09, s4, `taskset -c 0-7`, contended by this lane's own full clippy
rebuild — so it is a lower bound on how far each file got) produced a census on
30 of them.

**Read the exit first.** Every one of the 30 censuses came from the
**fixpoint** exit; the `ground.len() > ceiling` cap-hit branch — the one that
returns `egraph_ground_limit()`'s "ground-term count budget exhausted" —
**fired zero times on this population**. The ceiling does its work one step
earlier: admission is gated `ground.len() < ceiling`, so at exactly 8192
nothing can be admitted, the round admits nothing, and the loop takes the
fixpoint break. This matters for anyone grepping for the ceiling's own message:
these files never print it.

That splits the 30 cleanly:

| exit | files | what is in the pool |
|---|---:|---|
| fixpoint **at** `ground = 8192` — the ceiling starved admission | **25** | 200,781 instances |
| fixpoint **below** the ceiling — nothing left to match | **5** | 5,496 instances |

| clause value of the admitted instances | ceiling-starved (25 files) | term-starved (5 files) |
|---|---:|---:|
| **FALSE** — a conflict, the thing a refutation is made of | **0** (0.000 %) | **0** (0.000 %) |
| **UNIT** — propagates something new | 599 (0.298 %) | **0** (0.000 %) |
| TRUE — already implied by the current congruence | 135,637 (67.6 %) | 3,743 (68.1 %) |
| UNDETERMINED | 64,545 (32.1 %) | 1,753 (31.9 %) |
| generation ≥ 2 (derived from derived) | 166,196 (82.8 %) | 3,143 (57.2 %) |

**`clause_false = 0` on every single one of the 30 files**, in both classes —
that is the per-file claim, and it is the load-bearing one. Units appear on 6
of the 25 ceiling-starved files and on none of the term-starved five. The
percentages are pooled and are context.

So the loop fills its ceiling with two hundred thousand instances of which
**not one** is a conflict, two thirds are already true, and four fifths are
derived from other derived terms. A larger ceiling holds more of the same
distribution. The ceiling is the *operative* stop and simultaneously the
*wrong lever*, and both halves have to be said together: reporting only the
first invites the next lane to raise it.

## What an independent solver does with the same 32

Quantified `UF` was assumed to have no cheap oracle here, because the committed
differential fuzzes are quantifier-free. It does: **z3 4.13.3 is installed on
s4 and handles quantified UF**, so it can be run directly on these files at the
same protocol. (The loss list itself is scored against **cvc5**, which decides
all 32 — z3 is a second, independent reading, not the reference.)

| z3 4.13.3, 24 s / 8 GiB | files |
|---|---:|
| `unsat` | **18** |
| timeout | 11 |
| 8 GiB abort | 3 |

Every one of the 18 agrees with the file's declared `:status unsat` — **zero
disagreements**. And the wall times are the finding:

```
decided wall ms: 107 107 108 108 108 109 114 114 116 116
                 116 118 118 122 123 125 126 215
```

**Median 116 ms. Maximum 215 ms.** We spend up to 24 s and return `unknown` on
eighteen files an independent solver closes in about a tenth of a second, and
four of those are in the *starved* class where our loop saturates at 273–656
ground terms and simply has nothing left to match.

This is the number that settles the diagnosis. A problem another e-matching
solver refutes in 116 ms is not a problem about budget, ceilings, or memory. It
is a problem about **which instances get made**.

## The conclusion, stated plainly

**This division needs a capability we do not have: relevance-driven instance
selection.** Every piece of machinery around it is present and working — a
congruence-closure e-graph with e-matching, multi-pattern joins, an
incremental matcher, generation-ordered admission, term invention, a
nesting-preserving quantifier layout, certificate-checked instances. What is
missing is the part that decides *which* of the available instantiations is
worth making: trigger selection and scoring, an instance queue with a real cost
function, and instantiation-round restarts that discard a pool this census
shows to be inert. cvc5's and z3's answers here come from a handful of
instantiations, not from eight thousand.

Concretely, the next lane's targets, in the order the measurements support:

1. **Instance relevance.** The census is the specification: admit instances
   that are `FALSE` or `UNIT`, and stop admitting `TRUE` ones. Today the loop
   admits `TRUE` clauses at 81.6 % of its ceiling.
2. **Restart with a pruned pool.** Reaching the ceiling currently ends the
   loop; on 19 of 32 files there is 7.8 s (median) of clock left at that point.
   A restart that keeps generation ≤ 1 and re-matches would spend it.
3. **Trigger selection.** 19 of the 32 files carry **no** `:pattern`
   annotation at all (the whole `sledgehammer` and `grasshopper` families), so
   every trigger is ours to choose. The starved class — fixpoint at
   `ground = 273` while z3 refutes in 122 ms — is a trigger-selection failure
   with nothing else in it.

None of the three is a tuning change, which is why this note does not report a
tuning result.

## What this note does NOT establish

- **It is not a parity re-measurement.** No reference was re-run against the
  200-file `UF` list; `bench-results/PARITY.md` remains the ledger. The z3 pass
  above is 32 files, one solver, one host, and z3 is not the division's
  reference.
- **The wall times are contended.** See the host note under Protocol. Four
  files sit within a second of the budget boundary
  (`x2015…2416479` at 23.5 s, `uf.573210` at 24.2 s, `dl_copy_invariant_19_2`
  at 24.4 s, `smtlib.1098821` at 24.3 s) and could move between bucket (b) and
  bucket (d) on an idle box. Nothing in the argument depends on which side they
  land: the *stop mechanism* is read from `QPROBE`, not from the clock.
- **The census covers the 30 files that printed one**, not all 32, and it was
  taken on a contended box (a full clippy rebuild of this worktree ran
  alongside it), so how far each file got is a lower bound. The load-bearing
  claim is per file — `clause_false = 0` on all 30 — and the percentages are
  pooled context. `clause_unit = 0` is NOT universal: units appear on 6 of the
  25 ceiling-starved files, and an earlier draft of this note said otherwise
  before the full sweep finished.

## Reproducing it

```sh
cargo build --release -p axeyum-bench --example smtcomp_cli

# the split (bucket + stop mechanism), one file:
MEM_LIMIT_GB=8 timeout 29 env AXEYUM_QTRACE=1 AXEYUM_QPROBE=1 \
  scripts/mem-run.sh target/release/examples/smtcomp_cli <file> \
  --timeout-ms 24000 --trace

# the cap census (why a bigger ceiling does not help):
MEM_LIMIT_GB=8 timeout 29 env AXEYUM_FLOODPROBE=1 \
  scripts/mem-run.sh target/release/examples/smtcomp_cli <file> --timeout-ms 24000

# the ceiling is now A/B-able without a patch:
AXEYUM_QINST_GROUND=32768 target/release/examples/smtcomp_cli <file> --timeout-ms 24000
```

`AXEYUM_QINST_GROUND` selects a `qinst_egraph::GroundBudget` arm; an unset,
unparseable or zero value is `GroundBudget::SHIPPED`, so a typo degrades to the
shipped behaviour and `=0` cannot disable the "never hang" ceiling.

## Registry consequences

- `qinst_egraph.rs::MAX_GROUND_TERMS` moves from `undated("doc comment")` to a
  dated justification pointing at this note, with `env_override:
  Some("AXEYUM_QINST_GROUND")`.
- `qinst_egraph.rs::ONLINE_QUANTIFIER_LIMITS` was **unregistered** — the only
  one of the file's 31 constants that was, and not by oversight: it is
  **struct-valued** (`OnlineQuantifierLimits`), and `config_registry`'s
  coverage scanner matches only scalar and `Duration` types, so
  `every_governing_constant_is_registered` could not have named it even had
  `qinst_egraph.rs` been in `GOVERNED_FILES`. The entry is added here; the
  scanner blind spot is a separate finding and is not closed by it. Any
  struct-valued constant anywhere in a governed file is invisible to that gate
  today.
