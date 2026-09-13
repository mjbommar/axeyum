# ADR-1980 — the A/B

Lane `DT-EXACTNESS`, 2026-09-13. Binary `smtcomp_cli-ab`, built from
`e5f6764ba` in an EMPTY target dir, freshness-checked before a single file was
run:

    CARGO-EXIT=0
    FRESH ab: no crates/**/*.rs is newer than …/release/examples/smtcomp_cli
    BUILD-OK ab e5f6764baa0ab205f84428e544199020fc5c5fdf

**One binary, two arms, and the polarity is inverted relative to every other
runner in this repository.** ADR-1970's and ADR-1975's levers ship OFF, so their
`base` arm is the unset environment. This one ships ON:

| arm | environment | what it is |
|---|---|---|
| `base` | `AXEYUM_DATATYPE_NATIVE_REFUSAL=propagate` | the pre-ADR-1980 code, byte-equivalent to the bare `?` |
| `arm` | *unset* (`env -u`) | the shipped default |

`ab-run.sh` hardcodes both and `launch-ab.sh` takes no arm value at all, so the
polarity cannot be got wrong from a command line.

Envelope, identical to the census and both pinned boards: 24 s wall, 8 GiB
`ulimit -v`, one pinned physical core, both arms **back to back on the same file
on the same core**, arm order alternating per file.

## The probe, before the measurement

`probe.sh` refuses to pass unless the two arms actually DIFFER on at least one
file. A lever that is not reaching the binary and a change that is worth nothing
produce the identical zero, and nothing else in the protocol distinguishes them.

    PROBE seen=48 arms_differed_on=5
    PROBE-OK

## Results

| division | base | arm | net | gain | loss | sat↔unsat flips |
|---|---:|---:|---:|---:|---:|---:|
| UFDTLIRA | 105 | **143** | **+38** | 38 | 0 | 0 |
| UFDT | 31 | **50** | **+19** | 19 | 0 | 0 |
| AUFDTLIRA | 96 | **118** | **+22** | 24 | 2 | 0 |
| **total (3 divisions)** | **232** | **311** | **+79** | **81** | **2** | **0** |
| **UF** *(control)* | **90** | **90** | **0** | **0** | **0** | **0** |

**The control moved nothing at all** — not a gain, not a loss, not a flip, on
200 files. ADR-1966's `UFLIA` control lost one file reproducibly to the same
mechanism, so a zero here was not the expected outcome and is worth stating as a
measurement rather than an assumption. `UF` was chosen because it is a division
we already do well (90 of 200 on the `main` board) and because it is the
datatype divisions' quantifier-free-UF neighbour, so it exercises the same
ladder without the datatype branch. 4 files abort with rc 134 in BOTH arms; that
is pre-existing and identical either side.

Arm order was alternated per file. If it mattered the two halves would disagree;
printed so the reader can see it did not rather than taking the protocol's word:

| division | first=base (n) | base / arm | first=arm (n) | base / arm |
|---|---:|---|---:|---|
| UFDTLIRA | 104 | 55 / 72 | 96 | 50 / 71 |
| UFDT | 104 | 20 / 28 | 96 | 11 / 22 |
| AUFDTLIRA | 104 | 48 / 65 | 96 | 48 / 53 |
| UF *(control)* | 100 | 50 / 50 | 100 | 40 / 40 |

### The re-check: 3 runs per arm, on every MOVED row in either direction

ADR-1966 measured **11 of its 18 moved rows outside the target division as
ambient** — they vanished on re-check. So the first pass of a per-file A/B is,
historically, about 40 % noise on the rows nobody verified. All 83 movers here
were re-run three times per arm, and a row counts only if all three runs of an
arm agree with each other:

    83 movers: 81 STABLE-GAIN, 2 STABLE-LOSS, 0 UNSTABLE, 0 FLIP, 0 NO-MOVE

**Nothing vanished.** Net after re-check is unchanged at **+79**.

### The two losses, named

Both are the same SPARK higher-order-fold file pair in `AUFDTLIRA`, both
`unsat → unknown`, and **neither is in the targeted population**:

| file | base | arm | base_ms | arm_ms |
|---|---|---|---:|---:|
| `R509-011__higher_order_proof__why_b5aa01_…` | unsat | unknown | 808 | 6,314 |
| `R509-011__higher_order_proof__why_ec30e5_…` | unsat | unknown | 1,609 | 24,131 |

The mechanism is the cost below: the decline makes the ladder take a longer
path, and on these two that path runs out the clock. ADR-1966 saw exactly
−2 on this division too.

## The base arm reproduces `main`

The strongest available evidence that this is not a branch-only number:

| division | `main` (`bench-results/postmerge-board-20260913/`) | this A/B's BASE arm |
|---|---:|---:|
| UFDTLIRA | 105 | **105** |
| AUFDTLIRA | 96 | **96** |
| UF *(control)* | 90 | **90** |
| UFDT | 31 (ADR-1975's census; not on the post-merge board) | **31** |

Every base value lands on the published `main` number exactly. The branch
contains `main` at `c2fb0ade4` plus this lane's own commits and nothing else.

## Every gain is inside the population ADR-1975 sized

| division | gains | inside the 124 | outside | arg (1935) | result (1946) | non-atomic (1942) |
|---|---:|---:|---:|---:|---:|---:|
| UFDTLIRA | 38 | 38 | 0 | 25 | 7 | 6 |
| UFDT | 19 | 19 | 0 | 9 | 10 | 0 |
| AUFDTLIRA | 24 | 23 | 1 | 12 | 11 | 0 |
| **total** | **81** | **80** | **1** | **46** | **28** | **6** |

**80 of the 124 rows ADR-1975 sized converted — 65 %.** The one gain outside is
a different ADR-0022 refusal family that travels through the same site. All
three refusal messages are represented, so this is not one arm of the guard
doing all the work.

## What is left of the 124, and how it changed

| division | targeted | gained | left | left: arm_ms median |
|---|---:|---:|---:|---:|
| UFDTLIRA | 49 | 38 | 11 | 1,412 |
| UFDT | 36 | 19 | 17 | 3,013 |
| AUFDTLIRA | 39 | 23 | 16 | 17,423 |
| **total** | **124** | **80** | **44** | |

**ADR-1975's characterisation of these rows no longer holds for the 44 that
remain.** It measured them declining "with a median 23.9 s of 24 s UNSPENT — a
shape refusal, not a clock problem". After this change the remainder spend a
median of 1.4 s / 3.0 s / 17.4 s and up to the full 24 s. They have moved from
SHAPE-bound to genuinely searching and failing, which is a different and harder
target. A lane taking the recursive-expansion capability next should re-census
rather than inherit ADR-1975's decline-time figure.

## The cost, which lands on the rows that did NOT move

A decline makes the dispatcher run thirteen rungs it used to skip. On a query
none of them can decide, that work is spent for nothing:

| division | whole-division wall, base → arm | on the rows that did not move |
|---|---|---|
| UFDTLIRA | 209 s → 301 s (**+92 s**) | +89 s over 162 rows (**+0.55 s/row**) |
| UFDT | 1,287 s → 1,737 s (**+449 s**) | +451 s over 181 rows (**+2.5 s/row**) |

The gains themselves are nearly free — on UFDTLIRA the gained rows cost a median
**107 ms** in the base arm and **109 ms** in the shipped arm — so essentially the
whole cost is rungs running on queries they still cannot answer.

**This is the number that decides whether a control division loses files**, and
it is why a control is run at all: a division whose files sit near the timeout
can lose a verdict to work that buys nothing. It is also the mechanism behind
both losses above.

## Soundness

Every new verdict against **three** authorities — the declared `:status`, z3
4.13.3, cvc5 1.3.4 — with the comparable denominator published per authority
([ADR-1957]), because a zero disagreement over an authority that had no opinion
is not evidence:

| division | new verdicts | `:status` comparable | z3 comparable | cvc5 comparable | comparisons | disagreements |
|---|---:|---:|---:|---:|---:|---:|
| UFDTLIRA | 38 | 38/38 | 38/38 | 38/38 | 114 | **0** |
| UFDT | 19 | 18/19 | 17/19 | 19/19 | 54 | **0** |
| AUFDTLIRA | 24 | 24/24 | 24/24 | 24/24 | 72 | **0** |
| **total** | **81** | **80/81** | **79/81** | **81/81** | **240** | **0** |

The 3 no-opinion rows: 1 `UFDT` file declares `:status unknown`, and z3 timed
out at 24 s on 2 `UFDT` files. They are reported, not dropped.

**All 81 new verdicts are `unsat`**, and 0 `sat`↔`unsat` flips occurred anywhere
in 1,200 solves. That matters for how much the cross-check is worth: per
[ADR-1976] a reference cross-check is strong for an `unsat` and weak for a
`sat`, and this population is entirely `unsat`, so the cross-check is doing the
work it is good at. The `sat` side is exercised by the test suites instead,
where every `Sat` is replayed against the ORIGINAL assertions inside the test.

### A defect found in the verifier itself

The `:status` column above reads `0/81 comparable` with the script as inherited
from `bench-results/dispatch-decline-audit-20260913/`. Its second grep stage
anchored `(sat|unsat|unknown)$` against a string ending in `)`, so it matched
nothing on every file, always. ADR-1966 published the resulting zero as "these
files carry none". They carry it. Fixed here; see commit `78fcd2b26`.

## Noise floor

Three independent runs of ONE arm over a whole division at fixed code
(`noise-floor.sh`). ADR-1970 declined to ship on a `+2` whose baseline varied by
3 files at one commit; a delta reported without this number is unbounded.

**The arm measured is the SHIPPED one, not the base**, deliberately: the shipped
arm runs strictly more code per file (see the cost section — +0.55 s/row on this
very division), so it is the arm more exposed to ambient load, and measuring the
quieter one would understate the floor.

    UFDTLIRA, shipped arm, 200 files, 3 runs:  143 / 143 / 143
    band = 0
    files that disagree with themselves across the three runs: 0

**A band of 0 files, against a measured effect of +38 on that division.** The
per-file re-check says the same thing from the other direction: 0 of 83 movers
came out UNSTABLE.

Run 1 independently reproduces the A/B's own arm value for `UFDTLIRA` (143),
from a different script, on different cores, at a different time.

## What this is worth on `main`

**This is a BRANCH measurement.** It was taken on
`worktree-agent-a0e2fcdb67b70f186`, which is `main` at `c2fb0ade4` plus this
lane's five commits and nothing else. It will be re-measured on `main` after
merge, and today's post-merge board found one lane's `+22` was worth about `+6`
there while seven others landed within 0–6 files. So the question is not
rhetorical.

**Expectation: +79 should survive the merge close to intact, and the specific
reason is that the base arm already IS `main`.**

| division | `main` on the post-merge board | this A/B's base arm | difference |
|---|---:|---:|---:|
| UFDTLIRA | 105 | 105 | 0 |
| AUFDTLIRA | 96 | 96 | 0 |
| UFDT | 31 (ADR-1975 census) | 31 | 0 |

A branch whose base arm has drifted from `main` is measuring a delta against a
tree nobody will merge into; that is the mechanism behind a `+22` becoming `+6`.
This one has not drifted at all, on three divisions, at the same envelope.

**What can still reduce it, named in advance so the re-measure can be read
honestly:**

1. **Another lane landing on the same rows.** The 80 converted rows are the
   exactness-refused population; any lane whose change also decides them takes
   the credit first, and the board is a max, not a sum. `AUFDTLIRA` is the
   division where this has already happened once (ADR-1966's 110 came back as 96
   on `main` after ADR-1965 landed).
2. **The +0.55 to +2.5 s/row cost interacting with a busier box.** Both losses
   here are clock-driven. A `main` re-measure under heavier ambient load could
   turn more near-timeout rows the same way. The direction of this risk is
   asymmetric — it can cost files, not gain them.

**If the post-merge number lands materially below +79, the first thing to check
is overlap with whatever else merged, not this lane's protocol** — the noise
floor is 0 files over three full-division runs and the re-check found 0 of 83
movers unstable, so drift is not going to be the explanation.
