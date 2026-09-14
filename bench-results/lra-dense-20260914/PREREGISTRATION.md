# LRA-DENSE — pre-registered rules

Written and committed **before** any measurement of this lane's own, and before
any code change exists. ADR-2045 is the handoff; its data is the input and its
numbers are not re-litigated here except where this lane re-derives them.

Lane: `lra-dense`. ADR number reserved: **ADR-2055**.

Branch base: `git merge-base main HEAD` is
`91c721f8eda678e40124e089d6761ce3d3d02f94`, which **is** local `main`'s HEAD.

Compute: **6 pinned pairs** — s5 `(0,8)`/`(1,9)`, s6 `(0,8)`/`(1,9)`,
s7 `(0,8)`/`(1,9)`. All three hosts read load average 0.00–0.09 at launch.
Two shards per host and not three, for ADR-2045's reason: this division's
undecided rows reach ~7.8 GiB each against 27 GiB hosts.

---

## 0. The populations, fixed now

Derived by `scripts/lists.py` from ADR-2045's committed `census-rows.tsv` and
`ref/*.tsv`, with its merged addressability rule (best verdict per file per
solver over the loaded pass **and** the idle re-take).

| list | n | what |
|---|---:|---|
| `ALL200.txt` | 200 | the whole `QF_LRA` board division — **the A/B population** |
| `DENSE74.txt` | 74 | the offline dense-matrix engine route: 40 `ABORT/oom` + 34 `Timeout/ResourceLimit` |
| `DENSE50.txt` | **49** | the addressable subset of `DENSE74` — the prize |

**The prize is 49, not ADR-2045's 50.** ADR-2045's `Timeout/ResourceLimit`
bucket holds 35 rows of which 30 are addressable, but **one of the 35 is the
lazy-SMT wall-clock row**, which its own census attributes to a different
engine. Excluding it leaves 34 dense-engine clock rows, 29 of them addressable,
and `20 + 29 = 49`. This is bookkeeping, not a disagreement: ADR-2045's "50 of
61 = 82 %" becomes **49 of 61 = 80 %**, and the finding is unchanged.

---

## 1. Decision RULES, not a conversion rate

A rate taken from ADR-2045's **mixed** blocker population does not transfer to
`DENSE74`, so none is carried over. Every rule below is an outcome test.

### R0 — re-derive, do not inherit

The A/B's base arm re-derives the population on **this branch**. If the base arm
does not read **107 decided of 200**, the A/B is void and I say so rather than
reporting a delta against an inherited number.

### R1 — the profile decides whether there is a lever at all (priority 1)

Report, per row, over `DENSE74`:

- peak RSS (`/usr/bin/time -v`), and
- the measured split between the `lra.rs:944` dense materialisation, the
  `Tableau` dense matrix, and everything else.

**Falsifier.** If the `lra.rs:944` dense materialisation is under **10 %** of
peak RSS at the median `DENSE74` row, then removing it **cannot** be the lever,
and I report that as the finding instead of shipping it as one. The refactor may
still land on its own merits (R3) but **must not be described as addressing the
5.07 GiB**.

**This rule can only be answered by measurement.** A profile is required; an
arithmetic estimate from `m`, `nvars` and `size_of::<Rational>()` is reported
**beside** it as a cross-check and is not a substitute for it.

### R2 — is the round-trip real?

"Real" means both halves, each checked separately:

1. `lra.rs` materialises a dense `nvars`-wide `Vec<Rational>` per constraint; and
2. `Tableau::new` re-sparsifies **exactly that vector** and the dense form has
   no other consumer.

If either half fails — in particular if the dense vector is read again after
`Tableau::new` — the round-trip is **not** pure waste and I say so.

### R3 — verdict-neutrality of the refactor, verified not assumed

The refactor (L1) is claimed semantics-preserving. That claim is **tested**:

- **0** rows decided in the base may change verdict in the arm;
- **0** `sat`↔`unsat` flips anywhere;
- soundness against declared `:status`: **0** disagreements, with the
  **comparable denominator printed** beside the zero;
- the z3 differential fuzzes (`qf_lra_differential_fuzz`,
  `simplex_lra_fallback_differential`, `qf_uflra_differential_fuzz`) pass with
  **nonzero** test counts, each `test result:` line quoted.

Any failure here **blocks the change**, whatever the verdict delta.

New decisions **are** permitted and are the gain; they are not neutrality
violations.

### R4 — SHIP rule, separate from the CLAIM rule

Pre-registered separately so a null on one cannot be retro-fitted into the other.

**SHIP (L1, the round-trip removal).** Land it iff: R3 passes in full **and**
measured peak RSS over `DENSE74` does not increase on any row **and** the
exit-status channel (R6) shows **0 new aborts**. A verdict-neutral reduction in
peak RSS is worth landing on engineering grounds even at net `+0`; it is not
worth landing at net `+0` **and** unmeasured risk.

**CLAIM (a board gain).** Report a board gain only if net ≥ **+5** over
`ALL200`, with **0** verdict losses and **0** new aborts, and the net strictly
exceeds the measured row-level noise floor (R5). Below that the result is
published as a **null**, and a null closing an 80 % bucket is the reportable
outcome, not a failure.

**No lever is to be manufactured.** If the profile says the round-trip is a
minority of peak RSS and removing it decides nothing, that is the answer.

### R5 — noise floor, measured, at ROW level

Two identical passes of the **same arm** over one whole division (`ALL200`),
ten-plus minutes apart with different neighbours. Report rows differing and
verdict-identity flips, not only the count. **The band is assumed non-zero until
measured.** Every moved row is re-run **3× per arm** before it is counted.

### R6 — the exit-status channel

ADR-2045's arm was `losses=0` by verdict and **created five new aborts**. So the
census carries, per row per arm: verdict, **process exit status** (`134` abort,
`124` wall kill), wall ms, peak RSS, stderr line 1.

**A row that terminates cleanly in the base and aborts in the arm is a LOSS**,
recorded as such even when both arms read `unknown`. Reported on its own line,
never folded into the net.

### R7 — control and exposure, both run, both non-vacuous

- **Control: `QF_S`** — must not move. Non-vacuity is **shown, not asserted**: I
  name the route binding its undecided rows and verify that route **executes**
  there, so that the zero is a zero over a live division and not over 200
  instant declines.
- **Exposure: `QF_UFLRA`** — this is the division that **shares the changed
  code** (`simplex::feasible_within`), so it is where a regression would appear.
  Required: **0** losses and **0** new aborts.

If either is not run, it is reported as **"did not run"** and the change does
not ship on the strength of a zero nobody measured.

### R8 — authorities for any new verdict

Every row newly decided by the arm is checked against **z3** and **cvc5** using
`bench-results/dt-exactness-20260913/verify-new-verdicts.sh`.
`z3 -T:` takes **SECONDS**, `cvc5 --tlimit` takes **MILLISECONDS**.
No-opinion counts are reported **separately** from disagreements, and the
**comparable denominator is printed beside any zero** (ADR-1957).

### R9 — Wilson intervals

Any proportion over n < 100 carries a Wilson 95 % interval.

### R10 — the A/B measures THIS BRANCH

Stated in the runner header along with **polarity**. The post-merge value is
**predicted explicitly** before the merge.

### R11 — the cell cap (`MAX_TABLEAU_CELLS`) is a separate question

Asked and answered on its own. A cap in `feasible_within` converts an abort into
a decline, which is correct; ADR-2045 already measured that converting aborts to
declines decides **nothing**. So:

> **"The cap belongs in `feasible_within` and it buys 0 verdicts" is a
> legitimate, publishable finding and is pre-registered as an acceptable
> outcome.**

It is NOT to be rescued by re-describing it as a gain.

### R12 — the online engine's refusal

If reached: **size** what the refusal actually is
(`"model did not replay (arithmetic outside the incremental engine)"`) and
**hand it off named**. Do not half-build a second incremental engine. Naming it
precisely is a success condition; starting it is not in scope.

---

## 2. Falsifiers, written down in advance

1. **The dense materialisation is a minority of peak RSS.** Then the round-trip
   is waste but not *the* waste, and the 5.07 GiB is the `Tableau` — which no
   refactor removes, only a different algorithm does. (R1.)
2. **Removing it decides nothing** because the rows that stop aborting then
   spend the clock instead. ADR-2045 measured exactly this shape once already:
   clearing the admission screen let 21 rows reach the engine and decided **0**.
3. **The cap decides nothing**, for ADR-2045's already-measured reason.
4. **The refactor is not verdict-neutral**, in which case it is a defect and not
   a refactor, and R3 blocks it.

If 1 and 2 both hold, the honest report is: *the offline dense engine is not
fixable by removing allocations from it, and the division needs the incremental
engine to accept these queries* — which is a clean negative closing an 80 %
bucket, and is what R12 then hands off.

---

## 3. Banned, having each produced a wrong answer in this repository

- `echo "exit=$?"` after a pipeline; `grep -q` under `pipefail`; an empty grep
  read as a negative result; fixed-name scratchpad files shared across lanes.
- A gate or suite believed without a **nonzero** `test result:` count.
- A reference measurement taken under load (ADR-2045's own first pass moved by a
  third for this reason). **All reference measurement on idle hosts.**
- Describing an unfinished check as anything but **"did not run"**.
