# Where the linear-arithmetic deficit actually goes — measured findings

Status: **measurement-grounded diagnosis (2026-08-21).** Executes ranked gap #1
of the [2026-08-21 SMT capability gap
analysis](../../plan/gap-analysis-smt-solvers-2026-08-21.md) §9: *QF_LRA 58.9 %,
QF_IDL 54.8 %, QF_RDL 67.7 %, QF_UFLIA 52.2 % of the reference — the largest
aggregate deficit, and four divisions **share one cause worth diagnosing before
building**.*

That last clause was a hypothesis. This note tests it.

**It is false as stated, and the way it is false is the useful part.** There are
**three** causes across the four divisions, and only one of them is shared —
by exactly two divisions, QF_IDL and QF_RDL. The largest single block of losses
in the *worst* division is not a search problem at all: it is a route that
returns `unknown` after a median of **1.3 s of a 24 s budget**, on 48 files the
reference decides.

This is diagnosis, not construction. No shipped code changed. Two candidate
fixes were built in a private snapshot and A/B-measured; one is refuted below
and the other is reported with its measured yield.

---

## 0. The instrument, and why you should believe it

Population: the four **committed, pinned** competition lists,
`bench-results/parity-lists/{QF_LRA,QF_IDL,QF_RDL,QF_UFLIA}.txt`, 200 files each,
sha256 `b636239947db` / `d7c9713a0280` / `9dc32e2c5dfb` / `f88e67890fae` —
**identical to the hashes recorded in the `PARITY.md` entries these ratios come
from**, so this is the same population, not a re-sample.

Per file, two solvers, 24 s wall each, 12 GiB address-space cap, external kill at
32 s:

- **axeyum** through `target/release/examples/uf_unknown_probe`, which calls the
  same `solve_smtlib` the shipped `smtcomp_cli` calls but *prints the
  `UnknownReason` kind and detail that the competition CLI is required to
  suppress*. That string is the whole diagnosis; without it every failure is the
  word `unknown`.
- **z3 4.13.3** (`/usr/bin/z3 -T:24`) as the second opinion. **cvc5 is not
  installed on this host**, so the recorded ratios cannot be reproduced here.

Route ladders come from a second pass: `explain_corpus --list … --json`, whose
`check_auto_explained` records which route was tried and why each declined.

**Every `file:line` in this note is as of `8426fbd2d`, the commit measured.** That
is not ceremony: `auto.rs` moved 23 lines under another lane while this note was
being written, so a citation read against the tip would already be wrong.

### Three checks that this instrument is not lying

1. **It reproduces the recorded score.** QF_LRA: this run decides **86/200** —
   exactly the 86/200 in the `PARITY.md` entry of 2026-08-06. QF_IDL 65 (recorded
   68), QF_RDL 99 (105), QF_UFLIA 92 (94). The three shortfalls are contention:
   this sweep ran 8-way parallel on a box whose load average sat at 12–22, and a
   24 s wall budget loses marginal files under load. Nothing moved the other way.
2. **z3 is a fair stand-in for cvc5 on these four lists** — which had to be
   checked, not assumed, because the whole ranking is stated against cvc5. z3
   decides 151 / 128 / 154 / 185 where cvc5 recorded 146 / 124 / 155 / 180. Every
   division is within 5 files. The *classification* below is of axeyum's failures
   and does not depend on the reference at all; the reference only decides which
   failures are worth counting.
3. **The two axeyum instruments agree on the mechanism.** Where the front-door
   probe attributes a QF_LRA miss to the LRA atom cap it counts 29 such files
   among the misses; the independent `explain_corpus` route pass counts 31 of the
   same population. The classes are not an artifact of one binary.

**Reference frame.** 16-thread i5-12600K, sweep at `-P 8` with three other lanes
on the box, load average 12–22 throughout. Wall times below are therefore an
*upper* bound and the decided counts a *lower* bound. This matters for one number
only (see §6) and is flagged there.

Raw per-file data and its column dictionary:
[`bench-results/linear-arithmetic-diagnosis-20260821/`](../../../bench-results/linear-arithmetic-diagnosis-20260821/README.md).

---

## 1. `unknown` is not one thing — the failure taxonomy

Every undecided file falls into exactly one of these, read off the
`UnknownReason` the front door produced:

| tag | meaning |
|---|---|
| **P** | **front-door reject** — the file never reached a solver |
| **S** | **admission decline** — a route refused the query on a size constant, before doing any search |
| **I** | **incompleteness** — a route ran, converged on nothing, and said so |
| **T** | **budget exhausted** — search ran out of wall clock |

The distinction that matters most is **S versus T**, because they have opposite
fixes: a T file needs a faster search, an S file needs the search to be *allowed
to start*.

---

## 2. Per-division classification

`files` is the whole class; **`miss`** is the sub-count z3 decides and axeyum
does not — the only files that represent a real deficit.

### QF_LRA — 86 decided, 65 misses

| class | files | miss |
|---|---:|---:|
| **S1** admission decline: online CDCL(T) LRA atom cap `> 1024` | 71 | 29 |
| **T1** budget exhausted (route name erased by the wrapper, resolved in §3) | 38 | 33 |
| **T3** deadline overrun — still running at 32 s on a 24 s budget | 5 | 3 |

### QF_IDL — 65 decided, 65 misses

| class | files | miss |
|---|---:|---:|
| **T1** budget exhausted (resolved in §3) | 58 | 25 |
| **S2** admission decline: `lia-dpll` pre-SAT skeleton envelope | 46 | 25 |
| **T3** deadline overrun | 31 | 15 |

### QF_RDL — 99 decided, 55 misses

| class | files | miss |
|---|---:|---:|
| **S1** admission decline: online CDCL(T) LRA atom cap `> 1024` | 56 | 19 |
| **T1** budget exhausted (resolved in §3) | 39 | 34 |
| **T3** deadline overrun | 4 | 0 |
| **T2** budget exhausted, route named | 2 | 2 |

### QF_UFLIA — 92 decided, 93 misses

| class | files | miss |
|---|---:|---:|
| **I1** incompleteness: lazy function-consistency CEGAR inconclusive | 48 | 48 |
| **T1** budget exhausted (resolved in §3) | 34 | 34 |
| **P1** **front-door reject: `Int` literal beyond the modelled range** | 26 | 11 |

### All four, 278 misses

| class | miss | share |
|---|---:|---:|
| T1 budget exhausted (wrapper-erased) | 126 | 45.3 % |
| S1 LRA atom cap `> 1024` | 48 | 17.3 % |
| I1 lazy UF CEGAR inconclusive | 48 | 17.3 % |
| S2 `lia-dpll` pre-SAT envelope | 25 | 9.0 % |
| T3 deadline overrun | 18 | 6.5 % |
| P1 `Int` literal beyond i128 | 11 | 4.0 % |
| T2 budget exhausted, route named | 2 | 0.7 % |

### Two things to read off this before going further

**`unknown` reasons are being destroyed on the way out.** 126 of 278 misses —
the single largest class — arrive as `preprocessed dispatch timeout after reduced
solve`, emitted at `auto.rs:1937` by `dispatch_reduced`, which discards whatever
the inner dispatch said and substitutes a generic timeout. The reason the
solver's own diagnostic is useless on 45 % of its hardest cases is a four-line
wrapper. §3 recovers the real reasons with a second instrument; a consumer with
`(get-info :reason-unknown)` could not.

**QF_UFLIA loses 26 files at the parser.** `Int` is modelled inside `i128`, and
the `20230314-Jaroslav-Bendik-Certora` family is EVM verification: literals like
`115792089237316195423570985008687907853269984665640564039457584007913129639936`
(= 2^256) are a **parse error**, not an `unknown`. SMT-LIB `Int` is unbounded;
ours is 128 bits. That is a clean capability zero, it costs 13 % of the division,
and no amount of solver speed touches it.

---

## 3. The route ladders — what the wrapper erased

Second instrument: `explain_corpus --list --json` over every miss file, giving
the ordered list of routes tried and the reason each declined. The ladder is
strikingly uniform inside each division and **different between them**.

```
QF_LRA   62/65   dl-online:NOT-APPLICABLE → nra-real-root:NOT-APPLICABLE → nra:BUDGET
QF_IDL   64/65   dl-online:BUDGET         → lia-simplex:UNSUPPORTED     → lia-dpll:BUDGET
QF_RDL   51/55   dl-online:BUDGET         → nra-real-root:NOT-APPLICABLE → nra:BUDGET
QF_UFLIA 82/82   … → dl-online:NOT-APPLICABLE → uf-arith-lazy-overbound-pre-lia:BUDGET
                   → lia-simplex:UNSUPPORTED → lia-dpll:BUDGET
                   → uf-arith-lazy-overbound:BUDGET
```

The **decisive** (last) attempt's reason, which is what the wrapper threw away:

| division | decisive route and reason | files |
|---|---|---:|
| QF_LRA | `nra` → `online CDCL(T) LRA atom cap exceeded (N > 1024)` | 31 |
| QF_LRA | `nra` → `lazy SMT: wall-clock timeout reached` (the legacy fallback loop) | 22 |
| QF_LRA | `nra` → `timeout in the online CDCL(T) LRA driver` | 10 |
| QF_IDL | `lia-dpll` → `pre-SAT skeleton exceeds the joint resource boundary` | 51 |
| QF_IDL | `lia-dpll` → other (timeout after N rounds; model reconstruction declined) | 13 |
| QF_RDL | `nra` → `online CDCL(T) LRA atom cap exceeded (N > 1024)` | 19 |
| QF_RDL | `nra` → `timeout in the online CDCL(T) LRA driver` | 18 |
| QF_RDL | `nra` → `lazy SMT: wall-clock timeout reached` | 14 |
| QF_RDL | `nra` → `lra: Fourier–Motzkin exceeded the wall-clock / size budget` | 2 |
| QF_UFLIA | `uf-arith-lazy-overbound` → `lazy function-consistency CEGAR inconclusive` | **82 / 82** |

### 3.1 The budget is fragmented, and the fragments are visible

`dl_probe_budget` (`auto.rs:3340-3345`) hands `dl-online` the whole timeout minus
`min(t/4, 6 s)` — **18 s of 24 s**. On QF_IDL and QF_RDL that probe *accepts* the
query (it is difference logic; that is what these divisions are) and then runs
out of clock (both blocks below are the same file,
`QF_IDL/asp/ChannelRouting/channelRoute.in9.smt2`, in one trace):

```
dl-online declined budget: "budget exhausted in the online difference-logic driver
  (atoms=11664, equality_gates=5760, bool_equality_gates=46225,
   cnf_vars=249855, clauses=607171)"
```

The remaining ~6 s then goes to a route that, on QF_IDL, **declines instantly on
a size constant it could have evaluated at t=0**:

```
lia-dpll declined budget: "lazy linear arithmetic pre-SAT skeleton exceeds the
  joint resource boundary (atoms=11664, cnf_vars=242902,
  base_trigger=>1024/>4096, moderate_envelope<=1280/<=8192,
  initial_clauses=0, blocking_lemmas=0); declining before the first SAT round"
```

So on 51 QF_IDL files the shipped configuration spends 18 s on a solver that
cannot finish, then 0 s on a solver that was never eligible. Nothing else is
tried. `MAX_PRE_SAT_ARITH_ATOMS = 1_024` / `MAX_PRE_SAT_CNF_VARS = 4_096`
(`dpll_lia.rs:61-62`) against files carrying 3,180–11,664 atoms.

### 3.2 The admission constants are inconsistent between neighbouring routes

Five routes on one ladder, five unreconciled opinions about what is admissible:

| route | admission constant | site |
|---|---:|---|
| `dl-online` (difference logic) | `MAX_DL_ATOMS = 1 << 20` | `dl_online.rs:101` |
| online CDCL(T) LRA | `MAX_ONLINE_LRA_ATOMS = 1_024` | `lra_theory.rs:93` |
| `lia-dpll` pre-SAT | `1_024` atoms **and** `4_096` CNF vars | `dpll_lia.rs:61-62` |
| eager Ackermann | `MAX_ACKERMANN_CONGRUENCE_PAIRS = 64` | `euf.rs:64` |
| UFLIA interface split | `MAX_SPLIT_DEPTH = 64` used as a **pair-count** cap | `uflia_online.rs:83,307` |

A 6,500-atom difference-logic query is admitted by `dl-online` (cap 2^20) and
refused by every route downstream of it (cap 1,024). The caps were each set by a
local measurement against a local failure — the comments say so, and they are
honest — but nothing reconciles them, so the ladder's *effective* admission
policy is "the first route's cap, then a cliff."

---

## 4. One cause, or four? — the answer is three, and they do not line up with the divisions

The gap analysis grouped these four rows because their *ratios* cluster in
52–68 %. Similar rates are not evidence of a similar reason, and the traces say
they are not one reason.

**Cause A — the difference-logic CDCL(T) driver runs out of clock. Shared by
QF_IDL and QF_RDL, and by nothing else.** `dl-online` accepts the query and
returns `budget exhausted in the online difference-logic driver` on **64/65**
traced QF_IDL misses and **51/55** traced QF_RDL misses. Same module
(`dl_online.rs`), same `CdclT` spine, same failure, and the two divisions
genuinely are one code path — `Mode::Integer` vs `Mode::Real` selected by
`numeric_mode` from the declared sorts, diverging only in strictness handling and
model lift. This part of the hypothesis is **confirmed**, for two divisions.

**Cause B — the real-linear route: half a size refusal, half a slow search.
QF_LRA, plus the tail of QF_RDL.** On QF_LRA, `dl-online` is *not applicable* on
62/65 misses, so cause A never arises; the decisive route is the online CDCL(T)
LRA driver and its legacy fallback. 31 of 65 refuse on `MAX_ONLINE_LRA_ATOMS`,
32 time out. QF_RDL shows the same split — but only *after* cause A has already
spent 18 of its 24 s.

**Cause C — the lazy UF/arithmetic CEGAR does not converge. QF_UFLIA, 82 of 82
traced misses, and no other division.** Not a shared cause with anything: it is
one route, one decline, 100 % of the division's non-parse misses.

**Plus a capability zero that is not a cause at all:** 26 QF_UFLIA files rejected
at the parser for `Int` literals beyond `i128` (§2).

So the honest restatement of gap #1 is: **two of the four divisions share a
cause; the other two each have their own; and QF_UFLIA additionally loses 13 %
of its files before a solver runs.** "Diagnose the shared cause before building"
was the right instinct and the wrong count.

### What *is* common — a dispatch policy, and it is not common to all four

The ladder is serial, each rung re-derives the problem from scratch, and no rung
can use another's work. Where an earlier rung *accepts* the query, the deciding
rung therefore gets a fragment of the clock. That is demonstrated on three of the
four divisions and not on the fourth:

- **QF_IDL, QF_RDL** — `dl-online` accepts and burns its 18 s reserve on 64/65
  and 51/55 misses; everything downstream runs on the remainder.
- **QF_UFLIA** — `uf-arith-lazy-overbound-pre-lia` and then `lia-dpll` both run
  and decline before the CEGAR route that finally answers; §5.2 measures what
  that route does with what it is left.
- **QF_LRA** — *not* fragmented. `dl-online` declines `NOT-APPLICABLE` on 62/65
  misses without spending anything, and the decisive route gets essentially the
  whole budget (median wall 27 s of a 24 s soft budget). QF_LRA's problem is the
  route itself, not the ladder above it.

So "the ladder wastes the budget" is a real finding on three divisions and an
overclaim on four. It is also why the caps in §3.2 matter more than their
individual values: a cap that fires on rung 4 has already let rungs 1–3 spend
the clock.

---

## 5. Two candidate fixes, built and measured

Both were built in a private snapshot (`scripts/lane-snapshot.sh`), never in the
shared tree, and each is a **one-constant** change so that nothing else can
explain the delta. Each was positive-controlled first: the patched binary was run
against a file whose baseline behaviour is known, and its output had to *differ*
before any sweep was believed.

### 5.1 REFUTED — "the LRA atom cap is terminal, so let it fall through"

The most obvious lever in §2. `MAX_ONLINE_LRA_ATOMS` refuses 71 QF_LRA files
(and 56 QF_RDL files) **before theory construction**, at a median of 1.5 s — 94 %
of the 24 s budget unspent — and the decline is classified `ResourceLimit`, which
`dpll_t.rs:121-133` treats as *terminal*: the legacy abstraction/refinement
fallback that would otherwise take the query is never entered. The route
comments themselves say the cap's original Fourier–Motzkin justification is gone
(`lra_theory.rs:76-92`).

Change: `lra_theory.rs:203`, `UnknownKind::ResourceLimit` → `UnknownKind::Incomplete`,
so the decline falls through to the fallback instead of ending the query.

Positive control: on `_standard_init5_ground.i_3_2_2.bpl_7.smt2` the baseline
prints `ResourceLimit / atom cap exceeded (1455 > 1024)`; the patched binary
prints `Timeout / preprocessed dispatch timeout after reduced solve`. The route
changed.

Result over all 71 QF_LRA atom-cap files, 24 s budget, 12 GiB address-space cap:

| outcome | files |
|---|---:|
| newly decided | **0** |
| aborted — memory allocation failure past 12 GiB | **54** |
| killed at the external 32 s wall | 10 |
| clean `unknown` (timeout) | 7 |

**The cap is load-bearing protection, not an oversight.** Removing its terminality
converts 71 clean, cheap `unknown`s into 54 process aborts. Both routes are
inadequate above ~1,000 atoms — the online one refuses, the fallback allocates
without bound — and the residual `memory_limit_mb` defect recorded in the gap
analysis §7 means nothing stops it. This is a genuine capability hole in the LRA
route, not a routing bug, and the fix is inside `AtomBuilder`/the fallback's
memory behaviour, not at the cap.

Data: `bench-results/linear-arithmetic-diagnosis-20260821/ab-atom-cap-fallthrough.tsv`.

### 5.2 CONFIRMED — QF_UFLIA gives up at 1.3 s because it never minimises a wide theory core

The QF_UFLIA finding is the sharpest number in this note. Its 48 `I1` files —
**all of which z3 decides** — return `unknown` after a median of **1.3 s** of a
24 s budget, having used **5 % of it**, with a median of **one** CEGAR solve
round.

Unwrapping the full decline (the front door truncates it; this is the tail):

```
lazy function-consistency CEGAR inconclusive (applications=154, …, solve_rounds=4,
  elapsed_ms=2957, …):
    lazy linear arithmetic retained 8426 literals in unminimized theory cores
    (limit 8192) after 83 rounds this solve; declining before the next SAT round
    (…, core_len_avg=69.8, core_len_max=353,
     core_src_lp=78, core_src_large=24, core_src_minimized=0, …)
```

Read `core_src_minimized=0`. **Not one theory core in the whole solve was
minimised.** `dpll_lia.rs:1334` sends a core to the unminimised `Large` bucket
whenever `indices.len() > MAX_MINIMIZED_THEORY_CORE_ATOMS`, and that constant is
**128** (`dpll_lia.rs:48`) against observed cores averaging 70 and reaching 353
literals. Wide cores then consume the cumulative
`MAX_DYNAMIC_LARGE_CORE_LITERALS = 8_192` budget (`dpll_lia.rs:86`) — 24 cores of
~350 literals is enough — and the solve is abandoned.

The two constants interact in exactly the wrong direction: **the cores too wide
to minimise are the same cores the retention budget exists to ration.** So the
loop never spends the oracle calls that would make its clauses narrow, and dies
of the clauses being wide, with 95 % of its wall clock untouched.

Change: `dpll_lia.rs:48`, `MAX_MINIMIZED_THEORY_CORE_ATOMS` `128` → `4_096`.
(Deletion minimisation is already deadline-bounded at `dpll_lia.rs:1958`, so the
worst case is spending budget that is currently thrown away.)

Positive control: on `mathsat/EufLaArithmetic/medium/medium10.smt2` the baseline
gives up after 1.5–3.0 s depending on machine load; the patched binary runs the
full budget on the same file. Behaviour changed.

Result over all 48 files, same budget and caps:

| outcome | files |
|---|---:|
| **newly decided** | **18** (17 `sat`, 1 `unsat`) |
| still CEGAR-inconclusive | 16 |
| now genuinely timing out (budget fully used) | 14 |

**Soundness: 18/18 agree with z3, and 18/18 agree with the benchmark's declared
`:status`. Zero disagreements on either axis.**

### 5.3 A third measurement, for calibration: is the rest just slowness?

40 miss files — 10 per division, taken deterministically as every *k*-th entry of
that division's miss list, never chosen after seeing a result — re-run at **4×
the budget**, 96 s instead of 24 s.

| outcome at 4× budget | files |
|---|---:|
| newly decided | **1** of 40 |
| still `ResourceLimit` — an admission decline | 22 |
| still `Timeout` | 17 |

Two readings, and the first is a control on the taxonomy itself. **S-class files
behave exactly as the taxonomy predicts they must:** a size refusal does not care
how much clock you give it, and 22 of these return the identical decline at four
times the budget. If the S/T split were an artifact of naming, quadrupling the
clock would have blurred it. It did not.

Second, and less comfortable: the T-class searches are **not one constant factor
from finishing.** Four times the wall clock buys one file out of forty. Whatever
closes QF_IDL/QF_RDL's cause A is a better search, not a longer one.

---

## 6. The single highest-leverage fix

**Minimise wide theory cores in the lazy LIA loop instead of abandoning the query
at 5 % budget use.** `dpll_lia.rs:1334`'s
`MAX_MINIMIZED_THEORY_CORE_ATOMS = 128` is the wrong number in the wrong
direction: it excludes from minimisation exactly the cores whose width then
exhausts `MAX_DYNAMIC_LARGE_CORE_LITERALS`, and the query dies with 95 % of its
wall clock unused.

### The measurement that supports it

Whole-division A/B, both binaries run under identical caps on the same machine
in the same window, over the full committed 200-file lists:

| division | files | baseline decided | patched decided | gained | lost | vs z3 | vs declared `:status` |
|---|---:|---:|---:|---:|---:|---:|---:|
| **QF_UFLIA** | 200 | 92 | **109** | **+17** | 0 | 0 disagreements | 0 disagreements |
| QF_IDL | 200 | 65 | 64 | 0 | 1 | 0 disagreements | 0 disagreements |

QF_IDL is the control: `dpll_lia` is on its ladder too (§3), so the change had to
be shown *not* to hurt a division it does not help. The one "lost" file is
contention, not a regression — re-run on a quieter box both binaries decide
`jobshop16-2-8-8-4-4-16.smt2` `sat`, baseline in 10.0/10.6 s and patched in
11.5/13.8 s, against a 24 s wall. It is a marginal file that the 8-way sweep
pushed over the line, and it was the patched binary's turn to lose it.

### What it would buy

+17 files on QF_UFLIA, measured. The recorded ledger entry is **94/180 =
52.2 %** (axeyum 94 of 200, cvc5 180 of 200); the same +17 on that baseline is
111/180 = **61.7 %**, which moves QF_UFLIA from the *worst* of the four to
second, ahead of QF_LRA (58.9 %) and QF_IDL (54.8 %) and still behind QF_RDL
(67.7 %). This is a projection from an A/B, **not** a parity result — only
`scripts/parity-run.sh` against cvc5 may move a number in `PARITY.md`, and that
sweep has not been run.

### Why this one and not the others

- It is the **only** intervention in this note that produced new decides at all.
  §5.1's, the obvious one, produced 0 and 54 aborts.
- It is a **policy** correction, not a capability build. The route already
  implements everything needed; it declines to use it.
- The cost is bounded by construction: `minimize_core` (`dpll_lia.rs:1950-1973`)
  already polls the deadline every candidate and returns the current — always
  valid — core on expiry, so the worst case is spending budget the shipped
  configuration currently throws away.
- The evidence is **48 files whose median whole-solve is 1.3 s of 24 s**. Nothing
  else in the four divisions has that shape; every other class is a query the
  solver genuinely worked on.

### The right form of the fix — not the constant this A/B moved

`4_096` was chosen to make the experiment decisive, not because it is right.
`MAX_DYNAMIC_LARGE_CORE_LITERALS` exists for a measured reason — 24 cores of
~430 literals grew BatSat from 1.8 GiB to an 8 GiB abort (`dpll_lia.rs:74-86`) —
and simply widening the minimisation window trades that protection for the gain
above. The shipped change should instead make minimisation **budget-driven rather
than width-gated**: minimise while wall clock and oracle calls remain, and fall
back to the `Large` bucket only when the budget is genuinely gone, which is what
line 1334's own `past_deadline` arm already does for the other half of the
condition. That keeps the memory protection while removing the case this note
measures — a solve that refuses to minimise, and then dies of not having
minimised, at 5 % budget use.

### Runners-up, ranked and costed

1. **`Int` beyond `i128`** (§2). 26 QF_UFLIA files, 11 of them z3-decidable, lost
   *at the parser*. Bounded, unambiguous, and untouched by any amount of solver
   work — but a real change to the integer model, not a constant.
2. **`dl-online` search speed** (cause A). The largest single-route class in the
   note — 64/65 QF_IDL and 51/55 QF_RDL misses — but §5.3 says 4× the budget
   buys 1 file in 40, so this is a *better* search, not a longer one, and it is
   not small.
3. **Reconcile the admission constants** (§3.2). `dl-online` admits 2^20 atoms,
   every route below it admits 1,024. At minimum, a route that will refuse on a
   *pre-solve, stable* count should say so **before** the ladder spends 18 s on
   the rung above it — on 51 QF_IDL files that decline is computable at t=0 and
   is taken at t≈22 s.
4. **Stop erasing the `unknown` reason** (`auto.rs:1937`). Not a decide-rate fix
   at all; it is why this note needed a second instrument to answer a question
   the solver already knew the answer to.



---

## 7. What this note does **not** establish

- **The reference is z3 4.13.3, not cvc5 1.3.4.** cvc5 is not installed on this
  host, so the recorded ratios cannot be reproduced here. §0 shows the two agree
  within 5 files per division on this population, which is why z3 is used to
  decide *which* failures count — but a per-file cvc5 comparison would move
  individual rows, and the ranked-gap ratios in the gap analysis stay cvc5's.
- **The measured decide-rates are depressed by contention.** 8-way parallel on a
  loaded box; QF_LRA reproduced its recorded 86 exactly, the other three came in
  2–6 files low. None of the *class* boundaries depend on wall time except the
  T3 (deadline-overrun) class, which is inflated by load.
- **The §5.2 yield is measured on one division at one budget on one machine.**
  It is a real A/B with a positive control and a soundness cross-check, not a
  parity entry. Nothing here has been through `scripts/parity-run.sh`, which
  remains the only instrument allowed to move a `PARITY.md` number — and which,
  as the gap analysis §2.1 records, is still gated by nothing.
- **`explain_corpus` decided 5 of the 267 miss files the front door did not**
  (4 `unsat`, 1 `sat`), consistent with its documented divergence from the
  shipped front door. That is 1.9 % of the traced population and it does not
  touch the mechanism attribution — the route ladders are read off the routes
  that ran, not off the verdict. No `explain_corpus` verdict is used as an oracle
  anywhere in this note.
- **The A/B binaries were built from a private snapshot** at `8426fbd2d`, not
  from the shared checkout, and neither patch is proposed for merge as written.
  §5.1's is refuted. §5.2's raises a constant whose stated purpose is to bound
  the cost of deletion minimisation; the measured 18-file gain says the *policy*
  is wrong, not that `4_096` is the right number.
- **No claim is made about QF_LIA or QF_NIA**, which were not measured here.

---

## 8. Reproducing this

```sh
# per-file front-door probe with the UnknownReason the competition CLI suppresses
cargo build --release -q -p axeyum-bench --example uf_unknown_probe
( ulimit -s 524288; target/release/examples/uf_unknown_probe <file.smt2> 24000 )

# route ladders
cargo build --release -q -p axeyum-bench --example explain_corpus
target/release/examples/explain_corpus --list <list> 24000 --json
```

Data committed with this note:

| file | contents |
|---|---|
| `bench-results/linear-arithmetic-diagnosis-20260821/QF_{LRA,IDL,RDL,UFLIA}.tsv` | 800 rows: axeyum verdict, `UnknownKind`, decline detail, wall ms; z3 verdict and wall ms; declared `:status`; file size |
| `.../ab-atom-cap-fallthrough.tsv` | §5.1, 71 files |
| `.../ab-uflia-core-minimization.tsv` | §5.2/§6, the 400-file QF_UFLIA + QF_IDL A/B |

These are the per-file sidecars the four `PARITY.md` entries claim to have. They
do not exist: `bench-results/parity-details/` is **gitignored** (`.gitignore:51`),
so every entry's `per-file detail` row points at a path that is absent from the
tree for all divisions but `QF_BV`, whose `.tsv` was force-added. That is why
this note ships its own.

## Provenance

Measured 2026-08-21 at `8426fbd2d`, 16-thread i5-12600K, z3 4.13.3 at
`/usr/bin/z3`, cvc5 absent. Sweep at `-P 8`, A/B passes at `-P 3`–`-P 6`, load
average 9–22 throughout, three other lanes on the box. A/B binaries built from a
private `scripts/lane-snapshot.sh` tree; the shared checkout was never modified.
