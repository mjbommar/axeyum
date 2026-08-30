# Formalized mathematics strand — August 2026

> **STATUS 2026-08-19 — the cross-check story changed, and this strand is its
> home.** Lean has **two** checkers and they disagree about our own artifact.
> Measured 2026-08-18 on the 470-declaration constructed-real carrier:
> `lean AxeyumCarrier.lean` — the **elaborator** — refuses 4 declarations in
> 14.1 s, while `lean --run replay-lean4export.lean carrier.ndjson` — the
> **kernel**, `Environment.addDeclCore` from an empty environment — accepts
> **all 470** in 1.4 s.
>
> - **Our kernel is not more permissive than Lean's.** That was one of three
>   candidate explanations and it is not the one. Lean's elaborator will not
>   unfold a `theorem` while reducing, and the four refused `CReal` declarations
>   must compute through `Nat.gcd`, whose descent rests on the theorem
>   `Nat.mod_lt`. Re-spelling `theorem` as `def` — one token per line, no term
>   changed — makes the whole carrier elaborate clean
>   ([ADR-0517](../research/09-decisions/adr-0517-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md)).
> - **The default did not change, deliberately**
>   ([ADR-0518](../research/09-decisions/adr-0518-proofs-stay-spelled-theorem-and-the-def-option-is-a-measuring-instrument.md)):
>   every artefact this repository ships already elaborates clean under
>   `theorem`, so the switch buys nothing on the shipped surface and would break
>   the suite that pins the divergence.
> - **The coverage hole that hid it.** Emission is reachability driven, so
>   **122 of the carrier's declarations had never been handed to any Lean.**
>   Closed by a suite that exports the COMPLETE environment and requires Lean's
>   reported constant count to equal our kernel's.
> - **Two limitations to publish, not to footnote.** The shipped `.lean`
>   artefact still does not carry the whole carrier, and 4 of the carrier's
>   declarations are kernel-checkable but not elaborator-checkable.
>
> The mechanism, the coverage hole and how to state the limitation are in
> [`03-integrate.md`](03-integrate.md#lean-has-two-checkers-and-they-disagree).
> Also measured 2026-08-19 and used below: the trusted surface is
> `complex 0 · creal 0 · integer 0 · logic 0 · nat 0 · rat 0 · string 0 · real 30`,
> where `real` is the axiomatized ℝ package the constructed carrier exists to
> replace.

> **STATUS 2026-08-15 — started.** The strand had no landed work for as long as
> it existed; the first increment is in. What landed, and what it measured:
>
> - **The importer was pointed at real Lean for the first time.** 40 well-known
>   `Init`/`Std` theorems, exported one at a time by an official `lean4export`
>   binary and imported: **13 admitted, 27 declined**. Every decline was our
>   *kernel* refusing a declaration on definitional equality; the reader declined
>   nothing. The blocker census and the four clusters are in
>   [`01-collect.md`](01-collect.md).
> - **Five imported facts landed end to end**, each citing a SHA-256-pinned
>   stream in `artifacts/lean-imports/` and re-derived by
>   `scripts/check-fact-evidence-replay.sh`.
> - **`imported-kernel-lean` is now a distinct `proof_route`**
>   ([ADR-0454](../research/09-decisions/adr-0454-imported-kernel-lean-proof-route.md)),
>   and it cannot claim `axiom_footprint: []`. Recording what Lean says does not
>   make it checked here, and the ledger now refuses to let it read that way.
>
> Two results from the other strands still bound what this one should plan for:
>
> - **The Lean proof-TERM route is unavailable at our scale.** Mathlib's
>   `lrat_proof` peaks at 96.6 GB on a 628 MB certificate; native reflection does
>   the same instance in 8.9 GB
>   ([arXiv:2607.00815](https://arxiv.org/abs/2607.00815), verified). Any plan
>   here that assumes importing or emitting proof terms for large results needs
>   rewriting around reflection. See
>   [`../refactor-2026-08/05-proof-consumption.md`](../refactor-2026-08/05-proof-consumption.md).
> - **The export is now actually tested.** 163 of 163 modules are read by a real
>   Lean 4.30.0, where previously zero were and the suites printed `ok` anyway.
>   Integration claims can now be checked rather than asserted.

The third roadmap strand, parallel to
[engineering](../refactor-2026-08/README.md) and
[mathematics](../mathematics-2026-08/README.md).

Those two ask *where is the code untidy* and *what mathematics can we do*. This
one asks: **the world has already formalized roughly ten million lines of
mathematics. What do we collect, how do we synthesize it, how does it get into
axeyum, and what do we build ourselves instead?**

> **Parallelism.** The ingest path lives in `crates/axeyum-lean-import/` and the
> kernel in `crates/axeyum-lean-kernel/`. The kernel is **owned by another lane**
> — see
> [`refactor-2026-08/00-parallel-work.md`](../refactor-2026-08/00-parallel-work.md).
> The *collection* and *synthesis* phases below touch neither and can start now.

## The universe, measured

Re-measured 2026-08-15; the earlier figures in this table were roughly a year
stale and two of the licences were described wrongly. Sources and the full
correction list are in [`01-collect.md`](01-collect.md).

| library | system | size | licence |
|---|---|---|---|
| **Mizar Mathematical Library** | Mizar | ~3.7 MLOC — **unverified**, primary sites unreachable | dual GPL-3.0+ and CC BY-SA 3.0 |
| **Archive of Formal Proofs** | Isabelle/HOL | **~5,360,300 lines, 1,017 entries, ~324,200 lemmas** (isa-afp.org) | **per entry**: BSD-style or LGPL |
| **Mathlib 4** | Lean 4 | **135,592 definitions, 284,457 theorems** (mathlib_stats) | Apache-2.0 |
| **Mathematical Components** | Rocq/Coq | not verified this round | not verified this round |

Network analysis of Mathlib alone extracts **308,129 declarations and 8.4 M
edges across 7,563 modules**
([arXiv:2604.24797](https://arxiv.org/abs/2604.24797), pinned to Mathlib commit
`534cf0b` of 2026-02-02; verified). That figure and the `mathlib_stats` one do
not reconcile — different snapshot, different definition of "declaration".

These are the corpora we can check ourselves against, and the map of what has
already been formalized. Their size is a *stock* built at human bandwidth over
years; ours is a **rate**, and it is measured below.

## The thesis of this strand

**Build the foundations ourselves, axiom-free, in parallel — and use the world's
libraries to check ourselves against, not to substitute for building.**

Measured on 2026-08-14: one lane produced **73 proved theorems in 11 h 43 min**
— ~149/day/lane — every one reporting **no axioms**, while also writing an ADR
each and updating tests. Ten lanes is ~1,500/day. The construction plan and the
arithmetic are in [`05-throughput.md`](05-throughput.md); the binding constraint
turns out to be a **single-file lock**, not compute or capability.

> **Do not quote that rate without the correction beside it.** Re-measured on
> 2026-08-17 and again on 2026-08-19: **6.4 theorems/day/lane realized against
> 149 projected**, because a lane spends most of its time on things that are not
> proving. And the counter that produced 149 measures *one prelude* —
> `nat_prelude` has been flat at **139** since 2026-08-17 while ℤ (57 derived,
> all axiom-free), ℚ, the constructed ℝ and ℂ were proved out elsewhere. Both
> re-measurements, and why no number in that section can currently size a roadmap
> item, are in [`05-throughput.md`](05-throughput.md#re-measured-2026-08-19-the-counter-is-flat-and-the-counter-is-now-the-wrong-instrument).
>
> **"The binding constraint turns out to be a single-file lock" is falsified.**
> The lock was removed: `nat_prelude.rs` is 845 lines today, sharded into eleven
> topic modules, the first two splits landing 2026-08-14. Five days of sharded
> library produced +33 theorems. It was a real multi-agent-hygiene win and not a
> throughput win, and this sentence conflated the two.

What makes this ours rather than a re-derivation is the loop the integration
allows: the library gives the solver facts, the solver decides goals the library
needs, reconstruction turns those decisions into kernel-checked terms, and the
DAG says what to prove next. **That cycle was closed end to end once on
2026-08-14.** It has never been automatic. Making it automatic is the strand.

Import stays, in a supporting role we are uniquely placed to fill:

- We have an **independent Lean kernel** (`axeyum-lean-kernel`, 37,987 lines)
  that is not Lean, written in a different language, by different people.
- We have a **fail-closed importer** for the official `lean4export` NDJSON
  format, with 25 test suites — and, since 2026-08-15, six SHA-256-pinned
  streams produced by a real exporter that back six facts in the ledger. All
  six import clean today with `axioms=none`.
- On 2026-08-14 the **reverse** direction closed too: Lean's own kernel accepted
  an axeyum development from an empty environment, with a tamper control.
  **Narrower than it reads, corrected 2026-08-18:** what Lean saw was the
  closure of one refutation, not the carrier — 343 of 465 declarations when it
  was measured. The whole carrier was first handed to Lean on 2026-08-18, and
  Lean's *kernel* took all 470 while its *elaborator* refused four (see the
  status block above).

A library checked by exactly one kernel is a single point of trust. A second,
independent kernel that admits the same declarations is a measurement almost
nobody can produce — and it tells us where our own construction diverges from
the world's. That is worth having *in addition to* building, and it is the
research community's pluralistic-library problem ("QED Reloaded", Rabe et al.),
whose interchange infrastructure we should consume rather than rebuild.

**And the divergence has now been measured in the direction that matters most.**
The worrying outcome was never "Lean refuses something of ours"; it was "our
kernel admits something Lean's would not," which is a soundness defect wearing a
compatibility costume. On the constructed-real carrier that outcome is excluded:
Lean's kernel accepts every declaration our kernel does. The residue is a
*checker* difference inside Lean, not a kernel disagreement between projects —
which is a much better result and a much narrower claim, and it is only visible
because someone exported the complete environment rather than the reachable part
of it.

## Where we actually stand

Re-measured 2026-08-16. The previous version of this section was stale on nearly
every line, and it was misdirecting the strand: it named as "next" work that had
already been done in this strand's own diaries.

**Verified on this host, by running it:**

```
axeyum-lean-import      25 test suites, 81 examples, fail-closed reader
artifacts/lean-imports  6 pinned streams, 6,057 records, 340 KB, sha256-pinned
                        ALL SIX import clean today, `axioms=none`
artifacts/facts         6 facts on proof_route `imported-kernel-lean`
Nat prelude             128 theorems, 23 of them divisibility
references/             EMPTY — nothing cloned on this host
```

**Re-measured 2026-08-19**, each row by running the named example
(`-p axeyum-lean-kernel` except `front_door_carrier`, which is
`-p axeyum-solver --features full`):

```
artifacts/facts         340 fact files; docs/research/09-decisions 523 ADRs
Nat prelude             139 theorems, 31 of them naming `dvd`   (nat_theorem_inventory)
Int prelude             57 derived, 57 with an EMPTY axiom footprint, 0 still asserted
                                                                 (int_theorem_inventory)
trusted surface         complex 0 · creal 0 · integer 0 · logic 0 · nat 0 · rat 0
                        · string 0 · real 30                     (nat_axiom_inventory
                                                                  --include-constructed)
shipped front door      1,304,276 / 1,330,091 / 1,442,247 B over CReal, ZERO carrier
                        axioms on all three; the `Real` control non-vacuous at 12/17/8
                                        (front_door_carrier --require-axiom-free, exit 0)
artifacts/lean-imports  6 pinned NDJSON streams, 476 KB
references/             NOT empty on this host: `lean4export` and `drat-trim` are
                        cloned. The 2026-08-16 line above was a HOST fact and it
                        has changed; it was never a project fact (`references/`
                        is gitignored), which is exactly why it should not be
                        read as a project status.
```

`real: 30` is the **axiomatized** ℝ package and the only nonzero row — it is what
the constructed carrier exists to replace, not an assumption the constructed
results rest on.

**Cited from [`diary-import-scale.md`](diary-import-scale.md) and
[`diary-import-strings.md`](diary-import-strings.md), NOT re-derived here** —
reproducing them needs a built `lean4export`, which this host does not have:

```
census, seed 20260815, after string literals landed
  Init+Std  500 sampled   CLEAN 254 (50.8%)   DECLINED 242   distinct roots 50
  Mathlib   400 sampled   CLEAN 139 (34.8%)   DECLINED 241   distinct roots 267
  declaration records reaching the kernel   634,291 / 1,181,015  (18.6x / 86x)
  UNSUPPORTED `literal-string-typing`       262 / 315  ->  0 / 0
```

### What the old text got wrong

- *"13 of 40 well-known theorems admitted"* — superseded by a 900-declaration
  seeded census across `Init`+`Std` **and** Mathlib.
- *"`Nat.add_comm` cannot be imported"* — it imports. `nat-add-comm.ndjson`
  admits 52 declarations with `axioms=none`, verified above. The `brecOn`
  blocker was closed by lane `import-brecon`.
- *"dependency-closed Init/Std/mathlib population UNSTARTED"* — both were
  censused, twice, with the corpus retained so the second run is identical
  rather than merely equivalent.
- *"NO mathlib clone"* — a 400-declaration Mathlib sample was censused. (Nothing
  is cloned *now*, because `references/` is gitignored; that is a host fact, not
  a project one.)
- *"`L3` 0/12 — the phase that supplies ℤ, `Dvd`, and finite sums"* — L3 as an
  **import** milestone may still be open, but its stated *motivation* is
  overtaken: ℤ was proved out natively on 2026-08-16 (integer prelude, 0 axioms),
  ℚ exists over it, and the Nat prelude carries 23 divisibility theorems. We no
  longer need to import ℤ in order to have it.

### The frontier, as measured rather than as planned

The binding constraint is no longer scale, the reader, or string literals. It is
a **small, enumerable set of definitional-equality failures in Lean's own
`Init`/`Std` core** — and the strongest result this strand has produced is that
**not one root blocker is Mathlib-specific**. Category theory, measure theory,
affine geometry and functional analysis all check; what refuses is `Nat.bitwise`,
`Nat.Linear`, `Fin`.

Two consequences for what to do next, neither of which is "download more":

1. **Diagnose the roots, which nobody has done.** The scale lane said so
   plainly — *"I located them and did not diagnose them; that is the honest
   state."* 50 roots in `Init`+`Std`, 267 in Mathlib, against 98%+ cascades.
2. **`ImportLimits` record cap is now a verdict-shaped harness bound.** Fourteen
   Mathlib streams stop at `record count exceeds 2000000`. That is not a kernel
   refusal and must never be counted as one.

## The four phases

1. [`01-collect.md`](01-collect.md) — which corpora, in which formats, under
   which licences, and what it costs to hold them.
2. [`02-synthesize.md`](02-synthesize.md) — the same theorem exists in four
   systems under four names. Alignment, deduplication, and the interchange
   formats that already exist (Dedukti, MMT/OMDoc, OpenTheory) so we do not
   invent a fifth.
3. [`03-integrate.md`](03-integrate.md) — getting it through
   `axeyum-lean-import` into an independently-checked environment, at
   population scale rather than fixture scale.
4. [`04-implement.md`](04-implement.md) — the boundary decision: what we import
   versus what we prove ourselves, and why `nat_prelude` is being built by hand
   while 284,457 theorems sit next door.
5. [`05-throughput.md`](05-throughput.md) — **the construction plan**: the
   measured production rate, the single-file lock that caps it, and the
   self-extension loop only this architecture can run.
6. [`06-parallel-production.md`](06-parallel-production.md) — **the fleet
   playbook**: how to run four to five Sonnet lanes against the frontier
   concurrently, measured on 2026-08-23 when the library went 463 -> 544
   axiom-free theorems in a day. The four binding constraints in order (cargo
   slots, disjoint file areas, the coordinator's own merge throughput, stalls),
   the brief shape that works, where Haiku is and is not usable, and the merge
   check that caught a silent five-theorem revert.

## The measure of success

Not how much we ingest, and not theorem count. **Theorems the system proved
without a human writing the proof**, on a zero-axiom base, in the order the DAG
asked for — plus, from the import side, how much foreign mathematics axeyum can
now *use* in a proof, a certificate or a negative control that it could not use
before.

**Corrected 2026-08-19: the first number is no longer zero, and the correction is
smaller than it sounds.** Three facts carry `kind: kernel-term`,
`check_status: checked` and an empty axiom footprint with no hand-written Lean
proof term behind them — `Nat.ascFactorial_zero`, `Nat.descFactorial_zero` (a
target-independent bounded producer that emits `Eq.refl`; 2 of 138 candidate
rows) and `Nat.fib_add_two` (a target-specific term program, repaired by hand
across two failed runs, so it does **not** meet the autogenesis programme's own
autonomy bar). All three re-derive today: `scripts/check-autogenesis-fact-operation.py`
exits 0 on each. What is machine-driven throughout is selection, checking and
crash-safe admission.

[`05`](05-throughput.md#it-is-no-longer-zero--corrected-2026-08-19) has the
qualifications. **C2 — solver refutation reconstructed into a library theorem —
has still produced zero**, so the arrow this strand is named for remains ahead of
us; the number moved by a different and narrower route.
