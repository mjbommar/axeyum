# Two defects this board found, with repros

Neither is fixed here. **This is a measurement lane**: a board row and a
behaviour change in one branch cannot be told apart afterwards, so no solver
code was touched. Each of these should be its own lane.

Both are **sound** — every one returns `unknown`, which is a first-class result,
and the board's zero-disagreement check is clean on all three divisions. They
cost coverage, not correctness.

---

## 1. `abv-online-cdclt` enters and makes no progress. 16 of QF_ABVFP's 21 winnable files.

**Repro** (24 s budget; any of the 16 files in `../winnable/QF_ABVFP.txt` whose
census row reads `open_after=dl-online`):

```sh
smtcomp_cli /nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/\
QF_ABVFP/20170428-Liew-KLEE/aachen_syn_nan_float.x86_64/query.03.smt2 \
  --trace --timeout-ms 24000
```

`--trace` prints:

```
; partial abv in_flight=abv-online-cdclt online_entered=1 online_returned=0 …
                cegar_rounds=0 congruence_pairs_scanned=0 index_evals=0 row_lemmas=0
; partial route decided_by=none bound_by=dl-online last=dl-online … attempts=3
; partial route-open ms=24982 after=dl-online attributed_ms=17
```

The dispatch records **three** route attempts (`fd:parse`, `probe`, `dl-online`)
on a ladder that reaches **14** when it completes, and 24.982 s of a 25 s budget
is in the open segment after `dl-online`. `abv-online-cdclt` was entered and did
not return. Under ADR-1936 every one of these rows is `UNCLASSIFIED`: the census
cannot rank them, because what they describe is the dispatcher.

**It is not slowness, and the distinction is measured, not assumed.** The same
file at a **600 s** budget — 25x the board's — is in `abv-online-cdclt.log`
here:

```
; partial abv in_flight=abv-online-cdclt online_entered=1 online_returned=0 … cegar_rounds=0
; partial route-open ms=600979 after=dl-online attributed_ms=20
unknown
```

**600.979 s and zero CEGAR rounds** on a query with `row_sites=4` that cvc5
decides in 0.11 s and z3 decides in 0.11 s. A 25x budget bought zero rounds, so
the route is not converging slowly; it is not reaching its first round. (That
600 s run was on the shared dev box under other lanes' load, which is why its
TIME is not quoted as a measurement — but no contention factor turns a >0 round
count into 0.)

This is the single largest blocker on `QF_ABVFP` and it is a bug, not a missing
capability: `row_sites=4` is a trivially small array problem and the FP core
already decides QF_BVFP 199/200.

**What a fix lane should confirm first:** whether the route is deadline-blind
(takes no deadline, so the watchdog is the only thing that stops it) or is stuck
before its loop. The instrument says `phase stack=none depth=0 … deepest=dl-online:check`
— the code holding the budget carries no phase frame at all, which is itself a
finding about instrument placement (ADR-1936's last consequence).

---

## 2. `array projection element sort mismatch` — an internal error on a mixed FP/BV array

**Repro:**

```sh
smtcomp_cli /nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/\
QF_ABVFP/20170501-Heizmann-UltimateAutomizer/interpolation2_true-unreach-call.c_40.smt2 \
  --trace --timeout-ms 24000
```

```
; give-up kind=Error detail=backend failure: array projection element sort mismatch:
  read site produced (_ BitVec 32) for an array whose element sort is (_ FloatingPoint 8 24)
```

One file of 200. Both references decide it. The message is specific enough to
act on: a read site's projected sort disagrees with the array's declared element
sort across the FP/BV boundary — exactly the combination this division is named
for.

It is reported here rather than ranked with the capability blockers, because an
internal error names a defect in the code that raised it, not a fragment we
cannot decide. `census-summarize.py` breaks it out for that reason, and
`controls/` has a mutant requiring that break-out to exist and to carry the
repro path.

---

## 3. `MAX_THEORY_ATOMS = 1_024` — the QF_UFBV cap. See `../README.md`.

`crates/axeyum-solver/src/ufbv_online.rs:93`. Named here for cross-reference;
the counts and the sizing are in the division's own section of the board README,
because unlike the two above it is a deliberate, documented limit rather than a
defect — the question it raises is what the right number is, not whether the
code is wrong.
