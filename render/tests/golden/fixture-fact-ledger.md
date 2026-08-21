# Two ledger entries, rendered from their evidence

*The P0 golden fixture for the render strand*

Authors: Axeyum render strand, lane CORE

> This document is the smallest thing the render pipeline can produce that is still honest. Every number, statement and badge below was resolved from a file on disk: the two propositions come from the fact ledger by checked reference, the claims about them come from a recorded run whose declared inputs are re-hashed on every build, and the table and the figure are copied out of that run rather than typed here. The prose is the only part a human wrote.

## What the pipeline is for

A rendered document here is a checker output, not prose about one. The distinction is not stylistic: the claims below carry the status their evidence earned, and if the run behind them had exited nonzero the badges would say so, because the emitter that printed them cannot compute a status at all. Nothing in this file can be edited into looking better.

Read the scope of the claims carefully, because it is the honest part. The run behind them validated two fact-ledger entries and read what they record. It did **not** check the mathematics -- that was checked elsewhere, by the routes the ledger names, and those statements appear below as statements of record with their own status axes rather than as claims this document makes.

**Claim -- Ledger record of F:bool-and-comm** [CHECKED]

The fact-ledger entry for Boolean conjunction's commutativity is schema-valid and records a proof term this project's kernel admitted, together with the assumptions that admission rests on.

- Evidence `R:fixture-fact-ledger-check` (primary): Validated 2 fact-ledger entries against artifacts/ontology/fact.schema.json and checked their recorded status, route, footprint and evidence rows: 0 finding(s). -- `python3 render/tests/fixtures/make_run_record.py` exited 0, 3 input(s) re-hashed.
  - run claim `f-bool-and-comm` [CHECKED]: The ledger entry F:bool-and-comm validates against artifacts/ontology/fact.schema.json and records epistemic_status=proved on proof_route=imported-kernel-lean with an axiom footprint of 3 entries and 2 evidence row(s), 2 of them check_status=checked, naming 5 distinct checker(s).
  - replay: `python3 render/tests/fixtures/make_run_record.py --out /dev/stdout`

**Claim -- Ledger record of F:excluded-middle** [CHECKED]

The fact-ledger entry for the law of excluded middle is schema-valid and records a term-level decision, on a route whose trust base is different in kind from the imported one above.

- Evidence `R:fixture-fact-ledger-check` (primary): Validated 2 fact-ledger entries against artifacts/ontology/fact.schema.json and checked their recorded status, route, footprint and evidence rows: 0 finding(s). -- `python3 render/tests/fixtures/make_run_record.py` exited 0, 3 input(s) re-hashed.
  - run claim `f-excluded-middle` [CHECKED]: The ledger entry F:excluded-middle validates against artifacts/ontology/fact.schema.json and records epistemic_status=proved on proof_route=smt-term-level with an axiom footprint of 2 entries and 1 evidence row(s), 1 of them check_status=checked, naming 3 distinct checker(s).
  - replay: `python3 render/tests/fixtures/make_run_record.py --out /dev/stdout`

**Claim -- No unearned axiom-freedom** [CHECKED]

Neither entry claims an empty axiom footprint on a route that cannot deliver one. This is the check worth having: an empty footprint is the strongest thing this project publishes, and only the constructed kernel route can earn it.

- Evidence `R:fixture-fact-ledger-check` (primary): Validated 2 fact-ledger entries against artifacts/ontology/fact.schema.json and checked their recorded status, route, footprint and evidence rows: 0 finding(s). -- `python3 render/tests/fixtures/make_run_record.py` exited 0, 3 input(s) re-hashed.
  - run claim `no-unearned-axiom-freedom` [CHECKED]: Neither fixture fact records an empty axiom_footprint on a route other than kernel-lean, so neither claims an axiom-freedom its route cannot deliver.
  - replay: `python3 render/tests/fixtures/make_run_record.py --out /dev/stdout`

## What the run measured

Taken out of the run record by reference. No cell below was typed into this manifest.

| fact | established here | externally | proof route | axiom footprint | evidence rows | checked rows | distinct checkers |
| --- | --- | --- | --- | --- | --- | --- | --- |
| F:bool-and-comm | proved | proved | imported-kernel-lean | 3 | 2 | 2 | 5 |
| F:excluded-middle | proved | proved | smt-term-level | 2 | 1 | 1 | 3 |

Source: `python3 render/tests/fixtures/make_run_record.py` (exit 0), 3 input(s) hashed.

![Bar chart of axiom-footprint size and evidence-row count for each fixture fact](https://github.com/mjbommar/axeyum/blob/10ef29f7f9764e29628e88d21184515c6cf6156a/render/tests/fixtures/fixture-footprints.svg)

*Drawn from the same rows: a changed footprint changes the picture.*

## The statements of record

**Boolean conjunction is commutative** (`F:bool-and-comm`)

For all Booleans x and y, x && y equals y && x.

```lean4
((x : Bool) -> ((y : Bool) -> Eq.{1} Bool (Bool.and x y) (Bool.and y x)))
```

Status: established here `proved`; externally `proved`.

Proof route: `imported-kernel-lean`.

Axiom footprint (3):

- `lean4export-3.1.0-stream-faithfulness`
- `axeyum-lean-import-wire-translation`
- `lean4export-3.1.0-delivered-bytes-are-the-intended-export`

Depends on: nothing (foundational).

Evidence rows in the ledger: 2.

Pulled from `artifacts/facts/F-bool-and-comm.json` by reference. If that id stopped resolving, this build would fail rather than print a plausible-looking theorem.

<details>
<summary>Statement of record: the law of excluded middle</summary>

**Law of excluded middle** (`F:excluded-middle`)

For every proposition p, p or (not p) holds.

```smtlib2
(assert (or p (not p)))
```

Status: established here `proved`; externally `proved`.

Proof route: `smt-term-level`.

Axiom footprint (2):

- `axeyum-ir.bool-evaluator`
- `classical-two-valued-bool-semantics`

</details>

<details>
<summary>How the first claim above was resolved</summary>

The resolution this build performed, in order. Every step either produced data or refused; none of them produced a status.

1. **read the manifest block**
   - in: block `claim-bool-and-comm`
   - out: a claim with one evidence reference. Zero references would have been a build error here, before anything was read.
2. **load the run record**
   - in: run-fact-ledger-check.json, expecting id `R:fixture-fact-ledger-check`
   - out: the record, its declared id matching the reference.
3. **re-hash every declared input**
   - in: the record's three declared input paths
   - out: three SHA-256 digests, each equal to what the run recorded. A single mismatch would have ended the build: the evidence would be describing bytes that are no longer there.
4. **compute the rendered status**
   - in: declared `checked`, run exit status 0, run claim status `checked`
   - out: `checked` -- the minimum of the declared ceiling and every cap the evidence imposed. This step can only lower.
5. **resolve the statement of record**
   - in: the fact reference `F:bool-and-comm`
   - out: the ledger entry's title, prose, formal statement and both status axes, fetched rather than transcribed.
   - by: `F:bool-and-comm` (Boolean conjunction is commutative)

</details>

**Certificate -- kernel admission**

The proof term behind the first statement of record: an exported Lean declaration stream that this project's independent kernel type-checked. The artifact's digest is verified on every build of this document.

Artifacts:

- [lean4export NDJSON 3.1.0 stream](https://github.com/mjbommar/axeyum/blob/10ef29f7f9764e29628e88d21184515c6cf6156a/artifacts/lean-imports/bool-and-comm.ndjson)

Replay:

```sh
cargo test -p axeyum-lean-import --test imported_fact_evidence -- --nocapture 2>/dev/null | grep -q 'AXEYUM-IMPORT-FACT|F:bool-and-comm|'
```

*Archived -- [the run record this document rests on](https://github.com/mjbommar/axeyum/blob/10ef29f7f9764e29628e88d21184515c6cf6156a/render/tests/fixtures/run-fact-ledger-check.json) (not shown here).*

If you want to disbelieve this page, the cheapest attack is to change one byte of either fact file and rebuild. The build will refuse, and it will name the file, the digest the run recorded and the digest on disk. That is the whole design in one sentence.

---

Rendered from Doc-IR by `axeyum-render`. Epoch 1787312215 (2026-08-21T11:36:55Z, source `commit`), commit `10ef29f7f9764e29628e88d21184515c6cf6156a`.
