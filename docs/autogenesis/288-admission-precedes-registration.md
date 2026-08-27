# 288 — Admission precedes registration, so 0 admissible is not a registry gap

Date: 2026-08-27

## Task

Un-jam the frontier selector (doc
[`262`](262-curriculum-directed-frontier-selection.md)): 141 dependency-ready
facts, 0 admissible, every one rejected `no-registered-operation`. The brief
asked for at least one genuinely general operation registered over OPEN
facts (`applicability.fact_ids` a list, not length one), or a precise account
of why that is the wrong fix.

## Re-measurement, today's ledger (776 facts, up from 662 at doc 262)

```
python3 scripts/validate-facts.py
  776 facts checked, 0 errors (computed=2 conjectured=3 open=176 proved=591 refuted=4)

python3 scripts/fact-frontier.py --json
  ready: 132   admissible: 0   selected: None
  outcome: refused-no-admissible-candidate
  rejected_by counts: no-registered-operation=132, gate-coupling-review-required=8,
                       no-supported-route=6
```

Doc 262's 141/0 is now 132/0 — nine facts left the ready set (mostly settled
elsewhere by ledger lanes since 08-24), but the outcome is unchanged. This
document adds the diagnostic doc 262 was missing: **why registration cannot
close this gap by itself**, verified against the validator rather than
inferred from its behaviour.

`scripts/fact-frontier.py --json` now reports this split directly (new
`diagnostics.unregistered_by_route_class` key, purely additive — see
"What changed in this repository" below):

```
diagnostics:
  ready_count: 132
  admissible_count: 0
  unregistered_by_route_class:
    decidable: 1          <- could in principle be helped by registration
    no-route: 6           <- registration cannot help; no procedure exists
    proof-route-only: 125 <- registration cannot help without a NEW kernel proof
```

Of 776 facts in the WHOLE ledger — not just the ready 132 — exactly **one**
open fact (`F:fp16-add-monotone-rne`, fragment `QF_FP`) sits in any
SMT-decidable fragment. Every other open fact is `Nat`/`Int` (172) or `none`
(the six famous open problems: Collatz, CH, excluded-middle, FLT, FOL
validity, Gödel incompleteness, Goldbach — genuinely `no-route`, not a
registry gap of any kind).

## The finding: `admission` is a completed-work attestation, not a producer contract

`scripts/validate-autogenesis-operations.py`'s `ADMISSION_CONTRACTS` is a
closed set of exactly two tuples:

```python
ADMISSION_CONTRACTS = {
    ("proved", "kernel-lean", "kernel-term", "must-be-empty"),
    ("proved", "smt-term-level", "unsat-certificate", "must-be-nonempty"),
}
```

Both require `epistemic_status == "proved"`. There is no third tuple, and no
scope value (`authoritative` or `counterfactual-fixture-only`) is exempt —
`validate_operation` checks every operation's `admission` against this set
regardless of scope. **You cannot register an operation, of any shape,
without its `admission` block asserting the work is already proved.**

Verified empirically, not just read from the validator: every one of the 27
currently-registered operations names a fact whose CURRENT
`artifacts/facts/*.json` `epistemic_status` is `proved` — including all three
facts under `authoritative-mathlib-nat-modeq-remainder-family-v1`, registered
2026-08-26 (doc
[`287`](287-imported-nat-mod-operation-registration.md)), which turned out to
already be `proved` (dated 2026-08-18, via an independent route) by the time
that operation existed. Doc 287's own framing agrees with this finding
independently: *"Registration raises the reusable multi-target operation
count but settles zero facts... proof feasibility, dispatch authority, and
durable ledger mutation are three different claims."*

For the two "family" execution drivers that DO permit a fact's OWN ledger
status to still be `open` at registration time
(`bounded-induction-multi-target-v1`, `modeq-family-multi-target-v1`,
`imported-candidate-family-multi-target-v1`), the substitute requirement is
just as strict: each named target needs a `statement_adapter_manifest` +
candidate manifest already sitting in `artifacts/autogenesis/`, in state
`"candidate-checked-not-admitted"` — meaning a genuine, independently
kernel-checked proof candidate already exists, produced via the s5-hosted
pinned Mathlib checkout + `lean4export` toolchain
(`docs/contributor-guide/...`, referenced from every such manifest's
`reproduction` field). I confirmed there are currently **zero** such
manifests for any open fact:

```python
# every artifacts/autogenesis/*.json with a "state" containing "checked" and a
# source_fact_id: 13 found, 0 with a source_fact_id NOT already named in
# operations.json's applicability.fact_ids.
```

So the registry is not lagging behind a backlog of finished-but-unwired
proofs. Every checked candidate that has ever been produced has already been
wired in. **There is nothing sitting around free to register.**

## Why I did not register a new operation anyway

Given the above, the only way to register a genuinely new, HONEST operation
covering an open fact is to first produce a genuinely new, independently
checked proof candidate for it — using either:

1. the s5-hosted Mathlib + `lean4export` pipeline (I confirmed `ssh s5` works
   from this worktree) to export a new target statement and feed it to the
   existing generic checkers (`crates/axeyum-lean-import/examples/
   modeq_family_operation.rs`, which IS shape-generic — it declines by typed
   `UnsupportedRecursorShape`/`UnsupportedIffShape` rather than pattern-matching
   fixed theorem names — or the bounded-induction proposer), or
2. a live, in-repo decision-procedure run for `F:fp16-add-monotone-rne`, the
   one open fact whose fragment (`QF_FP`) already has a terminating route.

Both are real, bounded pieces of work, and neither is registry engineering —
they are proof/search production, explicitly out of this lane's scope
(`crates/` is another lane's, and this task's effort budget is a diagnostic
and tooling pass, not a new theorem). I chose not to gamble on either
inline:

- Route 2 has a cautionary data point already in the ledger: fp8 (E5M2, an
  *8-bit* format) took **25m46s** for the SAME symbolic bit-blast+DRAT route
  that would have to run at 16 bits (`F:fp8-add-monotone-rne`'s own evidence
  notes call this "the arity wall"). No prior timing exists for fp16; running
  it inline with no bound risks exactly the kind of open-ended background
  computation this project's own gotchas say never to defer an answer behind.
- Route 1 requires authoring a new Lean statement-adapter wrapper matching an
  exact Mathlib lemma shape, exporting it via `lake env lean` +
  `lean4export` on s5, and confirming the generic checker's structural
  pattern recognizes the goal — the same round trip that (per
  `docs/autogenesis/`'s own history, ~250 numbered documents deep on exactly
  this family) has taken many iterations even for lemmas simpler than the
  ones open here (e.g. `Int.ModEq.add_left`, `Int.ModEq.of_dvd`). Attempting
  it once, un-reviewed, risked landing a half-finished manifest or a false
  "shape supported" claim rather than real progress.

**This is the answer the task explicitly permits as a valid outcome**: the
registry is not the binding constraint, and fabricating admission for
unproved work is precisely the "checker that cannot fail" failure mode this
project has repeatedly found and repaired elsewhere. Registering an operation
whose `admission` falsely claims `proved` would be exactly that defect,
introduced deliberately.

## What changed in this repository

- `scripts/fact-frontier.py`: added a `diagnostics` key to the machine
  frontier (`--json`/`--output`) reporting `ready_count`, `admissible_count`,
  and — the new discriminator — `unregistered_by_route_class`, splitting
  "no registered operation" facts by whether their fragment already has a
  terminating decision procedure (`decidable`), needs a new kernel proof
  (`proof-route-only`), or has no route at all (`no-route`). This is purely
  additive (no existing key removed or renamed); `verify_machine_frontier`
  still round-trips because it recomputes the whole artifact, and
  `scripts/tests/test_fact_frontier.py`'s 8 tests still pass unmodified.
  Rationale for adding it: without this split, "0 admissible" reads as "the
  registry needs more entries" (doc 262's framing) when the real story —
  confirmed above — is that 125 of 132 ready facts need a NEW kernel proof
  and only 1 needs paperwork. Future lanes reading `fact-frontier.py --json`
  no longer have to reconstruct this by hand.
- No changes to `artifacts/autogenesis/operations.json`,
  `artifacts/autogenesis/nursery-v1.json`, or any fact in
  `artifacts/facts/`.

## Verification run

```
scripts/check-autogenesis-holdout-isolation.py   -> PASS (unchanged; I did
  not touch the nursery partition)
python3 scripts/validate-autogenesis-operations.py  -> PASS (unchanged registry)
python3 scripts/tests/test_fact_frontier.py         -> 8 passed
python3 scripts/fact-frontier.py --json             -> ready=132 admissible=0
  (unchanged outcome, new diagnostics surfaced)
```

## Curriculum crosswalk, re-measured

Doc 262's crosswalk (nursery families -> `docs/curriculum/curriculum.toml`
nodes) is about `artifacts/autogenesis/nursery-v1.json`, a fixed,
held-out-partitioned population — it has not grown this week (touching it
requires the amendment-ledger protocol, ADR-0542, and nothing here warranted
that). Its five-of-23-nodes-covered finding is unchanged.

What HAS grown since doc 262 is the fact ledger's own `kernel-lean` route:
this week's merge landed ~30 new `proved` `CReal`/`Complex` facts (uniform
convergence, alternating-series bracketing, polynomial evaluation over
`CReal`, factor-quotient/Horner-form facts over `Complex`). These map
directly onto three curriculum nodes that doc 262 recorded as
**zero-pressure**: `sequences-and-limits`, `calculus`, and `complex` — all
three already exist in `docs/curriculum/curriculum.toml` with
`status = "lean-horizon"`, `family = ""` (no `axeyum-scenarios` solver
family), which is the SOLVER axis. The new facts are on the KERNEL axis
(doc 262's 2026-08-24 amendment already separates these two and warns against
conflating them). I did not edit `curriculum.toml`: the three relevant nodes
already exist, adding finer subdivisions (limits/continuity/integration/
series as distinct nodes) would each need a real
`scripts/gen-foundational-concepts.py` `CURRICULUM_MAP` entry naming an
EXISTING `artifacts/examples/math/` pack, which no such node has yet — adding
one without a real pack risks the same "asserts coverage it cannot
demonstrate" defect `check-curriculum-coverage.py` exists to catch. The
correct, safe statement is: **`sequences-and-limits`/`calculus`/`complex` now
carry real KERNEL pressure (dozens of proved facts) despite zero SOLVER
pressure**, which is a genuine update to doc 262's picture and is recorded
here rather than in a curriculum.toml edit that would need its own pack work
to back it honestly.

## What would actually unjam this

In order of confidence:

1. **Someone with the s5 Mathlib/lean4export pipeline and time to iterate**
   exports a new statement-adapter target from the `Int.ModEq`/`Nat.ModEq`
   neighbourhood already proved-out at refl/symm/trans/comm (candidates
   visible in the ready set today: `F:ml430-int-modeq-add-left-6e17c69a`,
   `F:ml430-int-modeq-neg-f649f6c5`, `F:ml430-int-modeq-of-dvd-b9c41fce`,
   `F:ml430-int-modeq-sub-3148f130` — four facts sharing one lemma family,
   which is exactly the "list, not length one" shape asked for), gets the
   generic checker to accept at least two of them, and registers ONE
   multi-target operation over the accepted set. That operation would then
   be genuinely general in the sense doc 228 and this task ask for.
2. **A bounded attempt at `F:fp16-add-monotone-rne`** via the existing
   `axeyum-bench/smtcomp_cli` route, run with an explicit timeout and
   reported honestly if it does not finish — this is a single fact, so even
   a success only moves `admissible` from 0 to 1, but it is the only
   currently-open fact where NO new proof engineering is required, only
   compute.
3. **A schema question worth an ADR, not a silent code change**: should
   `ADMISSION_CONTRACTS` grow a third, weaker tuple for a genuinely
   prospective producer registration (e.g. `epistemic_status: "attempted"`,
   distinguishing "the machine will try this" from "the machine already
   succeeded")? That would let `fact-frontier.py`'s `admissible` mean
   "a general procedure is registered to attempt this," decoupled from "a
   proof already exists" — closer to what doc 262's language ("registration
   is a human decision") seems to have assumed the field already meant. I am
   not proposing this be made — it changes what the headline "N admissible"
   number is allowed to claim, and that is squarely the kind of decision
   CLAUDE.md's Session Protocol reserves for an ADR, not a diagnostic pass.
