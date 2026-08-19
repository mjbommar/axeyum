# agent-axreal — `Real` -> `AxReal`, and the assertion it caught

Detail behind [`docs/plan/status/71-axreal.md`](../status/71-axreal.md). The
decision is
[ADR-0522](../../research/09-decisions/adr-0522-the-axiomatized-reals-are-renamed-before-they-are-retired.md);
the scoping is [`64-retire-real.md`](64-retire-real.md).

## What the rename is

One string literal. `crates/axeyum-lean-kernel/src/arith_prelude.rs` interns the
carrier once (`kernel.name_str(anon, "Real")`) and every other declaration is
`declare_axiom(kernel, r, "<leaf>", …)` under it, so the whole 30-row package
moves with that one edit. Everything else in the diff is *consumers* — string
matches, doc comments, two golden Lean fixtures, and the ledger's row keys.

Unlike `AxNat`, which `Kernel::lean_name` remaps at **render** time only (Lean's
builtin `Nat` needs its special kernel support, so the stored root stays `Nat`),
this renames the **stored** declaration. `display_name`, `lean_name`,
`axiom_footprint` and the ledger therefore all move together and no code path
can observe the old spelling.

## The assertion it caught, which is the whole argument for doing it first

`reconstruct::tests::lra_dispatch_tests::the_theory_front_door_accepts_the_farkas_route`
asserted

```rust
assert!(source.contains("Real.add_le_add"));
```

against a module the shipped route emits over the **constructed** carrier. It
passed — because `CReal.add_le_add` contains `Real.add_le_add` as a substring.
The test read as "the theory front door really carries ordered-field content
from the axiomatized package" and in fact could not tell the two carriers apart;
it would have gone on passing if the route had been switched back. The rename
turned it red on the first run, because `CReal` does not contain `AxReal`.

It now asserts `CReal.add_le_add` **and** `!source.contains("axiom AxReal :
Sort")` — the same two-sided shape its sibling
`the_shipped_strict_conflict_module_is_over_the_constructed_carrier` already
used, with a comment recording why the loose form was worthless.

## And a second one, in evidence for a settled fact

`examples/infeasibility_farkas_lean.rs` decides whether the facade's module
"carries ordered-field content" with

```rust
name.contains(".lra.hyp._") && (ty.contains("Real.le") || ty.contains("Real.lt"))
```

`CReal.le` satisfies that too, so once the facade route moved to the constructed
reals the scan went on printing the right verdict about the wrong carrier. The
rename turned it into `no ordered-field hypothesis axiom` and the example exited
non-zero — which is the **checker command of `F:schedule-critical-chain-
infeasible`**, a `proved` fact. The predicate now names both carriers in full
and the command exits 0 again with `kernel axioms 26 = 17 prelude + 4 variable +
5 hypothesis`, so the fact's 17 prelude rows are re-derived rather than
transcribed. That fact's own notes had transcribed the collision as fact:
"declares an `axeyum.reconstruct.lra.hyp._N : Real.le …` hypothesis axiom".

So this is the **third and fourth** known instance of one substring collision.
The first was worked around in place (`examples/front_door_carrier.rs` decides
the carrier from the carrier *declaration*, and says so) and nobody looked for
another; two more were sitting in a test and in a fact's evidence, and only a
rename could see them, because both were passing.

Both fixes are two-sided or exhaustive rather than looser: the test now also
asserts `!source.contains("axiom AxReal : Sort")`, and the predicate still fails
on a module carrying no ordered-field hypothesis at all.

## What the rename BROKE, and what did not notice

Six evidence rows across three settled facts are `grep -E` patterns anchored on
an example's stdout, and the rename moved that stdout:

| fact | row | anchored on |
|---|---|---|
| `F:farkas-refutation-over-constructed-reals` | `creal-equality-slot-costs-nothing` | ``the `Real` route declares 18 AXIOMS`` |
| | `the-real-comparison-is-not-vacuous` | `over Real  : closed False …` × 5 |
| `F:real-axioms-modelled-by-constructed-setoid` | `creal-model-add_comm` | `^law\s+Real[.]add_comm\s+CReal[.]add_comm` |
| | `creal-model-mul_comm` | same shape |
| `F:shipped-front-door-refutes-over-constructed-reals` | `front-door-emits-the-constructed-carrier` | `carrier Real (AXIOMATIZED)` count = 0 |
| | `the-real-control-is-not-vacuous` | `over Real  : footprint …` × 3 |
| | `the-verdict-lines-and-the-exit-status` | `the Real control is non-vacuous` |

`validate-facts.py` reported **340 facts, 0 errors** throughout: it checks the
ledger's *structure and semantics* and never executes a `checker_command`. The
gate that does is `scripts/check-fact-evidence-replay.sh`, which is in
`scripts/check.sh` and was not in this lane's brief. Nothing in the fact schema
ties a pattern to the program whose output it reads, so **a rename in the code
silently rots the evidence for a `proved` fact and the fact ledger's own
validator says nothing**. That is worth a mechanism, not just a fix.

Note the shape of `front-door-emits-the-constructed-carrier`: it asserts
`carrier Real (AXIOMATIZED)` occurs **0 times**. After the rename it still read
0 — for the new reason that the string cannot occur at all. A count-of-zero
assertion survives a rename by going vacuous, which is the one direction that
does not announce itself.

All eighteen evidence rows on the four affected facts were re-run after the fix;
every one exits 0.

## The ledger: a rename is not a retirement

`gen-lean-axiom-ledger.py` keys rows on `(prelude, name)`, so the rename is a
30-row departure and a 30-row arrival, and `--check` says so. The obvious
remedy, `--accept-population-change`, is the wrong verb twice over: it drops
every row to `unclassified` (losing 30 classification and discharge decisions),
and it files 30 rows as **retired**, which publishes a 30-row reduction in the
trusted surface that did not happen. The generated ledger's headline "N
assumptions have been retired" would have read 65 for 35 real retirements.

So the script gained `--accept-rename OLD=NEW`. It re-keys live rows, carries
their authored metadata across, and takes `canonical_type`/`type_sha256` from the
measurement — identity still comes from the kernel, never from the flag. A
target the kernel does not admit is refused with a pointer to
`--accept-population-change`, and the prefix maps `X` and `X.child` only, never
every name that merely starts with `X` (that is the `CReal` confusion one level
up).

Result: `LEAN_AXIOM_LEDGER_RENAME|rows=30|Real->AxReal`, then
`total=30 … real=30 … retired=35 axiom_free=7 unclassified=0` — same 30, same 35,
no metadata lost.

## Measurements

| quantity | before | after |
|---|---|---|
| trusted surface | `complex 0 · creal 0 · integer 0 · logic 0 · nat 0 · rat 0 · string 0 · real 30` | identical |
| ledger row names | `Real`, `Real.*` | `AxReal`, `AxReal.*` |
| retired rows | 35 | 35 |
| unclassified live rows | 0 | 0 |
| `gen-lean-axiom-ledger.py` tests | 39 | 43 |
| ledger mutation controls | 10 measured | 13 measured, no survivors |

Mutation controls for the three new guards, each `killed 1`:
`--accept-rename refuses an unmeasured target`,
`--accept-rename prefix does not capture a longer name`,
`--accept-rename OLD=NEW argument shape`. The prefix guard **SURVIVED** on the
first attempt — the test used a prefix (`Rea`) that no longer prefixes any live
row after the rename — and was rewritten against `AxRea` before it counted.

Two golden Lean fixtures carry the axiomatized package and were re-blessed:
`arithmetic-farkas-linear.lean` (37 occurrences) and
`arithmetic-sum-of-squares.lean` (11). Both diffs are rename-only.

## Not done here

The retirement itself (ADR-0522 step 2). Also: this repository's historical
documents — ADRs, strand notes, diaries — still spell `Real`, deliberately. They
record what was true when they were written, and rewriting them would destroy
the record the rename exists to make legible.
