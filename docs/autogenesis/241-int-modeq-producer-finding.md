# 241 — The `integer-modular-equivalence` schema is real but currently unreachable: `Nat.div_rec_lemma`

**Measured 2026-08-22**, `cargo build -p axeyum-lean-import --example
statement_adapter_import` (debug), against the four exported streams under
`/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-modeq-family-v1/`.

## The task

Build the second general autogenesis producer: one schema — unfold
`Int.ModEq n a b` to `a % n = b % n`, close with a primitive `Eq` combinator
(`Eq.refl`, `Eq.symm`, `Eq.trans`, `Iff.intro Eq.symm Eq.symm`) — covering
exactly four `train`-partitioned facts in `integer-modular-equivalence`:

    F:ml430-int-modeq-refl-30e15520   Int.ModEq.refl
    F:ml430-int-modeq-symm-984a6e67   Int.ModEq.symm
    F:ml430-int-modeq-trans-6d7863e0  Int.ModEq.trans
    F:ml430-int-modeq-comm-1e4bcc07   Int.modEq_comm

All four confirmed `train` in `artifacts/autogenesis/nursery-v1.json`
(`family: "integer-modular-equivalence"`), so building against them is
legitimate under the train/development/held-out isolation rule.

## What already existed

An earlier attempt at this same task, **earlier in this session** (2026-08-22
~21:01), had already done the expensive groundwork. It was killed by the
coordinator, who diagnosed it as stalled from a frozen transcript and a clean
worktree — both true, and both consistent with the work it was actually doing,
which was writing to `/nas3` outside the repository. The diagnosis was wrong and
the artifacts survived, which is the only reason this pass was cheap. Before it
was stopped it had:

- Written the proof-free adapter source
  `AxeyumAutogenesisIntModEqFamilyV1.lean` on s5
  (`/home/mjbommar/lean-import-scale/mathlib4/`), defining
  `Axeyum.Autogenesis.Statement.IntModEqFamily.{intModEqRefl, intModEqSymm,
  intModEqTrans, intModEqComm}` as transparent `Prop`-valued `def`s — no
  axiom, theorem, opaque declaration, or proof value, exactly the
  `encoding: transparent-definition-of-prop` contract the working
  `bounded_induction`/`statement_reflexivity` producers use.
- Exported all four (plus four `Nat.ModEq` siblings for `development`) via
  `lean4export 3.1.0` against the pinned `Lean 4.30.0` /
  `mathlib4@c5ea00351c28e24afc9f0f84379aa41082b1188f` checkout, landing at
  `/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-modeq-family-v1/`:
  eight streams, `int-modeq-{refl,symm,trans,comm}.ndjson` and
  `nat-modeq-{refl,symm,trans,comm}.ndjson`, all with zero-byte `.err`
  files (clean export, ~6,000 records / ~320 KB each).

Both artifacts are exactly what this task's brief pointed at building, and
neither needed to be redone.

## What I measured

Built `statement_adapter_import` (the generic proof-isolated-import probe,
`crates/axeyum-lean-import/examples/statement_adapter_import.rs`) and ran it
against all four `int-modeq-*.ndjson` streams with their matching target
definition:

```
$ ./target/debug/examples/statement_adapter_import \
    int-modeq-refl.ndjson  Axeyum.Autogenesis.Statement.IntModEqFamily.intModEqRefl
Error: TrustedDeclaration { name: "Nat.div_rec_lemma", kind: Theorem }

$ ... int-modeq-symm.ndjson  ... intModEqSymm
Error: TrustedDeclaration { name: "Nat.div_rec_lemma", kind: Theorem }

$ ... int-modeq-trans.ndjson ... intModEqTrans
Error: TrustedDeclaration { name: "Nat.div_rec_lemma", kind: Theorem }

$ ... int-modeq-comm.ndjson  ... intModEqComm
Error: TrustedDeclaration { name: "Nat.div_rec_lemma", kind: Theorem }
```

All four fail identically, at the same declaration, before the goal ever
reaches a producer. `import_statement_ndjson` refuses `Nat.div_rec_lemma`
because it is a **theorem with a proof body** in the export stream (not a
recognized primitive or an already-bridged trusted substitution), and the
statement-isolation contract categorically will not admit an unreviewed
proof term — that is the whole point of the trusted-declaration refusal.

## Why a Nat division lemma gates an Int modular-equivalence fact

`Int.ModEq n a b` unfolds (transparently) to `a % n = b % n` using
`Int.emod`. `Int.emod` is defined in terms of `Nat.mod`, and `Nat.mod` is
compiled from **well-founded recursion**, whose generated equation lemma is
`Nat.div_rec_lemma`. So every one of the four target statements — despite
being pure `Eq`/`Iff` combinator facts about an equivalence relation, with
no arithmetic content in the *proof* this schema would supply — still
carries a `Nat.div_rec_lemma` dependency baked into the **statement's own
transparent unfolding**, before any proof search starts. This is exactly
the same 38-row first-blocker documented in
`docs/autogenesis/240-the-cascade-is-exact.md`; the ModEq family is gated by
that same shared bottleneck, not by anything specific to modular
arithmetic or to this schema.

## Disposition

Per the brief: this is not a producer failure to fix by reaching further
into the search; it is a statement-adapter blocker outside the scope given
to this task (`crates/axeyum-lean-import/src/` is owned this hour by the
lane clearing `Nat.div_rec_lemma` and its siblings — see
`docs/autogenesis/240-the-cascade-is-exact.md`'s bridged-blocker list). No
Rust producer/checker file was written for `int_modeq_support`, and no
registry entry was added to `artifacts/autogenesis/operations.json`,
because the schema has never reached a proof-isolated kernel goal to run it
against — registering it now would be exactly the "aspirational entry"
the brief forbids.

**The schema itself is still the deliverable of this analysis, and it is
unchanged and ready:** once `Nat.div_rec_lemma` (and any of its own
transitive theorem dependencies — `Nat.div_rec_fuel_lemma`, `Nat.le.brecOn`,
etc., per the coordinator's inspection of the same streams) is bridged the
same way `Nat.lt_irrefl`/`Or.elim`/`if_pos`/`of_decide_eq_true` already were,
all four `int-modeq-*.ndjson` streams should reach the goal unchanged (same
export, same target names), and the producer described in the task brief —
unfold `Int.ModEq`/`Int.modEq_comm`, close with `Eq.refl`/`Eq.symm`/
`Eq.trans`/`Iff.intro Eq.symm Eq.symm` — is a same-day follow-up once that
happens. The four `nat-modeq-*.ndjson` `development`-partition siblings are
already exported too, for whichever lane picks this back up.

## Gates run

- `python3 scripts/validate-facts.py` — unaffected (no fact files touched).
- `python3 scripts/check-autogenesis-holdout-isolation.py` — unaffected (no
  operation registered, no held-out fact touched).
- `python3 scripts/check-development-partition.py` — unaffected.
- `python3 scripts/gen-production-provenance-ledger.py --check` — unaffected
  (operations.json unchanged: still 25 operations, 24 single-fact + 1
  five-fact family).

No source files under `crates/axeyum-lean-import/` were modified. This
document and the measurement above are the only artifacts this task
produced.

## Companion measurement

[242](242-nat-division-gates-modular-arithmetic.md) reaches the same conclusion
from the other direction, and the two are worth reading together: it *predicted*
this blocker by reading the 32 trusted theorem records in the raw streams and
tracing the `%` unfolding, before the adapter was run. This document *measured*
it by running the adapter and reading the error. Prediction and measurement
agreeing on `Nat.div_rec_lemma` is stronger evidence than either alone, and 242
carries the breakdown of the surrounding 32-theorem cluster — most of which is
order material, not division.
