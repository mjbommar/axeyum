# ADR-0537: User triggers are a hint channel on the arena, and they replace auto-selection

Status: accepted
Index-summary: SMT-LIB `:pattern` was parsed and dropped, so a hand-written trigger had no effect at all. It is now recorded on the `TermArena` as a side table keyed by the quantifier term — a hint channel that no denotation reads — and a usable annotation REPLACES the E-matcher's own trigger selection rather than adding to it. Multi-patterns (conjunctive within one `:pattern`) and alternatives (disjunctive across several) are both honoured; anything the matcher cannot fire is declined whole and falls back to auto-selection. `:weight` is still absent, deliberately.
Index-status: accepted

Date: 2026-08-21

Related: [ADR-0016](adr-0016-quantifiers-binder-representation.md),
[ADR-0111](adr-0111-shared-incremental-ematching-session.md).

## Context

[`gap-analysis-smt-solvers-2026-08-21.md`](../../plan/gap-analysis-smt-solvers-2026-08-21.md)
§5 records that the quantifier *sat-direction* is closed (quantified LIA 12/12,
BV 54/54) and that what remains against Z3 is triggers: `:pattern` reached
`parse.rs` and was discarded with the comment "annotations … are hints we drop",
and `:weight` did not exist. Any Z3 workload whose quantifier performance rests
on hand-written triggers therefore had no path here — not a degraded one, none.

Measured on this host with `z3` 4.13.3, one file in two spellings:

```
(assert (= (h a) b))
(assert (forall ((x U)) (= (f x) a)))                             ; and, annotated:
(assert (forall ((x U)) (! (= (f x) a) :pattern ((h x)))))
(assert (not (= (f b) a)))
```

With Z3's own fallbacks off (`smt.mbqi=false smt.auto_config=false`) the
unannotated file is `unsat` and the annotated one is `unknown`: `(h x)` reaches
only `h a`, so it proposes `x := a` and never the instance that refutes. Axeyum
returned `unsat` for both, in both configurations — the annotation could not
change anything, which is exactly the gap.

## Decision

### 1. The annotation lives on the arena, not in the term

`TermArena` gains `quantifier_patterns: BTreeMap<TermId, Vec<Vec<TermId>>>`,
written by `set_quantifier_patterns` and read by `quantifier_patterns`. The
outer vector is a list of **alternatives**; each inner vector is one
**multi-pattern**.

Not an `Op::Forall` payload, and not a new node. A trigger is not part of what a
quantifier means — `(! B :pattern (p))` and `B` are the same formula — so
putting it in the term would make two identical formulas intern to two terms and
would put a performance hint inside the interning key, where every consumer that
compares or evaluates terms would have to learn to ignore it. `eval` does not
read the table; the interner does not key on it; a rebuilt identical `forall`
returns the identical `TermId`, annotation and all.

The arena is the right carrier because it is what is already threaded, by `&mut`
reference, from the parser to every solver route. A side table on `Script` would
have stopped at the front door.

**The hazard this design invites, and why it does not fire.** A table keyed by an
interned `TermId` cannot distinguish two source quantifiers that intern to one
term — one annotation would silently overwrite the other. It does not happen
because `fresh_quantifier_symbol` mints a uniquely-named binder symbol per
occurrence, so two syntactically identical `forall`s are already two terms. That
property is now load-bearing for something other than capture-avoidance, so it
is pinned by a test rather than left as a comment.

### 2. A usable annotation *replaces* auto-selection

Not "adds to". Replacing is what makes the annotation mean what its author
wrote; adding would keep the auto-selected trigger firing and quietly ignore the
author's restriction, which is the behaviour this ADR exists to end.

Replacing is also the only direction that can cost anything, and what it costs
is **completeness**: fewer proposed instances, so `unsat` can become `unknown`.
That is exactly what Z3 does on the file above. It is not a soundness risk, for
a reason that is structural rather than argued:

> Every instance the loop admits is `replace_subterms(body, x⃗ ↦ t⃗)`, and
> `∀x⃗. B ⊨ B[x⃗ := t⃗]` holds for **every** ground `t⃗`. The entailment is a
> property of `B` alone; it cannot depend on how `t⃗` was chosen. A trigger's
> only output is a substitution.

So a trigger *proposes*; it never *justifies*. Nothing downstream may read "a
trigger matched" as a reason an instance is entailed, and nothing can, because
the two are separated by construction: the matcher hands the driver a tuple of
ground terms and nothing else.

### 3. Alternatives are disjunctive, multi-patterns conjunctive

`CompiledUniversal` gains `pattern_groups: Vec<Vec<usize>>` beside the existing
flat `pattern_indices`. The join runs per group and the tuple sets are unioned;
within a group the substitutions are merged as before. One auto-selected trigger
set is one group, so the single-group path is byte-identical to the historical
join, including its budget. The shared join budget is threaded across groups
rather than reset per group, so N alternatives cannot buy N times the work.

Keeping these as two separate structures is not decoration. Measured on the file
above: `:pattern ((h x)) :pattern ((f x))` proposes both instances, while
`:pattern ((h x) (f x))` proposes **none** — `h x` binds only `x := a` and `f x`
only the class of `b`, and the intersection is empty. Collapsing alternatives
into one multi-pattern would have turned the first into the second.

### 4. What is declined, explicitly

Silently ignoring an annotation is the behaviour being fixed, so every case the
matcher cannot fire is dropped *whole* and falls back to auto-selection, leaving
the quantifier exactly where it was before annotations existed.

Declined in the parser (`build_trigger_term`): anything that is not an
application tree over declared uninterpreted functions whose leaves are bound
variables or declared constants — an interpreted operator, an indexed
identifier, a `define-fun` macro, a nested binder, a literal, or a term nested
past `MAX_TRIGGER_DEPTH`. Trigger terms are built directly rather than queued
through the frame machine precisely so that a pattern that cannot be built
declines instead of failing a parse that succeeds today.

Declined in the solver (`usable_trigger_groups`): an alternative containing a
non-application (`Pattern::Var` carries no root declaration, so `patterns_by_root`
can never schedule it); an alternative whose terms do not *jointly* bind every
variable of the universal (every tuple it could produce has an unbound slot,
which the join discards — it would starve the universal rather than trigger it);
and an alternative naming a binder variable this universal does not bind (that
symbol freezes into a constant no ground term equals, so the pattern would
compile and never fire).

### 5. `:weight` is not implemented

Deliberate, and cheap to state. The flood-control cost function in
`qinst_egraph.rs` orders deferred instances by *generation* alone, where Z3's
`qi_queue.cpp` uses `(+ weight generation)`. Adding a per-quantifier weight to
that sum is a small change, but it is a change to the one lever measured to
decide files in both directions (`FLOOD_EAGER_GENERATION_MAX` exists because
capping an early dump lost a 4 s `unsat`), and nothing in the corpus exercises
it: **0 of 1430 tracked `.smt2` files contain `:weight`, and 0 contain
`:pattern`.** A tuning knob nothing measures is a knob that will be tuned by
guesswork. It stays out until there is a corpus that moves under it.

## Consequences

- The committed corpus contains no `:pattern`, so the measured capability delta
  on it is exactly zero — by construction, not by luck. This feature is entirely
  about input from outside our corpus, and that should be said whenever its
  value is asserted.
- Obeying a useless trigger did **not** cost the refutation on the file above,
  because the loop's term invention seeds ground instances of the trigger itself
  and reaches `x := b` anyway. Z3 with `smt.mbqi=false` has no analogue. So the
  completeness cost is real in principle and absorbed here in practice — which
  is why the tests measure the proposed *instance set*, the direct observable of
  a trigger, and not the verdict, which several other routes can also reach.
- **Whether an annotation reached the loop is not otherwise observable**, so
  `AXEYUM_QPROBE=1` now prints `user-triggers vars=N written=W used=U` per
  annotated universal — including `used=0`, the declined case, which is the one
  that looks like success from the outside. Measured through the shipped front
  door on the motivating files: `written=1 used=1`, and `written=2 used=2` for
  two alternatives. The annotation survives the front door's rewriting and
  reaches `run_egraph_quantified_fallback`; it does **not** survive
  skolemization, which mints new terms, so the second (skolemized) e-graph pass
  in `auto.rs` runs on auto-selected triggers. That is a known and deliberate
  boundary, not an oversight: carrying annotations across a term rewrite needs
  the rewriter to be annotation-aware, which is a separate change.
- **The alternative-union path was live and unguarded for one round of testing.**
  Deleting it — forcing the historical flat conjunctive join — killed **zero**
  tests, because the only test exercising alternatives went through the one-shot
  `instantiate_forall_via_egraph` and not through the session's
  `witness_tuples_with_overrides`, which is the path the shipped loop runs. Two
  code paths, one tested. `the_session_unions_alternatives_instead_of_intersecting_them`
  now covers the second.
- `witness_tuples_via_egraph` and `instantiate_forall_via_egraph`, the public
  one-shot APIs, honour annotations too. Their documented contract of "the
  complete match set" now means complete *for the trigger in force*, which for
  an annotated quantifier is the author's.
