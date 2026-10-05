# Lane: resolve-kernel-subjects — the trust-closure `unresolved` population is not one thing

<!-- plan-section: lane-status -->

**Done (`resolve-kernel-subjects`, 2026-08-31).** `scripts/check-trust-closure.py`'s
`unresolved` count moved **90 -> 62** (live, rebuilt `kernel_declaration_projection`,
both measured with `--json`, `failures=0` both times). Ratio
`subjects/kernel_facts`: **0.9586 -> 0.9714**, against a floor of 0.9579.
Headroom before the L0 gate reds: **1 fact -> 29 facts.** No `min_ratio` or
other floor was touched.

**But the brief's "9 deliberate + 81 recoverable" framing does not survive
contact with the data, and reporting that correction is most of this lane's
value.** Investigating all 90 found three structurally different reasons a
fact lands in `unresolved`, only one of which "annotate the evidence" fixes:

| bucket | count | fix |
| --- | --- | --- |
| genuinely under-annotated (declaration exists, persistently, in the environment `kernel_declaration_projection` walks; evidence already spells it) | **28** | annotated this lane, `formal.kernel_theorem` |
| explicit `formal.kernel_theorem: null`, self-documented multi-theorem bundle | **7** | left alone (correct) |
| checked through an **ephemeral, isolated** `Kernel::add_declaration` instance that is created for one receipt check and discarded — the Mathlib-style dotted name is VERIFIABLY ABSENT from the persistent environment | **~36** (`ml430-*` facts with `axeyum-lean-import/sealed-kernel-capsule-v1`, `modeq-family-*`, `imported-candidate-*`, `conclusion-directed-transport-v1`, `bounded-induction-*`, `checked-dependency-theorem-receipt-v1` drivers) | **not annotated** — see below |
| genuine multi-theorem bundle / meta-fact / per-query ad hoc reconstruction, same shape as the 7 explicit-null but never marked | **~19** | **not annotated** — candidates for `kernel_theorem: null`, judgement calls not made mechanically this lane |

## What was actually recoverable, and how it was verified

28 facts had their declaration spelled in their own evidence and that
declaration is a real, persistent member of the environment
`kernel_declaration_projection` walks. Recovery used three tiers, in priority
order, each airtight enough to trust automatically:

1. **Title match** — the `ml430` mirror convention's title
   `"Mathlib v4.30 source proposition <Name>"`, accepted only when `<Name>`
   is a `theorem`-kind declaration in the environment (11 facts).
2. **Evidence-id match** — an evidence entry whose `id` begins `kernel-<Name>`,
   accepted only when unambiguous and `<Name>` is `theorem`-kind (13 facts).
3. **Exact type match** — `formal.statement` (for `formal.language == "lean4"`
   facts, already in `Kernel::render_lean` form), optionally stripped of a
   leading `def <Name> : ` / `theorem <Name> : `, compared BYTE-FOR-BYTE
   against every declaration's `canonical_type`, any kind. This is not a name
   heuristic — it is the actual rendered type — and it is what correctly
   resolved `F:rat-normalize-reduces` to the **Definition** `Rat.normalize`
   (4 facts total this tier, including 2 the id-tier left ambiguous).

**A fourth, wider tier — scanning the whole fact's JSON text for any
namespaced dotted name that happens to exist as a theorem — was tried and
explicitly rejected.** It produced plausible-looking but WRONG answers on 5
of the 90: it named `Nat.mul_comm` the subject of
`F:ml430-nat-gcd-fib-add-self-5a92d5e3` and `Int.add_neg_cancel_right` the
subject of `F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d` — both
are dependency theorems mentioned in `supports`/`notes` prose, not the fact's
actual subject. This is the exact "candidate resolved by DEPENDENCY MENTION,
not by SUBJECT identity" failure mode, and it is why the shipped tool has no
such tier (see its module docstring). It is also the mistake CLAUDE.md's
`Nat.ascFactorial` warning describes from the other side: an early draft that
included `Definition`s in the theorem-name candidate pool would have
mis-annotated `F:ml430-nat-one-ascfactorial-8bacb017` with `Nat.ascFactorial`
(the Definition) instead of correctly leaving it unresolved, because its real
subject `Nat.one_ascFactorial` does not exist under that name.

Every one of the 28 was spot-verified before applying: for the 13 `lean4`-language facts,
`formal.statement` was compared **byte-for-byte** against the candidate's
`canonical_type` (2 needed a `"theorem <Name> : "` prefix strip, both
confirmed as pure formatting, not content, differences); for the 11 `ml430`
title-matched facts, one (`Int.add_modEq_left`) was hand-verified against its
Mathlib surface statement (`n + a ≡ a [ZMOD n]` vs. the rendered
`Int.ModEq x0 (Int.add x0 x1) x1`) before trusting the pattern for the rest.

## The tool: `scripts/annotate-trust-closure-kernel-theorem.py`

Re-runnable, `--check`/`--apply`, exit status depends on the finding
(`--check` exits 1 iff an unambiguous unapplied candidate exists). Verified
live:

```
$ python3 scripts/annotate-trust-closure-kernel-theorem.py --check
trust-closure unresolved: 62
unambiguous, unapplied theorem-kind candidates: 0
```

**Proof the gate still fires, done in `scripts/lane-snapshot.sh` scratch
copies, never the shared checkout:** copied the fixed
`F:wilson-theorem-over-constructed-integers` and `F:rat-normalize-reduces`
into a pre-fix snapshot (`unresolved` 90 -> 88, confirming both resolve
correctly); then stripped `formal.kernel_theorem` back off the Wilson fact
(simulating a regression / a landing that forgets the annotation) and
re-ran `check-trust-closure.py` against the SAME cached projection:
`unresolved` went back to 89. The tool's own `--check`, run against that same
mutated snapshot, correctly re-listed `F:wilson-theorem-over-constructed-integers
-> Int.wilson` among 27 unapplied candidates. Both the L0 gate and this
lane's ratchet genuinely discriminate a re-introduced under-annotation.

**Mutation-verified control suite:**
`scripts/tests/test-annotate-trust-closure-kernel-theorem.sh` — 11 cases (3
positive recovery tiers, 3 negative controls: dependency-only mention,
ambiguous evidence ids, an explicit deliberate-null fact left untouched;
apply-then-reverify-clean; the null field's exact value preserved), one
mutation (delete the evidence-id tier) that kills exactly one case. Not
wired into `check.sh`/`justfile` this lane — that is a judgement call about
whether every future landing should be gated on this, left to whoever adopts
it as a standing check.

## Consequence found and fixed: `check-fact-depends-derived.py` drift

Setting `formal.kernel_theorem` also feeds `check-fact-depends-derived.py`'s
own `theorem_of()` (same priority-1 field, shared convention) — so the 28
newly-named facts went from `check-fact-depends-derived.py`'s silent
`unnamed` set into its enforced set, and their real (pre-existing, always
true) proof-term dependencies were suddenly checkable against `depends_on`.
`python3 scripts/check-fact-depends-derived.py --fix` (its own documented
remedy) added **196 missing edges across 54 facts** — most of them NOT among
the 28 (e.g. `F:cpoint-distsq-triangle-sq-bound` needed
`F:cauchy-schwarz-over-constructed-plane` added, because it always used that
theorem and could never be checked for it before the theorem had a name).
`python3 scripts/validate-facts.py` is clean (0 errors) after the fix.
**This is not scope creep** — annotating a fact's subject is exactly what
unlocks the dependency check that already existed for it; leaving the drift
unfixed would have left `validate-facts.py` newly red.

## The bigger finding: ~55 of the remaining 62 are not annotation bugs

**The `ml430-*` ephemeral-capsule facts (~36) cannot be honestly marked
`kernel_theorem: null` — that field's OWN documented meaning is "not about
exactly one kernel theorem," and these facts genuinely ARE about exactly one
theorem (e.g. `Int.fib_add_two`, `Nat.gcd_greatest`).** Their evidence
literally says so via `checker_operation` drivers like
`axeyum-lean-import/sealed-kernel-capsule-v1` whose own checker description
reads *"rebuilds the proof and re-admits it through `Kernel::add_declaration`
in a proof-isolated import"* — a genuinely FRESH kernel instance, created and
discarded per fact, never merged into the persistent environment
`kernel_declaration_projection` walks. Confirmed by direct lookup, not
inferred: `Int.fib_add_two`, `Nat.gcd_greatest`, every `Nat.ModEq.*` /
`Int.ModEq.*` Mathlib-spelling, `Nat.one_ascFactorial`, `Nat.zero_ascFactorial`
— all VERIFIABLY ABSENT from the live projection (2,719 declarations
checked). Forcing `null` onto these would misrepresent a single-subject fact
as a bundle, which is a worse lie than leaving it unresolved. **This is an
architecture gap in `subject_of()`'s three-tier model, not a data-entry gap
in the ledger** — the model has no way to say "about exactly one theorem, no
persistent name" — and closing it is a decision for whoever owns
`check-trust-closure.py`'s design, not a fact-by-fact fix.

**The remaining ~19 non-`ml430` facts are a mix**: genuine multi-theorem
bundles matching the EXISTING 7's self-documenting pattern (e.g.
`F:excluded-middle-not-intuitionistic` names both
`ipc_excluded_middle_not_provable` and `ipc_soundness`;
`F:nra-refutations-reconstruct-over-constructed-reals`'s own title says
"Two ... certificates"), meta-facts about module size or interface structure
rather than about a theorem (`F:lean-query-module-shrinks-by-a-shared-import`,
`F:ordered-ring-interface-is-the-same-over-the-axiom-free-integers`), and
per-query ad hoc Lean reconstructions with no stable declaration name at all
(`F:ordered-ring-farkas-refutation`, `F:schedule-critical-chain-infeasible`,
the `shipped-front-door-*` pair — same architecture as the `AxReal`
demonstrator route CLAUDE.md documents, not a persistent prelude
declaration). These are plausible `kernel_theorem: null` candidates but
marking them was a judgement call this lane chose not to make mechanically
under time budget — a future lane doing that work should read each fact's
`formal.statement`/`title` itself, not infer from this table.

**So the honest headline is: 7 (of the ORIGINAL 90) are deliberately
unresolvable with a field marking it so; roughly 55 more have a REAL reason
they cannot resolve under the current `subject_of()` model, but that reason
is not recorded anywhere machine-checkable** — the brief's "9 deliberate"
count was two facts short even before this lane started, and the true
"deliberate or structurally unresolvable" population, once someone finishes
marking it, is closer to 62 than 9.

<!-- plan-section: landed-changes -->

| 2026-08-31 | | `scripts/annotate-trust-closure-kernel-theorem.py` (`--check`/`--apply`) — recovers `formal.kernel_theorem` for trust-closure facts whose declaration is spelled unambiguously in `title`/evidence `id`/exact type; annotated 28 facts, `unresolved` 90 -> 62, ratio 0.9586 -> 0.9714 (floor 0.9579 unchanged) |
| 2026-08-31 | | `scripts/tests/test-annotate-trust-closure-kernel-theorem.sh` — 11 cases, 1 mutation, kills exactly one |
| 2026-08-31 | | `python3 scripts/check-fact-depends-derived.py --fix` — 196 missing `depends_on` edges added across 54 facts, unlocked by the 28 new `kernel_theorem` annotations; `validate-facts.py` clean |
