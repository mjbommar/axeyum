# Divergences from Lean 4

> Unless specified here, any divergence between this kernel and Lean 4 is a bug.

That sentence is the whole point of this file, and it is copied deliberately
from [lean4lean's `divergences.md`][lean4lean] — the most copyable artifact in
the Lean ecosystem, because it inverts the burden of proof. A kernel that
merely *lists what it has checked* tells you nothing about what it has not. A
kernel that says "everything not on this page is a bug" has made every
unlisted disagreement reportable by anyone.

A ledger nobody enforces is a wish, so this one is gated.
`scripts/check-lean-divergences.py` reads three **authorities**, collects every
divergence they currently report, and fails if this file does not name it. It
carries no list of its own: a checker whose subject is a literal inside itself
measures the maintainer's memory, not the tree.

| authority | key namespace | what it reports |
|---|---|---|
| `artifacts/kernel-conformance/summary.json` ([ADR-1663](../research/09-decisions/adr-1663-the-public-conformance-corpus-scores-both-halves-and-the-divergence-ledger-is-gated.md)) | `conformance:<case>` | every case of the public Lean Kernel Arena corpus whose verdict here is not the corpus's expected outcome |
| `crates/axeyum-lean-kernel/tests/kernel_differential.rs` ([ADR-0780](../research/09-decisions/adr-0780-the-kernel-differential-corpus-finds-real-defects-and-two-guards-survive-uncaught.md)) | `differential:<name>` | every entry of `EXPLAINED_INCOMPLETENESS` |
| `crates/axeyum-lean-kernel/tests/support/creal_representability.rs` ([ADR-0760](../research/09-decisions/adr-0760-independent-replay-is-graded-per-declaration-by-name.md)) | `census:<reason>` | every non-representable class of the replay census |

A fourth kind of entry carries `manual:` keys. Those name divergences no
authority reports automatically — each one states the command that shows it,
and is re-measured rather than inherited. Downgrading a real key to `manual:`
does not hide it: the gate requires the authority's own key, in the authority's
own namespace, to appear somewhere in this file.

**What "Lean" means here.** This project targets Lean's **kernel**, not its
elaborator ([ADR-0517](../research/09-decisions/adr-0517-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md)).
Cross-checks run against the pinned toolchain in `lean-toolchain`
(`leanprover/lean4:v4.34.0-rc1`, [ADR-1594](../research/09-decisions/adr-1594-the-crosscheck-pin-moves-to-lean-4-34-0-rc1-and-follows-the-pin-file.md));
the Mathlib corpus is pinned separately at Lean 4.30.0. A claim about "Lean" in
an entry below means the kernel of the pin the entry names.

---

## Open: we accept something Lean's kernel rejects

These are the entries that matter most. None is a soundness defect in the
sense of admitting `False` — but each one breaks the implication people
actually rely on, *"axeyum checked it, so Lean would check it"*.

### D1 — A `Theorem` whose type is not a proposition

**Status:** open
**Keys:** `conformance:tutorial/012_nonPropThm`, `census:theorem-type-not-prop`, `census:blocked-by-dependency`

Lean's `Lean.Environment.addDeclCore` refuses a `theorem` whose type does not
live in `Prop`; such a thing must be a `def`. This kernel does not make that
distinction, so it admits the arena's `nonPropThm` case — a `theorem` whose
type is `Prop` itself, which is a `Type`, not a proposition.

This is deliberate and load-bearing, not an oversight. `creal/uniform_convergence.rs`
makes `CReal.UniformConvergesOn` `Type`-valued on purpose: `Exists.rec` cannot
eliminate into `Type`, so a convergence *rate* has to be data. The replay
census grades the consequence per declaration by name rather than hiding it in
an aggregate: of a `creal` population of 2,045, **48** are `Type`-valued
theorems Lean's kernel refuses as theorems and **25** more are blocked behind
them ([ADR-0760](../research/09-decisions/adr-0760-independent-replay-is-graded-per-declaration-by-name.md)).
`census:blocked-by-dependency` is the second-order class: those declarations do
not diverge on their own account, only through a dependency that does.

**Consequence to state whenever the replay number is quoted:** a `Type`-valued
theorem of ours is a `def` of Lean's. It is not unprovable there, and it is not
wrong here; it is a different declaration kind, and the census counts it as
non-representable rather than as replayed.

**Re-measure:** `cargo test -p axeyum-lean-kernel --test real_lean_replay_census`
(prints `AXEYUM-REPLAY-CENSUS ... theorem_type_not_prop=N blocked_by_dependency=N`).

### D2 — Duplicate universe parameters on one declaration

**Status:** open
**Keys:** `conformance:tutorial/019_tut06_bad01`

The arena case declares a `def` with `levelParams := [u, u]`. Lean rejects it;
this kernel admits it. A duplicated parameter makes instantiation ambiguous —
`@f.{a, b}` has two candidate substitutions for the same name — so nothing
downstream can be relied on to mean one thing.

Bounded and closable: the check belongs at the trusted gate beside the existing
one that requires a recursor's universe parameters to be bound
(`crates/axeyum-lean-import/tests/recursor_universe_params_must_be_bound.rs`).
Not closed here because it is a change to `Kernel::add_declaration`'s admission
rules, which every prelude in the tree runs through, and this lane's remaining
budget could not carry both the change and the full kernel-suite re-run its
soundness class requires.

**Re-measure:**
`target/release/examples/kernel_conformance_check references/lean-arena-tests/bad/tutorial/019_tut06_bad01.ndjson`
(exits 0 = accepted; Lean rejects).

### D3 — Universe-level equality is *more complete* than Lean's

**Status:** open, sanctioned upstream
**Keys:** `manual:probe5-imax-assoc`, `manual:max-to-imax`

Lean decides universe equality by normalization, and those rules are provably
incomplete. Trepplein and Carneiro's thesis case-split instead and are more
complete. [ADR-0036](../research/09-decisions/adr-0036-lean-kernel-crate.md)
ports `leq_core` from nanoda, which is in the trepplein lineage, so this kernel
inherits the more complete position.

**Re-measured 2026-09-05, first-hand, not inherited**
(`cargo run --release -p axeyum-lean-kernel --example level_conformance_probe`):

```
LEVEL-PROBE name=probe5-imax-assoc lhs=imax(u,imax(v,w)) rhs=imax(max(u,v),w) axeyum=true lean=false verdict=more-complete-than-lean
LEVEL-PROBE name=max-to-imax     lhs=max(u,1)           rhs=imax(u,1)         axeyum=true lean=false verdict=more-complete-than-lean
LEVEL-PROBE name=negative-control lhs=imax(0,v)         rhs=succ(imax(0,v))   axeyum=false lean=false verdict=agree
LEVEL-PROBE name=positive-control lhs=max(u,v)          rhs=max(v,u)          axeyum=true lean=true  verdict=agree
```

Both probes report `true`, which is what a degenerate `|_, _| true` would also
print, so the example carries both controls: the negative one is the very shape
the arena's `level-imax-normalization` case exploits to derive `False`, and it
answers `false`.

- `probe5-imax-assoc` is Carneiro's example from §2.6 Probe 5 of the
  [kernel requirements](lean-kernel-requirements-2026-08-13.md): *"rejected by
  leanchecker but accepted by trepplein"*.
- `max-to-imax` is the shape of the open mutant
  `level.max-kind:1322:max-to-imax` that [ADR-1600](../research/09-decisions/adr-1600-the-kernels-metatheoretic-status-what-is-trusted-and-what-is-not.md)
  §4 records the Lean 4.34.0-rc1 cross-check as red on. The two levels are equal
  for every `u` because the right operand is a successor; Lean's C++ `normalize`
  sorts one spelling and not the other, so `is_equivalent` answers no **on the
  wire** while both kernels accept the same thing written in source.

**ADR-1600 left the resolution open — record an exemption, or make this kernel
as incomplete as Lean's. This ledger records the exemption, on upstream's own
evidence.** `leanprover/lean-kernel-arena` classifies exactly this shape as
`outcome: either` (`tests/corner-cases/imax-right-successor.yaml`): *"A checker
may reject these hand-crafted exports using a more conservative normalization,
or accept them by recognizing that the right operand is nonzero."* An `either`
outcome is the corpus saying that checkers may legitimately differ here. Making
a correct decision procedure deliberately incomplete to imitate a difference
the reference corpus does not consider a defect is the wrong trade, and it
would be a change to the soundness-critical core.

What follows from it, and must be said wherever completeness is claimed: **this
kernel accepting a term does not imply Lean's kernel accepts it.** The
implication holds in the other direction on everything measured so far
(`stricter_than_lean=0` across 291 mutants, ADR-1600 §4).

### D4 — `unsafe` and `partial` declarations are declined, not rejected

**Status:** open, deliberate
**Keys:** `conformance:tutorial/141_falseFromUnsafe`, `conformance:tutorial/142_falseFromPartial`

Both arena cases derive `False` from an `unsafe`/`partial` declaration and are
`bad`. Lean rejects them. This kernel *declines* them
(`ImportError::Unsupported`, code `declaration-unsafe-or-partial`, arena exit
code 2), which is not the same answer: a decline says "I will not judge this",
a reject says "this is invalid".

Declining is the fail-closed choice and is the right default — nothing unsafe
or partial can enter the trusted environment through this route — but it is
scored honestly in its own column and never inside a pass rate. Two of the
73 reject-half cases are declines, and the reject half is reported as
69 correct / 2 declined / 2 wrong rather than as a percentage.

---

## Open: we reject something Lean's kernel accepts

Incompleteness, not unsoundness. Each one costs interoperability, none costs
trust.

### D5 — No unit-like definitional equality

**Status:** open
**Keys:** `conformance:tutorial/107_unitEta1`, `conformance:tutorial/108_unitEta2`

Lean's definitional equality has a unit-like rule: a structure with one
constructor and no non-proof fields is definitionally equal to its unique
inhabitant, so `x ≡ ⟨⟩` for any `x` of such a type. This kernel does not
implement it, and both arena cases fail with
`KernelError::DeclarationValueMismatch`.

§4.6 of the [kernel requirements](lean-kernel-requirements-2026-08-13.md)
listed this as a known gap sourced from an agent audit and predicted it would
block *"a block of conformance tests"*. Measured against the real corpus, it
blocks exactly two, and they are the only two conformance cases this kernel
rejects for a reason inside the trusted gate.

### D6 — Internalization indices must be dense and ascending

**Status:** open
**Keys:** `conformance:core/level-index-out-of-order`

`lean4export` assigns `in`/`il`/`ie` indices contiguously in order, and this
kernel's reader requires that, treating them as array positions. The format
spec merely requires them to be integers, and the arena's case asserts that a
kernel must handle skipped or out-of-order indices: it defines level `2` before
level `1`, which is a valid encoding of `axiom foo : Sort 2`. We reject it as
`Malformed`.

Closable by keying the internalization tables by declared index rather than by
position, while keeping the fail-closed property that a reference to an
*undefined* index is still an error. Not closed here: it is a change to the
reader's topology guards, which are the importer's fail-closed core.

### D7 — Only `lean4export` may have written the stream

**Status:** open, deliberate
**Keys:** `conformance:core/sparse-name-index`

The reader rejects any stream whose `meta.exporter.name` is not `lean4export`.
The arena's `sparse-name-index` case is hand-crafted and declares
`"exporter": {"name": "handcrafted"}`, so we reject it at line 1 as `Malformed`
and never reach the sparse-index property it exists to test.

This is a provenance policy, not a format limitation, and it is deliberate: an
import is labeled scaffolding whose provenance is part of its label
([ADR-0601](../research/09-decisions/adr-0601-three-producers-one-trust-anchor.md)).
It is recorded because the corpus's expected outcome is `accept` and ours is
`reject`, and because it means D6's underlying property is **untested here** —
the only corpus case that exercises sparse *name* indices is refused before the
question is asked.

### D8 — A performance case does not terminate

**Status:** open
**Keys:** `conformance:perf/app-lam`

`good/perf/app-lam` is an arena performance case (1.2 MB of export, built to
stress a reduction strategy). The official kernel checks it. This kernel
produced **no verdict in 600 s**, at 3.0 GB peak RSS, measured with
`/usr/bin/time -v` on the dev box; the gate's own per-case budget is 30 s and
records it as `timeout`.

Recorded as a divergence rather than as a benchmark line because a checker that
cannot finish has not accepted anything. The other 15 performance cases in the
corpus pass, the slowest (`grind-ring-5`, 10.2 MB) in 8.1 s.

---

## Closed

### D9 — `PSigma` was admitted at `Sort (max u v)`

**Status:** closed
**Keys:** `manual:psigma-sort-level`

Lean requires `PSigma : Sort u → Sort v → Sort (max 1 u v)`; this kernel
admitted it at `Sort (max u v)`, which is wrong at `u = v = 0` (a `PSigma` of
two propositions is not a proposition). Found by a real-Lean gate on
2026-09-03 and fixed the same week in `c0054fd3b`.

Kept here rather than deleted: a ledger of divergences that only ever grows is
a list of excuses, and a closed entry is the evidence that entries can leave.

---

## Not a divergence, and why

Two things are regularly mistaken for entries in this file.

**The elaborator.** Lean has two checkers, and this project targets the kernel
([ADR-0517](../research/09-decisions/adr-0517-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md)).
Everything Lean's *elaborator* enforces and its kernel does not — implicit
argument synthesis, instance resolution, the `variable` block's coercions,
syntactic well-formedness of surface syntax — is out of scope by construction.
A source file Lean's elaborator rejects and this kernel's importer accepts is
not a divergence, because the importer never sees source: it reads
`lean4export` NDJSON, which is already elaborated.

**`Quot.sound`.** The kernel differential registers
`differential:quotient::quot_sound_absent` as an explained incompleteness, and
it is listed below so the gate is satisfied, but it is a *deliberate absence of
a primitive*, not a disagreement about a shared rule.

### D10 — `Quot.sound` is not a primitive here

**Status:** open, deliberate
**Keys:** `differential:quotient::quot_sound_absent`

This kernel implements exactly Lean's four-declaration quotient package —
`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` — and deliberately has no
`Quot.sound` ([ADR-1595](../research/09-decisions/adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md);
see the module docs of `creal.rs`, `int_prelude.rs`, `rat_prelude.rs`). Lean's
kernel treats `Quot.sound` as a fifth built-in primitive, so a term citing it is
trivially accepted there and rejected here — the name does not exist.

Imported declarations carry `Quot.sound` in their footprint and are labeled as
such; they are never counted as ours
([ADR-0601](../research/09-decisions/adr-0601-three-producers-one-trust-anchor.md)).

---

## How to re-measure the whole ledger

```sh
# the corpus, both halves, and the control (ADR-1663)
python3 scripts/check-kernel-conformance.py --self-test
python3 scripts/check-kernel-conformance.py --require-corpus --rerun

# this file, against the three authorities
python3 scripts/check-lean-divergences.py --self-test
python3 scripts/check-lean-divergences.py

# the level shapes of D3, with both controls
cargo run --release -p axeyum-lean-kernel --example level_conformance_probe

# the differential and the replay census
python3 scripts/check-kernel-differential.py
cargo test -p axeyum-lean-kernel --test real_lean_replay_census
```

[lean4lean]: https://github.com/digama0/lean4lean/blob/master/divergences.md
