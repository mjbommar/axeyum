# Footprint closure audit — does `axiom_footprint` see everything a theorem rests on?

2026-08-23. Diagnostic-only; nothing under `crates/axeyum-lean-kernel/src/` or
`artifacts/` changed. Instrument:
[`crates/axeyum-lean-kernel/examples/footprint_closure_audit.rs`](../../crates/axeyum-lean-kernel/examples/footprint_closure_audit.rs).

## Headline

**0.** Across every theorem in every prelude this audit covers (2,334
(theorem, prelude) rows, 41 of them touching the mechanism under test), **zero**
have an empty narrow (`axiom_footprint`-equivalent) trusted footprint and a
non-empty widened one. The suspected gap is real as a *mechanism* — the edge
set genuinely differs on 41 distinct theorems — but in every occurrence
observed here, the extra edges land on a non-trusted declaration
(`Constructor`), never on an `Axiom`, `Opaque`, or `Quotient`. The published
axiom-freedom claim is **not affected** by this gap for the preludes this
audit covers.

## The question and the mechanism

`Kernel::axiom_footprint` (`crates/axeyum-lean-kernel/src/lean_pp.rs:1297`)
walks `decl_deps`, which for an `Inductive` collects only the constants in the
inductive's **own type** — deliberately, per its doc comment: a constructor's
type is not what a proof rests on unless the proof mentions the constructor.
The module renderer needs a wider edge set for a different reason (a rendered
`inductive` command must declare its constructors inline, so it needs their
types' dependencies too) and gets it via a separate function, `render_deps`,
that `axiom_footprint` deliberately does not use.

The suspicion: if a proof uses an inductive family **as a type** without ever
mentioning a constructor, and a constructor's type (or the family's
recursor's type — one step further than `render_deps`, which widens only for
constructors) reaches a trusted declaration, `axiom_footprint`'s closure never
sees that edge, even though the family's well-formedness depends on it. This
audit measures whether that is reachable in this repository's actual
preludes, not just in principle.

## Method

`footprint_closure_audit.rs` reimplements `decl_deps` and the BFS closure
`axiom_footprint` uses, entirely over the crate's **public** surface
(`environment()`, `expr_node`, `Declaration::ty`/`value`, `anon`/`name_str`) —
it never calls or edits the private `lean_pp.rs` functions. For every prelude
`prelude_theorem_inventory.rs` builds (`logic`, `nat`, `axreal`, `integer`,
`rat`, `string`, and under `--include-constructed`: `creal`, `complex`,
`cpoint`) and every admitted `Theorem`, it computes:

- **narrow**: the closure exactly as `axiom_footprint`/
  `declaration_dependency_closure` compute it.
- **widened**: the same closure, except at every `Inductive` node the edge
  function also follows the constants in its constructors' types **and** its
  recursor's type (`render_deps` only does the constructor half).

**Fidelity is checked, not assumed.** For every one of the 2,334 rows, the
reimplementation's narrow-trusted set is asserted equal to
`Kernel::axiom_footprint`'s own answer, and its full narrow closure is
asserted equal to `Kernel::declaration_dependency_closure`'s own answer
(`assert_eq!`, aborts the run on any mismatch). The run completed with exit
status 0 both with and without `--include-constructed`, so every one of those
assertions held — this is not a reimplementation whose correctness is taken
on faith.

## Per-prelude table

| prelude | theorems | headline gap | edge-diff precondition (theorems) | `Opaque` decls | `Quotient` decls | union closure composition | dangling refs |
|---|---:|---:|---:|---:|---:|---|---:|
| logic   | 12  | 0 | 0  | 0 | 0 | Constructor=6, Definition=2, Inductive=6, Recursor=6 | 0 |
| nat     | 182 | 0 | 15 | 0 | 0 | Constructor=14, Definition=26, Inductive=11, Recursor=10, **Theorem=116** | 0 |
| axreal  | 12  | 0 | 0  | 0 | 0 | Constructor=6, Definition=2, Inductive=6, Recursor=6 | 0 |
| integer | 270 | 0 | 31 | 0 | 0 | Constructor=17, Definition=44, Inductive=13, Recursor=12, Theorem=177 | 0 |
| rat     | 389 | 0 | 37 | 0 | 0 | Constructor=17, Definition=57, Inductive=13, Recursor=12, Theorem=280 | 0 |
| string  | 16  | 0 | 4  | 0 | 0 | Constructor=8, Definition=3, Inductive=8, Recursor=7 | 0 |
| creal   | 470 | 0 | 37 | 0 | 0 | Constructor=18, Definition=84, Inductive=14, Recursor=13, Theorem=355 | 0 |
| complex | 494 | 0 | 37 | 0 | 0 | Constructor=19, Definition=96, Inductive=15, Recursor=14, Theorem=360 | 0 |
| cpoint  | 489 | 0 | 37 | 0 | 0 | Constructor=19, Definition=95, Inductive=15, Recursor=14, Theorem=368 | 0 |

"Union closure composition" is the declaration-kind histogram of the union of
every theorem's *narrow* closure in that prelude — i.e. what the DAG actually
bottoms out into. Across all nine preludes it bottoms out in `Constructor`,
`Definition`, `Inductive`, `Recursor`, and (once the closure reaches enough of
the library) `Theorem` — **never** `Axiom`, `Opaque`, or `Quotient`. That
includes `axreal`: its 12 theorems (identical to `logic`'s — `axreal` proves
no new theorem of its own over the 30 axioms it declares) never reach any of
the 30 `AxReal.*` axioms, independently reconfirming ADR-0509's "declared is
not reached" from a different code path than the one that first established
it.

Across every one of the 2,334 rows, columns for narrow-trusted and
widened-trusted names were empty (0 rows with either nonempty) — this audit
independently reconfirms, via its own closure walk rather than by trusting
`axiom_footprint`, that no theorem in any of the nine preludes rests on any
`Axiom`/`Opaque`/`Quotient` at all, narrow or widened.

## Secondary finding: the edge-set precondition is real and not rare

41 distinct theorems (across the union of all nine preludes) have at least
one inductive in their narrow closure whose constructor types or recursor
type reach outside that closure — the precondition for the headline gap. Only
four inductive families ever trigger it anywhere in the corpus:

| family | extra names introduced | source |
|---|---|---|
| `Nat` | `Nat.zero`, `Nat.succ` | recursor type only (`ctor=[]` every time) |
| `Nat.le` | `Nat.le.refl`, `Nat.le.step`, occasionally `Nat.succ` | almost entirely the recursor type; one case (`Nat.le_refl`) also picks up `Nat.succ` via a constructor type |
| `True` | `True.intro` | recursor type |
| `axeyum.string.2.Char` | `Char.c0`, `Char.c1` | recursor type |

The audit attributes each extra name to its source (constructor type vs.
recursor type) separately. **The recursor's type is overwhelmingly the
source** — `ctor=[]` in all but one of the 41 rows — which is exactly the
"one step further than `render_deps`" the task asked this audit to check:
`render_deps` (the module renderer's edge set) widens only for constructors
and would have missed nearly all of this.

Representative rows (`Nat.le_refl` pulls in the most, from two different
families in the same closure):

```
Nat.le_refl	Nat:[ctor=[];rec=[Nat.succ;Nat.zero]]|Nat.le:[ctor=[Nat.succ];rec=[Nat.le.step;Nat.succ]]
Nat.le_succ_succ	Nat:[ctor=[];rec=[Nat.zero]]
Nat.lt_add_one	Nat.le:[ctor=[];rec=[Nat.le.step]]
axeyum.string.2.append_assoc	axeyum.string.2.Char:[ctor=[];rec=[axeyum.string.2.Char.c0;axeyum.string.2.Char.c1]]
```

**Why the mechanism never reaches a trusted declaration here**: every extra
name introduced by widening is itself a `Constructor` of an ordinary,
axiom-free inductive (`Nat.zero`/`Nat.succ`/`Nat.le.refl`/`Nat.le.step`/
`True.intro`/`Char.cN`) — never a name that resolves to `Axiom`, `Opaque`, or
`Quotient`. The one prelude that *does* declare axioms (`axreal`, 30 of them)
shows **zero** occurrences of the precondition at all (`inductive_edge_diff_theorems=0`
in the table above): none of its 12 theorems touch an inductive whose
constructor/recursor types reach anything outside their narrow closure in the
first place. So the reason the gap doesn't fire is not "the precondition
never occurs" (it occurs on 41 theorems) — it's that, in this codebase, the
precondition and "the widened target is trusted" have never co-occurred.
That is a fact about the current preludes, not a structural guarantee; a
future inductive whose recursor type mentions an `Axiom`/`Opaque`/`Quotient`
declaration and which some proof uses only abstractly would reproduce exactly
the gap this audit was built to look for.

## Secondary finding: no `Opaque` or `Quotient` declarations, confirmed independently

`opaque_decls` and `quotient_decls` are both 0 in all nine preludes,
confirmed by directly scanning `Environment::iter()` for
`Declaration::Opaque`/`Declaration::Quotient` — a code path independent of
`nat_axiom_inventory` and the Lean axiom ledger. This corroborates the
ledger's claim ("axreal: axiom=30" is the only nonzero row) via a second,
independently-written instrument.

## Secondary finding: zero dangling references

`union_dangling` is 0 in every prelude, and no individual theorem row (2,334
of them) had a nonzero narrow- or widened-dangling count. A "dangling"
reference is a constant some declaration in the closure mentions that
resolves to nothing in the environment at all — this audit counts those
separately rather than silently treating an absent declaration as "no
dependency" (as the task specification required). None occur in the current
preludes.

## What this establishes, and what it does not

**Establishes:**
- The narrow-vs-widened gap `axiom_footprint` is theoretically exposed to
  does not currently affect any theorem in `logic`, `nat`, `axreal`,
  `integer`, `rat`, `string`, `creal`, `complex`, or `cpoint`.
- The precondition for the gap (an inductive's constructor/recursor edges
  reaching outside a theorem's narrow closure) is real and occurs on 41
  theorems, not zero — so this is a measured absence of *co-occurrence* with
  a trusted target, not a claim that the mechanism can't exist.
- The reimplementation used to measure this agrees with
  `Kernel::axiom_footprint` and `Kernel::declaration_dependency_closure` on
  every one of 2,334 rows (checked by `assert_eq!`, not assumed).
- Independent (from a different code path) reconfirmation that all nine
  preludes report `Opaque`/`Quotient` = 0, and that `axreal`'s 30 axioms are
  unreached by any of its own theorems.

**Does NOT establish:**
- Anything about the kernel's own reduction and typing rules — β/η/δ/ι/ζ,
  proof irrelevance, strict positivity, universe constraints, elimination
  restrictions. Those justify every non-leaf node in this graph and are
  entirely outside it; they are checked by differential replay against
  official Lean 4.30.0, not by this audit.
- Anything about preludes this audit doesn't build (only the nine
  `prelude_theorem_inventory.rs` covers). An empty result from a tool never
  pointed at a subject is not evidence about that subject.
- That the gap is structurally impossible. It is a live mechanism this audit
  now measures on every future prelude change; a new inductive whose
  recursor/constructor types reach a trusted declaration, combined with a
  proof that uses the family only abstractly, would show up here as a
  nonzero headline number and would need `axiom_footprint`/`decl_deps`
  itself reviewed — a decision this audit deliberately declines to make.

## Reproduction

```sh
cargo build --release -p axeyum-lean-kernel --example footprint_closure_audit
./target/release/examples/footprint_closure_audit --include-constructed \
  > rows.tsv 2> summary.txt
```

Exit status 0 means every fidelity assertion held for every theorem audited;
a nonzero exit means the reimplementation diverged from `axiom_footprint` or
`declaration_dependency_closure` and the run aborted rather than reporting a
number computed by a divergent walk.
