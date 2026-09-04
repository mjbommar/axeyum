# ADR-1611: a computability layer, and connecting Cantor to undecidability

Status: accepted
Date: 2026-09-04
Lane: `computability`

Index-summary: A minimal machine model over ℕ — a `step : Nat → Nat`
transition function on a Nat-encoded configuration space, run for a given
number of fuel steps via `Nat.rec` — chosen over an explicit register-machine
front end and over a `Nat.Partrec.Code`-style syntactic evaluator because it
reaches a genuine undecidability result in one file with no `List`/Gödel
front end. `Nat.RM.self_halting_not_decidable` refutes a two-sided-correct
decider for the model's self-referential halting predicate at one marker
point; the two-case proof is built from the same `Bool.rec`/`Or`-split and
disjointness facts `Nat.cantor_no_fixed_point`'s family is built from, but
does not literally call it — the attempt and why it didn't land cleanly are
recorded below. The undecidability of first-order validity was not
reached and stays `open` in the fact ledger.

## Context

`docs/math-department/10-logic-and-foundations.md` (the proof-theory
reviewer, roadmap item **2** of their "Next five") names a specific,
three-part gap: no machine model, no halting problem, and
`Nat.cantor_no_fixed_point` — the library's diagonalization result — sitting
unconnected to any undecidability claim. Item 3 of the same brief, the
undecidability of first-order validity, sits `open` in
`artifacts/facts/F-*.json` with no proof behind it and was named as
"if you reach it" — a real theorem, not a placeholder to fill.

The brief that dispatched this lane was explicit about the two live design
questions: which machine model, and whether "not decidable" here means the
genuine constructive thing (a decider would force a contradiction) rather
than a classical non-existence claim smuggled past `funext`/`propext`/choice,
none of which this kernel has.

## Decision

**Model: a shallow, step-function register machine, not a syntactic
register-machine front end and not `Nat.Primrec`'s sibling
`Nat.Partrec.Code`.**

```text
Nat.RM.runFuel (step : Nat → Nat) (c fuel : Nat) : Nat
  := Nat.rec (fun _ => Nat) c (fun _ ih => step ih) fuel
Nat.RM.Halts (step : Nat → Nat) (x : Nat) : Prop
  := ∃ fuel, Eq Nat (runFuel step x fuel) 0
Nat.RM.diagStep (H : Nat → Bool) (c : Nat) : Nat
  := Bool.rec (fun _ => Nat) 0 c (H c)        -- if H c then c else 0
```

A "program" is not a syntactic object decoded by a universal interpreter —
it *is* its `step : Nat → Nat` function, exactly the μ-recursive-flavoured
shallow embedding computability-in-a-proof-assistant projects commonly start
from. `0` is the distinguished halted configuration; `runFuel` is ordinary
structural recursion on the fuel argument alone (`step`/`c` held fixed,
mirroring `Nat.add`'s own right-recursion holding its left argument fixed),
so it is total, decidable per step, and needs no equation lemmas — every
consuming proof uses the `ι`-reduction directly, the same discipline
`ble.rs`'s double-`Nat.rec` construction uses.

`diagStep` is the one machine this file needs: given a candidate total
decider `H : Nat → Bool`, it is the machine that asks `H` about its own
CURRENT configuration at every step. Starting it from the fixed marker `1`:
if `H 1 = true` it self-loops at `1` forever (proved by fuel induction, not
merely evaluated); if `H 1 = false` it reaches `0` in exactly one step. `H`
being called directly inside `diagStep`'s own definition is not a shortcut —
it is the same move `Nat.cantor_diagonal`'s witness `g := fun n => not (f n
n)` already makes: an arbitrary bound function, called directly, is exactly
what a diagonal construction is allowed to do.

**Rejected: an explicit register-machine front end (Gödel-numbered
instruction stream, decoded on the fly via `Nat.pair`/`unpairLeft`/
`unpairRight`, already present from `unpair.rs`/ADR-1220).** This was the
first design considered, because the pairing machinery already exists and a
"real" instruction-decoding interpreter reads as more faithful to "a machine
model". It was rejected on cost: encoding a genuinely Turing-complete
instruction set as a single Nat, decoding it position-by-position inside the
step function, and proving anything about the RESULT requires reasoning
about the ENCODING at every step (does decoding commute with the recursion,
does an instruction pointer stay in bounds) on top of the reasoning about the
MACHINE'S BEHAVIOUR — two coupled proof obligations where the shallow model
has one. The brief's own steer — "the kernel is best at finite, decidable,
syntactic material, so favour whichever gives the shortest route to (2)" —
argues for the front end only if the syntax itself is the point; here the
undecidability argument needs a `step : Nat → Nat` function that can call an
arbitrary `H`, and an instruction-decoding layer would not have made that
call any more expressive, only added a translation step around it.

**Also rejected, for this iteration: `Nat.Primrec`'s sibling
`Nat.Partrec.Code`** — an inductive `Code` type (`zero, succ, left, right,
pair, comp, prec, rfind`) with a fuel-bounded `evaln : Code → Nat → Nat →
Option Nat` evaluator, Mathlib's own shape
(`Mathlib/Computability/PartrecCode.lean`) and the natural extension of the
already-declared `Nat.Primrec` inductive (`primrec.rs`, ADR-1240) with one
more constructor for unbounded search. This is the RIGHT next step toward an
actual universal machine (see Consequences), and reusing `Nat.pair`/
`unpairLeft`/`unpairRight` for `Code`'s own Gödel numbering is the reason it
is next rather than further out — but building the inductive, its recursor
discipline, a fuel-bounded structural evaluator over BOTH `Code` and fuel,
and the encode/decode round trip needed for self-application is a multi-file
project on the scale of `Nat.Primrec`'s own supporting theorem stream
(ADR-1240's "the ordinary supporting theorems land the day after a draw").
Out of scope for one lane's session; the shallow model reaches a genuine,
narrower undecidability result today and does not foreclose building `Code`
later as a SEPARATE, more expressive model.

## Connecting Cantor: what was tried, and what actually landed

The brief's steer was specific: "derive the contradiction from the existing
Cantor result rather than rebuilding the diagonal" and "most likely that a
decider would yield a fixed point that `cantor_no_fixed_point` refutes".

That route was built first. Assume `H : Nat → Bool` two-sided-correct for
`Halts (diagStep H) 1`. The two correctness directions, combined with
`diagStep`'s definition, give — after a short derivation — `Eq Bool (H 1)
true ↔ Halts (diagStep H) 1` and (from `diagStep`'s two branches) `Halts
(diagStep H) 1 ↔ Eq Bool (H 1) false`, so `H 1 = true ↔ H 1 = false`, which
is exactly `Eq Bool (not (H 1)) (H 1)` — a genuine fixed point of `not`,
handed to `Nat.cantor_no_fixed_point` (`F := not`, with `∀ b, not b ≠ b`
built once, independently, by the same `Bool.rec` technique
[`cantor_pointwise`](../../../crates/axeyum-lean-kernel/src/nat_prelude/cantor.rs)
uses).

**It did not land as the cleanest proof term, and the reason is
asymmetric, not incidental.** The "H 1 = true" case needs the fuel-induction
non-halting fact (`∀ fuel, runFuel (diagStep H) 1 fuel = 1`, a Π₁-shaped
statement — a universal claim over unboundedly many fuel values) to refute
`Halts`; the "H 1 = false" case needs only ONE step (Σ₁-shaped — a single
witness). Routing the FIRST case through the shared `not b = b` fixed point
means deriving `False` from the fuel-induction argument first anyway (the
1≠0 disjointness IS the whole content of that case), then decorating it as
"a fixed point" via `False.rec` — decorative, not load-bearing, and it
obscures which fact is doing the work. The version that shipped
(`Nat.RM.self_halting_not_decidable`, `nat_prelude/computability.rs`) closes
the two cases directly: `bool_true_or_false`'s `Bool.rec`/`Or` case split
(the SAME shared plumbing `cantor.rs`'s three theorems and this file both
draw from `ops.rs`), `Nat.succ_ne_zero` in the true case, `Bool.true_ne_false`
in the false case. This is the same TECHNIQUE `cantor_no_fixed_point`'s own
proof uses — a constructive two-constructor case split discharged with
`Bool` disjointness, not excluded middle — applied to a new self-referential
statement, rather than a literal function call to the declared name.

**What is proved, precisely** (the reviewer named reads `#print axioms`
before the theorem, so this is stated exactly, not rounded up):

```text
Nat.RM.self_halting_not_decidable :
  ∀ H : Nat → Bool,
    (Eq Bool (H 1) true → Halts (diagStep H) 1) →
    (Halts (diagStep H) 1 → Eq Bool (H 1) true) →
    False
```

`H` is assumed correct ONLY at the single point `1`, for the single machine
`diagStep H` — narrower hypotheses than "H decides `Halts` for every step
function at every input", because the proof never uses more, and stating
more would overclaim. This is a genuine constructive refutation: the two
correctness directions plus `diagStep`'s own definition are jointly
inconsistent, full stop, with an empty axiom footprint
(`computability_tests.rs::self_halting_not_decidable_is_a_declared_axiom_free_theorem`).
It is **not** Turing's theorem for a fixed Turing-complete universal
machine — there is no program-as-data encoding here, no s-m-n theorem, no
recursion theorem, and `Halts` is not shown undecidable for an ENUMERATION
of machines, only for the one self-referential instance a candidate `H`
itself determines. Read `computability.rs`'s module doc before citing this
result; it says the same thing at the point of use.

## Item 3: the undecidability of first-order validity — not reached

`docs/math-department/10-logic-and-foundations.md` names this as item 2's
sibling and the fact ledger carries it `open` with nothing behind it. It
was not attempted this session: it needs, at minimum, an arithmetization or
equi-expressive encoding of first-order formulas over this kernel's `Nat`
carrier and a reduction from `Halts` (or an equivalent undecidable set) into
validity — a project on the scale of the model-theory reviewer's own item 3
(structures, satisfaction, soundness), not a corollary of the halting result
above. It stays `open`, honestly, rather than gaining a weak or padded
proof.

## Consequences

- **A genuine, if narrow, undecidability result now exists**, with the
  connection to `Nat.cantor_no_fixed_point`'s diagonalization made explicit
  in the module doc and this ADR, even though the final proof reuses the
  TECHNIQUE rather than the DECLARED NAME. `docs/math-department/
  10-logic-and-foundations.md`'s "no computability theory (no formal machine
  model, no halting problem, no reducibility)" line is now wrong on the
  first two counts and still right on the third.
- **The natural next step is `Nat.Partrec.Code`**: reuse `Nat.pair`/
  `unpairLeft`/`unpairRight` (already built, `unpair.rs`) for the encode/
  decode, extend `Nat.Primrec`'s inductive shape with an `rfind`
  constructor, and build a fuel-bounded structural `evaln`. That would
  upgrade this ADR's narrow self-referential result toward Turing's actual
  theorem (a fixed universal machine, undecidable over an enumeration of
  programs) and would also be the natural carrier for reducibility and the
  recursion theorem the reviewer's wishlist names.
- **First-order validity's undecidability is unblocked in principle** (a
  reduction FROM `Halts` is the standard route) but needs the arithmetization
  work the model-theory reviewer's own roadmap item names; it is not free
  from this ADR's machine model alone.
- No axioms were added; `unsafe_code` remains denied; the default build
  gained no new dependency (pure kernel-term construction, same as every
  other `nat_prelude` module).

## Evidence

- `crates/axeyum-lean-kernel/src/nat_prelude/computability.rs` — the model
  and the theorem.
- `crates/axeyum-lean-kernel/src/nat_prelude/computability_tests.rs` —
  evaluation tests for `diagStep`/`runFuel` at concrete numerals (self-loop
  under a constant-`true` decider, immediate halt under constant-`false`,
  each with a negative control naming the swapped value), and the
  declared-theorem/empty-footprint check for `self_halting_not_decidable`.
- `artifacts/facts/F-nat-rm-self-halting-not-decidable.json` — the fact
  ledger entry, `epistemic_status: proved`.
