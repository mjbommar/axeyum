# ADR-1320: one canonical definition per mathematical object

Date: 2026-08-31
Status: Accepted
Lane: `constant-canonicity`

Index-summary: Will this development end up with twenty definitions of pi? Measured 2026-08-31, nothing objected to a second one. `check-shape-duplicates.py` groups declarations by admitted TYPE and every `CReal`-valued constant has the identical type `CReal`, so it is structurally blind here -- 15 duplicate groups, zero containing a constant -- and `CReal.Equiv` is undecidable, so no mechanical "same real" test exists either. The population is small and measurable: **16** nullary data-valued definitions over `CReal`/`Complex`/`Int`/`Rat`, not just `CReal`. The gate derives that population from `kernel_declaration_projection` (including the `Prop` exclusion, from the head symbol's own result sort) and requires each constant to be adjudicated in `artifacts/trust-closure/canonical-constants.tsv` in both directions; an ALTERNATE construction must name a bridge theorem whose STATED TYPE mentions both constants, checked against the environment. Proved end to end by declaring a real second `CReal.pi`/`CReal.piMachin` in a snapshot kernel and watching the gate go red naming both. The limit is stated plainly: the gate cannot check that a "these are different objects" claim is TRUE -- it converts a silent omission into a written, attributable claim.
Index-status: Accepted

## Context

The question that started this was a user's: *will we end up with ten or twenty
definitions of pi?* A sibling lane is building `CReal.pi` right now.

Checking rather than reassuring found a real hole. Nothing in this repository
objects to a second definition of a mathematical constant:

- **The kernel cannot object.** `Kernel::add_declaration` type-checks a proof
  term against its stated type; a `Definition` has no proof body and is
  admitted once it is well-typed. CLAUDE.md already says this ("THE TRUSTED
  GATE CANNOT TELL YOU A `Definition` IS WRONG"). A second construction of pi
  is *not even wrong* — it is a perfectly good real number that nothing relates
  to the first.
- **The shape detector cannot object.** `check-shape-duplicates.py` (ADR-1170)
  groups declarations that state the same proposition, by admitted type.
  Measured 2026-08-31: **15 duplicate groups, and zero of them contain any
  constant.** Every `CReal`-valued constant has the identical type `CReal`, so
  a type-based detector over constants is either useless (one group holding
  `zero`, `one`, `e`, `cosOne`, `sinOne`, `inv2`, `inv3`, `two`, `three`) or
  blind. It is blind — `shape_search` reports singleton types, not the carrier
  group.
- **No decision procedure can object.** `CReal.Equiv` is undecidable. There is
  no mechanical test for "is this constructed real the same real as that one".

Note that the discipline this ADR wants is **already the practice**, and that
is the strongest evidence it is worth enforcing. Three alternative
constructions have already landed as THEOREMS rather than as second
definitions:

    CReal.expFn_one_equiv_e         : Equiv (expFn one) e
    CReal.cosFn_one_equiv_cosOne    : Equiv (cosFn one) cosOne
    CReal.cosFnWide_one_equiv_cosOne: Equiv (cosFnWide one) cosOne

`cos 1` has two alternative constructions and still exactly one constant. What
has never existed is anything that would notice if the next lane did it the
other way — which is precisely CLAUDE.md's standing finding that discipline
carried only by lane memory is not a gate.

## The measured scope

From `kernel_declaration_projection --release` over all eleven preludes
(14,137 rows, 1,850 definitions), deduplicated by name — a nullary definition
being one whose canonical type contains no arrow:

| carrier | constants |
| --- | --- |
| `CReal` | `CReal.zero`, `CReal.one`, `CReal.e`, `CReal.cosOne`, `CReal.sinOne`, `CPoint.Scalar.two`, `CPoint.Scalar.three`, `CPoint.Scalar.inv2`, `CPoint.Scalar.inv3` |
| `Complex` | `Complex.zero`, `Complex.one`, `Complex.I` |
| `Int` | `Int.zero`, `Int.one` |
| `Rat` | `Rat.zero`, `Rat.one` |
| *(excluded)* | `Nat.lt_well_founded : WellFounded.{1} AxNat AxNat.lt` |

**16 constants over 4 carriers.** Two corrections to the framing this lane was
given:

- The brief said "9 distinct `CReal`-valued definitions today (plus
  `CPoint.Scalar.*`)". It is **9 including** the four `CPoint.Scalar.*` rows —
  5 in the `CReal` namespace and 4 in `CPoint.Scalar`.
- **This is not a `CReal` problem.** `Complex.I` and `Rat.one` are the same
  shape of object with the same absence of any guard. Scoping to `CReal` would
  have left the hole open one carrier over, which the brief correctly warned
  against; scoping to all carriers costs seven extra registry rows.

The `Nat` prelude contributes nothing: `Nat.zero` and `Nat.succ` are
constructors, not definitions.

### Where the boundary is, and why it is there

`CReal`-valued **functions** are a real duplication hazard too — two
definitions of `exp` (Taylor series versus a limit) would be exactly the same
defect one arity up, and the shape detector is equally blind to them
(`(x0 : CReal) -> CReal` has 21 distinct members). They are **out of scope
deliberately**: there are 366 function-valued definitions, and a 366-row
hand-adjudicated registry is the shape of gate lanes turn off. Sixteen rows is
not.

The instrument for the function case is different and already exists —
`shape_search` by conclusion head plus a proof-skeleton read (CLAUDE.md's
"THE SAME ARGUMENT OVER A DIFFERENT AGGREGATE"). This ADR does not pretend to
cover it, and says so rather than quietly extending the population later.

## Decision

**One canonical definition per mathematical object. An alternative
construction lands as a THEOREM relating it to the canonical one, never as a
second definition.** Machin's formula is `CReal.pi_eq_machin`, not
`CReal.piMachin`.

Enforced by `scripts/check-constant-canonicity.py` against
`artifacts/trust-closure/canonical-constants.tsv`.

### What is derived, and what is declared

The design constraint the brief set — *"a registry nobody maintains is worse
than none"* — is met by deriving everything the authority can decide and
requiring a declaration only where it genuinely cannot.

**Derived from `kernel_declaration_projection`:**

- The population. The registry never lists what the constants ARE; it is
  checked against the environment in both directions, so a new constant fails
  the gate and a removed one fails it too.
- The `Prop` exclusion, which is the part that would otherwise have been a
  hand-written exemption list. `Nat.lt_well_founded` is a genuine nullary
  definition, but its head symbol `WellFounded` is itself a definition whose
  result sort is `Prop` — so it is a PROOF, and definitional proof irrelevance
  makes a duplicate of it harmless. The checker looks that up rather than
  naming the constant. There is no exemption list to grow.
- Each constant's carrier, checked against the registry's `carrier` column.
- Whether a claimed `bridge` theorem exists, is a theorem, and STATES a
  relation between the two constants — read from the projection's
  `direct_type_declarations` column, never its all-kinds column. A theorem
  that merely touches both constants inside its proof term relates nothing
  (`CReal.e_converges`'s proof touches 60-odd declarations its type never
  mentions).

**Declared, because the kernel cannot decide it:** which mathematical object
each constant denotes, and which constant is canonical for it.

### The registry

`artifacts/trust-closure/canonical-constants.tsv`, beside its sibling
`equivalent-pairs.tsv`:

    carrier <TAB> constant <TAB> object <TAB> role <TAB> bridge <TAB> reason

`role` is `canonical` (the definition of record) or `alternate` (a second
construction, which must name a `bridge`).

### The guards

| | |
| --- | --- |
| G1 UNADJUDICATED | a constant in the kernel with no registry row |
| G2 STALE | a row naming a constant the kernel lacks |
| G3 CARRIER-MISMATCH | the row's carrier is not the kernel's type |
| G4 AMBIGUOUS | two `canonical` rows for one (carrier, object) |
| G5 ORPHAN-ALTERNATE | an `alternate` whose object has no canonical |
| G6 MISSING-BRIDGE | an `alternate` naming no bridge theorem |
| G7 ABSENT-BRIDGE | a bridge that is not a theorem in the environment |
| G8 VACUOUS-BRIDGE | a bridge whose STATED TYPE does not mention both |
| G9 NO-REASON | a row with an empty `reason` |
| G10 NAME-COLLISION | prefix-matching names registered as different objects |
| G11 DUPLICATE-ROW | two rows for one constant |
| G12 EMPTY-AUTHORITY | zero constants parsed — a broken tool, not a pass |

G8 is what stops the registry being self-certifying: without it, any real
theorem name satisfies an alternate row and the `bridge` column becomes a
field nobody reads.

G10 is a **heuristic**, and is labeled as one in the source. `CReal.pi` and
`CReal.piMachin` prefix-match, so registering the second as its own
mathematical object is refused until the author writes `distinct-from:pi` in
the reason — an explicit, attributable claim. Its evasion is obvious
(`CReal.machinConstant` does not prefix-match `pi`), and it produces **zero**
false positives on today's population (verified pairwise; `one`/`cosOne`,
`two`/`three`, `inv2`/`inv3` all clear). G1 is the guard with no evasion.

## Proof that it fires

Two levels, because a fixture-only demonstration would leave the whole
kernel-to-checker path unexercised.

**End to end, against a real kernel.** In a `scripts/lane-snapshot.sh` scratch
copy — never the shared checkout — `build_creal_prelude_uncached` was patched
to declare two extra nullary `CReal` definitions, `CReal.pi` and
`CReal.piMachin`. The kernel admitted both (the projection grew 14,137 → 14,143
rows: two constants across `creal`, `complex` and `cpoint`), which is itself
the finding — nothing objected. The gate then:

    G1 UNADJUDICATED  CReal.pi : CReal is a new constant with no registry row...
    G1 UNADJUDICATED  CReal.piMachin : CReal is a new constant with no registry row...
    exit=1

Six further cases were run against that same mutated projection, each with a
registry variant, and each produced exactly its own guard:

| registry variant | verdict |
| --- | --- |
| both registered as separate canonical objects | G10 NAME-COLLISION |
| the same, plus `distinct-from:pi` in the reason | OK — 18 constants |
| `piMachin` as an alternate with no bridge | G6 MISSING-BRIDGE |
| bridge `CReal.expFn_one_equiv_e` (a real theorem, about `e`) | G8 VACUOUS-BRIDGE |
| bridge `CReal.pi_eq_machin` (never declared) | G7 ABSENT-BRIDGE |
| both canonical for object `pi` | G4 AMBIGUOUS |

And the unmutated kernel against the shipped registry: `OK -- 16 constants
over 4 carriers, 16 adjudicated, 0 bridged alternate(s), 1 nullary Prop-valued
definition excluded as a proof`.

**Per guard, mechanically.** 32 unit tests, and 19 mutations registered in
`scripts/tests/mutation_controls.py` (which runs `py_compile`, so it is immune
to the stale-`__pycache__` trap). **Every mutation kills exactly one test.**
Three structural choices were forced by that requirement and are the
transferable part:

- Failure cases assert `evaluate()`, not `main()`'s exit status. Routed
  through `main()`, all eleven guard tests die to the single mutation
  `return 1` → `return 0`, and a control that kills eleven tests measures
  nothing about eleven guards. `MainExitStatusTests` is the one place the
  status is asserted, so that mutation — the most important one, since a
  checker exiting 0 on completion alone is the defect this file exists to
  prevent — kills exactly one test.
- `test_a_finding_exits_one` deliberately triggers TWO independent findings,
  so deleting either guard leaves it alive.
- The `Prop` exclusion needs its own fixture. In the shared one an un-excluded
  `Nat.lt_well_founded` is an unadjudicated constant in every test, and the
  mutation killed ten.

## Registration

The CHECKER, not only its tests, in `scripts/check.sh`,
`scripts/local-ci.sh`, `.github/workflows/ci.yml` and the `justfile` —
beside `check-shape-duplicates`, the sibling it complements. ADR-1170's
finding four days ago was that registering only a checker's unit tests is the
quietest form of the checker-that-cannot-fail defect, and that gate ran for
four days without ever examining the environment. ~40 s warm.

## Consequences

**What this guarantees.** A new constant cannot land silently. Its author must
either register it as a new mathematical object — visibly, in a reviewed file,
attributably — or register it as an alternate and name a bridge theorem the
kernel has actually checked relates it to the canonical one. The registry
cannot go stale in either direction, and the constant population is read from
the kernel rather than remembered.

**What it does NOT guarantee, and cannot.** It cannot check that a `canonical`
row's claim is TRUE. A lane may register `CReal.piMachin` as object
`pi-machin` with `distinct-from:pi` and pass the gate. `Equiv` is undecidable
and no instrument can close that. What changes is that a duplication stops
being an omission — invisible, unattributable, discovered a year later — and
becomes a written false claim in a reviewed file. That is the same standing
`scripts/shape-duplicates-allowlist.json` has, which this repository already
accepts as the bar for an undecidable adjudication.

**Was a gate the right answer?** The brief asked this seriously, and the
honest case against it is that 16 constants and a small team could be handled
by a documented rule. The case for, which won: the failure is silent,
permanent, and poisons every downstream statement's meaning; the discipline is
already practised three times over and depends entirely on lane memory, which
this repository has measured failing repeatedly; the cost is one registry row
per new constant, which is a genuine forced-review moment rather than
paperwork; and the population is derived, so the registry cannot rot. A gate
would have been theatre if the population had to be hand-listed. It does not.

**Where the constructive `Apart` evidence sits.** A pleasant surprise from the
measurement: `Equiv` is undecidable in general, but **separation is positively
witnessable**, and five constant pairs already carry kernel-checked
distinctness proofs — `CReal.apart_zero_one`, `Complex.Equiv.not_zero_one`,
`Complex.Equiv.not_zero_I`, `Int.Characterization.zero_ne_one`,
`Rat.one_ne_zero`. Those are cited in the registry's reasons. Requiring one
per pair would be over-scoping (36 pairs for `CReal` alone, almost all
unproved), so they are recorded rather than demanded; the natural future
strengthening is a `separation` column checked exactly the way `bridge` is.

**For the `creal-pi` lane.** Nothing here depends on `CReal.pi` existing. When
it lands, it needs one row:

    CReal	CReal.pi	pi	canonical	-	<why this construction is the definition of record>

and the gate will fail until it does.

## Anything in the brief that was wrong

- "9 distinct `CReal`-valued definitions today (plus `CPoint.Scalar.*`)" —
  it is 9 *including* the `CPoint.Scalar.*` four.
- The brief left open whether this is a `CReal` problem or applies to every
  carrier. Measured: every carrier, and the cost of covering all four is seven
  extra rows.
- The brief's premise that the guard "cannot rest on deciding `Equiv`" is
  right, but understates what the authority can do: it cannot decide equality,
  and it CAN decide (a) the population, (b) the `Prop`/data split, and (c)
  whether a claimed bridge theorem actually states a relation between the two
  constants. Only (d) — which object a constant denotes — is genuinely
  declarative.

## References

- [ADR-1170](adr-1170-the-retrieval-gate-existed-and-ran-nowhere.md) — the sibling gate,
  and the "register the checker, not only its tests" finding.
- [ADR-0790](adr-0790-duplicate-identity-classes-are-labeled-not-deleted-and-two-numbers-are-published.md) — the same defect in
  the fact ledger, with `equivalent_to` as its declarative half.
- [ADR-0542](adr-0542-held-out-partition-breach-repair.md) —
  why a registry is repaired by amendment.
