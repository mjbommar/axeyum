# A per-function trust registry for `axeyum-cas` (roadmap item 10, first half)

Measured 2026-09-05 at commit `7a63a3204` (lane `cas-trust-registry`).

## The question

[`docs/math-department/13-computer-algebra.md`](../../docs/math-department/13-computer-algebra.md),
chair 12 (the chair): "a proof-carrying CAS with no real quantifier
elimination... no gate counts which of the 691 public functions carry a
certificate." The file's Next Ten item 10 asks for exactly that gate, plus
(not this lane's task) a SymPy parity corpus. This measurement is the first
half only: `scripts/check-cas-trust-registry.py`, its ratchet, and a
comparison against the "Certified" column of
[`docs/research/10-cas/README.md`](../../docs/research/10-cas/README.md#implemented).

## Method

`scripts/check-cas-trust-registry.py` walks every `.rs` file under
`crates/axeyum-cas/src` with a brace-aware scanner, not a whole-file regex:

1. **Mask.** Comment and string/char literal bodies are replaced with blanks
   (same length, newlines preserved), so a `"{"` inside a format string or a
   `mod tests {` inside a doc comment can never be read as code.
2. **Walk braces, classify each header.** For every `{`, the text since the
   last `;`/`{`/`}` at that nesting depth (its "header") is classified as a
   module, an inherent `impl`, a trait `impl`, a function signature, or
   something else (a struct/enum/trait body). Only two classifications keep
   their contents visible for recording: a `mod` that is not
   `#[cfg(test)]`/literally named `tests`, and an inherent `impl` of a type
   this same crate declared `pub struct`/`pub enum` (checked in a second pass
   over the whole crate, since a type can be declared on either side of its
   `impl` block, in the same file or a different one). A `pub fn` inside a
   `#[cfg(test)] mod tests { ... }`, inside a trait `impl` (which cannot
   legally carry `pub` on its items at all), or inside an `impl` of a private
   type is never recorded — the exact fixture required for this gate
   (`test_cfg_test_module_pub_fn_is_not_counted` in
   `scripts/tests/test_check_cas_trust_registry.py`) confirms this directly:
   a `pub fn` textually inside a `#[cfg(test)] mod tests` never reaches the
   enumeration.
3. **Only `pub fn`, never `pub(crate)`/`pub(super)`.** A visibility-restricted
   function is excluded regardless of where it lives.
4. **Certificate vocabulary, derived from the source.** Every `pub
   struct`/`pub enum` whose name ends in `Certificate`, `Evidence`, `Report`,
   or `Witness`, or is exactly `ZeroTest` or `CertifiedIntegral`, or has an
   inherent method literally named `verify` or `check`. Today that last rule
   contributes nothing new: the crate's one function literally named `check`
   (`sos::check`) is free-standing, not a method of any type, and no pub type
   has an inherent `verify`/`check` method — recorded here so the rule is
   exercised the day one is added, not because it currently changes the
   count.
5. **Classify each `pub fn`:**
   - `certified` — the return type names a vocabulary type, directly or
     through `Option<..>`/`Result<.., _>`/`Vec<..>`/a tuple.
   - `checker` — the function name starts with `verify`, `check`, `replay`,
     or `certify` (and did not already classify `certified`).
   - `uncertified` — everything else. This is an honest label, not a defect,
     mirroring `check-cas-internal-residue.py`'s treatment of `cas-internal`.
6. **Ratchet a floor**, `scripts/check-cas-trust-registry.ratchet`: every
   `FN` row (a function recorded `certified` at the last `--write`) must
   still classify `certified` today, not vanish; every `VOCAB` row (a
   certificate-vocabulary type) must still exist; the certified count must
   not fall below a recorded `COUNT` row. `COUNT` is its own row rather than
   `len(FN rows)` on purpose — a single function regressing or vanishing
   *always* also drops the current count below a shared floor, which would
   make that violation and the floor violation the same code path and
   `mutation_controls.py` would report the floor guard's own test as
   surviving its deletion (some other guard's fixture would keep the exit
   code at 1 regardless). Decoupling the two gave every guard an independent
   fixture. A **new** certified function not in the ratchet is refused too
   (`run --write to accept`, deliberately mirroring how the floor only rises
   on purpose); a **new uncertified function is never refused.**

Two real scanner bugs were found and fixed while validating against the full
crate (both are now regression fixtures in the test file):

- The impl-of-a-pub-type check was designed but never wired into the walk —
  every inherent `impl`'s contents were recorded regardless of whether the
  target type was `pub`. Fixed by making `scan_crate` a genuine two-pass scan
  (gather all `pub` type names first, then re-walk with that set).
- A `;` inside **unbalanced** brackets — an array-length return type like
  `Option<[MvPoly; 2]>` — was read as a statement terminator, silently
  truncating the header text and dropping the *next* item's signature
  entirely (not misclassifying it — it vanished from the enumeration).
  Found via `geometry_certify::same_point` and two `lib.rs` functions
  (`curl`, `cross`) missing from an initial scan; a bracket-depth counter
  now gates the `;` reset.

After both fixes, the scanner's output for "fully `pub fn`, any location"
matches a naive whole-crate regex over the masked text exactly (698 of 698),
confirming the skip logic is neither over- nor under-excluding on this
crate's actual source — a separate check (not gated, just verification) also
confirmed the skip mechanism is exercised: 11 `impl` blocks of non-`pub`
types exist in the crate today, none of which happen to contain a `pub fn`
(so today's total would be identical either way; the fixture-based test is
what actually proves the guard fires).

Re-run with:

```sh
python3 scripts/check-cas-trust-registry.py --report
python3 -m unittest scripts.tests.test_check_cas_trust_registry
```

## The numbers, 2026-09-05

```
axeyum-cas pub fn: 698 total -- certified 34, checker 26, uncertified 638
certificate vocabulary: 33 type(s)
OK: 34 certified fn(s) (floor 34, all held), 26 checker, 638 uncertified
```

34 of 698 public functions (4.9%) return a certificate-vocabulary type
directly or through `Option`/`Result`/`Vec`/a tuple. 26 (3.7%) are
`verify`/`check`/`replay`/`certify`-prefixed checkers. The remaining 638
(91.4%) are uncertified — not wrong, just not carrying a checkable artifact
in their signature.

Per-module breakdown (60 of 70 source files have at least one `pub fn`; the
rest — mainly `bin/*.rs` CLI entry points — have none):

| module | certified | checker | uncertified |
|---|---:|---:|---:|
| `lib.rs` | 3 | 0 | 166 |
| `geometry_certify.rs` | 1 | 5 | 27 |
| `gf2.rs` | 3 | 1 | 32 |
| `gf2_extension.rs` | 8 | 0 | 5 |
| `ntheory_certify.rs` | 4 | 4 | 0 |
| `sos/check.rs` | 4 | 0 | 0 |
| `telescoping_check.rs` | 2 | 2 | 12 |
| `extremum.rs`, `inverse.rs`, `mvt.rs`, `partial_fractions.rs`, `rationality.rs`, `taylor.rs` | 1 each | 1 each | 0 each |
| `real_algebraic.rs` | 1 | 1 | 7 |
| `geometry_json.rs` | 1 | 0 | 2 |
| `sos.rs` | 1 | 0 | 12 |
| all other modules (44 files) | 0 | remainder | remainder |

The full per-module table and the sorted list of uncertified functions per
module are in `--report`'s output (not reproduced here — it is long).

Certificate vocabulary (33 types), by rule: 31 end in `Certificate`/
`Report`/`Evidence`/`Witness` (e.g. `ExtremumCertificate`,
`HalfDegreeParitySplitReport`, `GosperEvidence`, `DegenerateWitness`, and the
five `gf2_extension.rs` shard/trace report types), 2 match an exact name
(`ZeroTest`, `CertifiedIntegral`). Zero types are pulled in solely by the
"has an inherent `verify`/`check` method" rule today (see Method §4).

## A documented scope boundary: sum-type returns

`geometry_certify::certify`/`certify_any_route`/`certify_by_linear_elimination`
classify `checker` (their names start with `certify`), not `certified`,
despite each returning `ProofOutcome`, an enum with a
`Certified(Box<GeometryCertificate>)` variant. `ProofOutcome` itself is not
in the vocabulary (its name matches none of the suffix/exact rules) and its
return type is not unwrapped as a sum type — only `Option`/`Result`/`Vec`/a
tuple are peeled. This is a deliberate scope limit, not a bug: `ProofOutcome`
carries a certificate in exactly one of three variants
(`NotInSaturatedIdeal`/`Declined` carry none), so classifying every function
returning it as unconditionally `certified` would overstate the guarantee.
Generalizing to arbitrary enum unwrapping is future work, not attempted here.

A second, narrower false-positive: two inherent methods named `checked_add`/
`checked_mul` (`geometry_certify::Gaussian`, `telescoping_check::SymbolicValue`)
classify `checker` purely because their names start with the four-letter
prefix `check` — they are ordinary checked-arithmetic helpers returning
`Option<Self>`, not certificate checkers. This is the literal, source-derived
prefix rule specified for this gate; narrowing it (e.g. requiring a word
boundary after `check`) is a follow-up, not applied here since it was not
asked for and changes today's count.

## Comparison against `docs/research/10-cas/README.md`'s capability table

The table has 28 rows (`Area` / `Functions` / `Certified`). For each row,
every backtick-quoted identifier in its `Functions` cell was checked against
the gate's `certified`/`checker` sets (matched on the function's own name,
ignoring module path). This is a one-off cross-check for this report, not a
new gate — the README is prose maintained by hand and this lane was told not
to edit it.

**Two rows agree.** `Core`'s `equal` is `certified` (returns `ZeroTest`,
matching the README's `equal ✓`); `Integration`'s `integrate` is `certified`
(returns `Option<CertifiedIntegral>`, matching `CertifiedIntegral` named in
the same cell).

Of the 28 rows, 27 carry an actual "Certified" claim (a checkmark, "exact",
or similar prose); the 28th (`Multivariate`) is `—`, i.e. no claim, and the
gate agrees (`mvpoly.rs` has 0 certified, 0 checker functions). Of the 27
rows with a claim, **25 disagree**: the named functions in that row's
`Functions` cell match neither the gate's `certified` nor `checker` set,
even though the `Certified` column marks the row with a checkmark or the
word "exact". Representative disagreements:

| Area | README's `Certified` cell | What the gate finds |
|---|---|---|
| Rational | `factor/apart/factor_expr ✓` | Only `partial_fractions::partial_fractions` (not named in this row at all — it is the same underlying certificate but the row cites `apart`, a different function) is `certified`; `factor`, `apart`, `factor_expr` themselves return plain `CasExpr`/`Vec<..>` values with no certificate type |
| Equations | `rational + radical + transcendental + system ✓; Sturm-certified` | None of `solve`, `real_roots`, `count_real_roots`, `real_root_intervals`, `solve_polynomial_system`, `solve_polynomial_inequality` are `certified` or `checker`; the crate's actual Sturm/IVT certificate (`real_algebraic::polynomial_ivt → Option<IvtCertificate>`) is not even named in this row |
| Linear algebra | `det/solve/eigvec/diag/jordan/matexp/ODE/companion ✓; A·P=P·J ✓` | None of the named `Matrix` methods are `certified` or `checker` |
| ODEs / recurrences | `✓ (substitute-and-check)` | None of `dsolve_*`, `solve_recurrence`, `apply_initial_conditions` are `certified` or `checker` |
| Transforms | `✓` | None of `laplace_transform`, `inverse_laplace`, `z_transform`, `inverse_z_transform` are `certified` or `checker` |
| Number theory | `re-check ✓` | None of the named `ntheory*` functions are `certified` or `checker` (the crate's real `ntheory_certify.rs` module, with 4 certified + 4 checker functions, is a *different* module from the ones this row names) |

The pattern repeats across the remaining 19 of the 25 disagreeing rows not
already shown above (Summation, Summation (definite), Complex analysis,
Approximation, Analysis, Trig, Complex, Logic/sets, Special functions,
Finite fields, Groups, Boolean algebra, Geometry, Vector calculus, Special
polys, Combinatorics, Logs/abs, Statistics, Radicals) — in every one, none
of the row's named functions match the gate's `certified` or `checker` set.
`Multivariate`'s own cell is `—` (explicitly uncertified), which is the one
row besides Core and Integration where the README's own claim already
matches the gate's finding.

**Reading of the disagreement.** The README's "Certified" column describes
an internal-discipline claim — the function checks its own result before
returning (differentiate-and-check, substitute-and-check, re-multiply,
truth-table verification) — not "the return type is a distinct, independently
checkable certificate object." Those are different claims. ADR-0601's own
vocabulary (`kernel-reconstructed` vs `cas-internal`) exists for exactly this
distinction in the fact ledger; this gate applies the same distinction to
the *source surface* rather than the fact ledger, and finds that almost all
of the README's "Certified ✓" marks describe `cas-internal`-style
self-checking, not a certificate artifact a caller could independently
replay. This is the measured version of chair 12's complaint: the column
was prose, and the source mostly does not carry what "Certified ✓" implies
to a reader expecting a certificate object.

This finding is a comparison for this report, not a change to the README —
the task for this lane is explicitly not to edit
`docs/research/10-cas/README.md`.

## What this measurement does not cover

- The SymPy parity corpus (Next Ten item 10's second half) — not this
  lane's task.
- Whether an `uncertified` function's result is *correct* — that is out of
  scope by construction; `uncertified` is a label about the signature, not a
  correctness claim.
- Full enum-variant unwrapping for return-type classification (see the
  `ProofOutcome` scope boundary above).
- Module-visibility resolution beyond the `impl`-of-a-`pub`-type check (a
  `pub fn` inside a non-`pub` `mod` nested several levels deep, none of which
  occurs in this crate today, would still be counted — the gate does not walk
  the full `mod` visibility chain, only the `#[cfg(test)]`/`tests` exclusion
  and the impl-of-pub-type check named in the task).

## Files

- `scripts/check-cas-trust-registry.py` — the gate
- `scripts/check-cas-trust-registry.ratchet` — the floor (34 certified
  functions, 33 vocabulary types)
- `scripts/tests/test_check_cas_trust_registry.py` — 21 tests, including the
  required `#[cfg(test)]`-exclusion fixture and the array-length-semicolon
  regression fixture
- `scripts/tests/mutation_controls.py` (`SUITES["cas-trust-registry"]`) — 6
  guards, each killed by exactly one test (`python3 scripts/tests/mutation_controls.py cas-trust-registry`)
- `scripts/check.sh`, `justfile` — the gate registered next to
  `cas-internal-residue`
