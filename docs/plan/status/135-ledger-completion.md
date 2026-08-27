# Lane: ledger-5 — register the last two days' proved mathematics, plus the first honest `cas-internal` fact

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, ledger-5, 2026-08-27).** Registered 29 new facts
in `artifacts/facts/` (28 `kernel-lean` + 1 `cas-certificate`).
`python3 scripts/validate-facts.py` is green:

```
805 facts checked, 0 errors  (computed=2 conjectured=3 open=176 proved=620 refuted=4)
  routes: cas-certificate=24(kernel-reconstructed=0,cas-internal=24) imported-kernel-lean=5 kernel-lean=559 search-certificate=12 smt-clausal=9 smt-term-level=17; 557 axiom-free on kernel-lean (not comparable across routes)
  cas-certificate: 24 total -- kernel-reconstructed 0, cas-internal 24
```

(776 pre-existing + 29 new = 805.)

**Ch.24 completion (uniform convergence):** `F:creal-weierstrassmtest` (the
Weierstrass M-test — notes record its two mathematically-necessary
hypotheses: `f` must respect `CReal.Equiv` because `CReal` is a Bishop
setoid, not a literal quotient (ADR-0512); the limit is built at the CLAMPED
point `max a (min pt b)` because `CReal.le` is undecidable and there is no
way to conjure the domain-membership proof an arbitrary symbolic point would
need), `F:creal-uniform-converges-add`, `F:creal-close-within-of-within`.

**The five skipped from batch 4 (`ledger-uc`, see
[133-ledger-uc.md](133-ledger-uc.md)'s Findings — these did not exist on that
lane's base and were correctly refused there; they exist on this lane's
merged `main`):** `F:nat-even-or-odd` (the computed `k := n/2` parity split,
never existential), `F:creal-alternatingbracketupper`,
`F:creal-alternatinglowerbound`, `F:creal-alternatingupperbound`. (The fifth
named in that lane's findings, `CReal.weierstrassMTest`, is registered above
as its own Ch.24-completion entry, not duplicated here.)

**Trig (16 facts):** `F:creal-sinterm`, `F:creal-sinseriespartial`,
`F:creal-sintermabsledominant`, `F:creal-sinone`, `F:creal-sinoneconverges`,
`F:creal-sinone-alternating-lower`/`-upper`, `F:creal-sinone-nonneg`,
`F:creal-sinone-le-exp-term-one`, `F:creal-expterm-antitone`,
`F:creal-expterm-zero-eq-one`, `F:creal-expterm-one-eq-one`,
`F:creal-cosone-alternating-lower`/`-upper`, `F:creal-cosone-nonneg`,
`F:creal-cosone-le-exp-term-zero`. The last two are the REAL `[0,
expTerm(0)]` bound on `cos(1)` and are recorded as SUPERSEDING (without
deleting) the loose `[-4,4]`-style bound in `F:creal-cosone-le-four`;
`F:creal-sinone-nonneg`/`F:creal-sinone-le-exp-term-one` do the same for
`sin(1)`.

**Ch.14 crossing chain:** `F:creal-crossingcloseclamped` (notes record that
BOTH domain hypotheses `crossingClose` needs are discharged BY CONSTRUCTION
via `min`/`max` clamping — no comparison decided), `F:creal-crossingsamplegea`,
`F:creal-riemannsamplecrossingclose`. (`CReal.meshScaledLeOfGe` was already
registered as `F:creal-meshscaledleofge` by `ledger-uc` — confirmed, not
re-registered.)

**Complex polynomials — only 2 of the 8 named were unregistered; the other 6
already exist from `ledger-uc`** (`F:complex-polydegreelt-polymul`,
`F:complex-hornerfromtop`, `-zero`, `-succzero`, `-succsucc`,
`F:complex-factorquotient`, `F:complex-factorquotient-degreelt` — confirmed
present, not duplicated): `F:complex-factorquotient-succ-eq`,
`F:complex-hornerfromtop-diag-eq-polyeval`.

**`CReal` polynomials:** already fully registered by `ledger-uc`
(`F:creal-polyeval` family, `F:creal-polyadd`, `F:creal-polyscale`,
`F:creal-polydegreelt` family) — confirmed present, nothing to add.

**The first `cas-certificate` fact under the `kernel-reconstructed`/
`cas-internal` split (ADR-0601 SS2):** `F:cas-ivt-cbrt2-in-1-2` — "`x^3-2` has
exactly one real root in `(1,2)`", the existing `axeyum-cas` unit test
`real_algebraic::tests::ivt_names_the_root_of_a_cubic`. Checker:

```
cargo test -p axeyum-cas --lib real_algebraic::tests::ivt_names_the_root_of_a_cubic -- --exact \
  2>/dev/null | grep -cE '^test real_algebraic::tests::ivt_names_the_root_of_a_cubic \.\.\. ok$'
```

Notes state PLAINLY: *"THIS EVIDENCE IS cas-internal, NOT kernel-reconstructed
(ADR-0601 SS2) ... verified by the CAS's own `verify_ivt_certificate` ... but
NOT YET reconstructed through `Kernel::add_declaration`. The ledger must not
let this read as kernel-checked."* `axiom_footprint` includes
`cas.ivt-certificate-not-kernel-reconstructed` as an explicit, honest
footprint entry.

## Checker forms used

- Theorems: `cargo run -q --release -p axeyum-lean-kernel --example
  theorem_dependency_inventory -- <Name> 2>/dev/null | grep -cE
  '^<Name>[[:space:]]'`
- Definitions (`sinTerm`, `sinSeriesPartial`, `sinOne`): `cargo run -q
  --release -p axeyum-lean-kernel --example kernel_declaration_projection --
  --require-declaration <Name> --require-kind definition 2>/dev/null | grep
  -cE '^found[[:space:]]<prelude>[[:space:]]definition[[:space:]]<Name>[[:space:]]'`
- Axiom footprint (all 28 kernel facts): `cargo run -q --release -p
  axeyum-lean-kernel --example nat_axiom_inventory -- --include-constructed
  --require-axiom-free {creal|complex|nat}`. Re-measured on this tree:
  `creal: axiom=0 opaque=0 quotient=0 total_trusted=0`, `complex: axiom=0
  opaque=0 quotient=0 total_trusted=0`, `nat: axiom=0 opaque=0 quotient=0
  total_trusted=0`, all exit 0.
- `cas-certificate` (1 fact): `cargo test -p axeyum-cas --lib
  real_algebraic::tests::ivt_names_the_root_of_a_cubic -- --exact` piped to
  `grep -cE` on the exact `... ok` line.

Every checker for every one of the 29 new facts was run individually against
the freshly-built (same-session) `target/release/examples/*` binaries and
confirmed to print a nonzero count before being written into a fact file
(`--release` confirmed mandatory throughout: this tree's binaries are
same-session, built at the point of use).

## Mutation testing (isolated snapshot, never the shared checkout)

`AXEYUM_AGENT=ledger-5 scripts/lane-snapshot.sh HEAD` ->
`/data0/axeyum/scratch/snap-ledger-5-80bbef601` (reclaimed with `rm -rf`
after use). Two kernel mutations plus one CAS mutation, all in the SAME
rebuild for the two kernel ones:

- `CReal.weierstrassMTest` -> `CReal.weierstrassMTest_MUTATED`
  (`creal.rs:5083`): `theorem_dependency_inventory weierstrassMTest` count
  **0** (was 1). Control in the SAME rebuild, `CReal.uniform_converges_add`:
  count **1**, unaffected.
- `CReal.sinOne` -> `CReal.sinOne_MUTATED` (`creal.rs:5087`, same rebuild as
  above): `kernel_declaration_projection --require-declaration CReal.sinOne
  --require-kind definition` count **0** (was 1). Control `CReal.sinTerm`
  (a Definition too, same rebuild): count **1**, unaffected.
- CAS: `real_algebraic.rs`'s `ivt_names_the_root_of_a_cubic` test's
  `assert_eq!(cert.root.degree(), 3)` mutated to `4`
  (`crates/axeyum-cas/src/real_algebraic.rs:744`): the fact's exact checker
  command count went **0** (was 1, test fails on the wrong assertion).
  Control in the same rebuild, `verify_accepts_the_unmutated_control`: count
  **1**, unaffected.

All three targets killed cleanly; both controls in each rebuild survived
unaffected, confirming the checkers discriminate on the named
declaration/test rather than on the build succeeding globally.

## Not registered, with reasons

- Anything from lanes still running (`integral_split_rat`, power series,
  producer contracts, shard-inventory outputs), Ch 21, FTA — per brief, out
  of scope for this lane.
- `CReal` polynomials and 6 of the 8 named `Complex` polynomial declarations
  — already registered by `ledger-uc` (batch 4); confirmed present via an
  environment-derived scan of every fact's `formal.kernel_theorem` before
  writing anything, not duplicated.
