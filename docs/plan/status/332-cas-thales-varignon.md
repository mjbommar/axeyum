# Lane: cas-thales-varignon — thales kernel-reconstructed and disclosed as refl-shaped; varignon deliberately left cas-internal

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (kernel-reconstructed 13 -> 14; thales
kernel-reconstructed with a full disclosure that its cofactor identity is
refl-shaped, not a genuine combination; varignon deliberately NOT
reconstructed -- its certificate has zero coordinates, zero generators, and
an already-empty conclusion polynomial, so reconstructing it would produce
Rat.zero = Rat.zero with no geometric content at all; next cheapest
cas-internal target is pappus-hexagon)`, cas-thales-varignon, 2026-08-30).**

## Step 0: verified the sizing rather than trusting it

`docs/plan/status/327-cas-geometry-pair.md` named both targets "reachable
with the ORIGINAL constant-cofactor-only machinery
(`cas_geometry_bridge_tests.rs`'s `prove_const_combination`)... possibly the
cheapest reconstruction in the whole geometry family." That much is TRUE for
thales and held with zero new proof-emitting code. But the same handoff, and
— it turns out — the orthocentre sibling fact's own `notes` field (written
2026-08-29, before this lane started) already contained the finding that
matters more than the sizing:

> "thales' single cofactor is the constant 1 against a conclusion
> byte-identical to its generator, so the kernel obligation there is refl."

This lane verified that claim directly against the CAS's own certificate
(`artifacts/geometry-certificates/thales-right-angle-in-semicircle.json`):
`cert.generators[0]` and `cert.conclusions[0].poly` are BYTE-IDENTICAL as
`IntPoly` (same 8 terms, same coefficients), and the cofactor is the constant
`1`. Since `poly_expr` is a deterministic function of its `IntPoly` input,
the kernel statement this bridge builds is literally `poly_expr(X) =
Rat.ofInt 1 * poly_expr(X)` for one specific `X` — a `mul_one`-shaped ring
fact true of ANY polynomial whatsoever, not one that discriminates Thales'
theorem from any other. The genuinely geometric coincidence — that "C lies
on the circle with diameter AB" and "CA ⟂ CB" expand to the IDENTICAL
polynomial — is checked only by a plain Rust `assert_eq!` in the translator
test, never by `Kernel::add_declaration`.

This is disclosed in full in the new fact's `axiom_footprint` (entry
`cas.thales-cofactor-is-refl-shaped-not-a-genuine-combination`) and in the
test doc comments. **I registered the fact anyway**, because it is not
content-free the way a hypothetical varignon sibling would be: the
translator still has to correctly transcribe a real six-variable, eight-term,
degree-2 polynomial, and `add_declaration` independently re-derives that the
transcription is a well-typed `Rat` expression obeying `left_distrib`/
`mul_assoc`/`Rat.ofInt_mul`. That is a real, if modest, assurance floor —
weaker than orthocentre's (which genuinely combines two DIFFERENT
polynomials additively, 16 terms merging to 8 with real cancellation), and
the difference is stated rather than hidden.

## Varignon: the hard look the brief asked for, and the verdict is NO reconstruction

Read directly from `artifacts/geometry-certificates/varignon-midpoint-parallelogram.json`:

```json
"coordinates": [],
"hypotheses": [],
"generators": [],
"conclusions": [
  {"id": "midlines-equal-x", "poly": {"terms": []}, "cofactors": []},
  {"id": "midlines-equal-y", "poly": {"terms": []}, "cofactors": []}
]
```

Every field that this bridge family's machinery translates from is empty.
The CAS's own `MvPoly` ring arithmetic has ALREADY fully cancelled the four
midpoint differences to the literal zero polynomial before a
`GeometryCertificate` is ever produced — the mathematical content (that the
midlines are equal vectors) lives entirely inside `axeyum_cas::mvpoly`'s
untrusted arithmetic, and by the time this bridge would see it there is
nothing left: no coordinate to universally quantify over, no hypothesis, no
cofactor, nothing to combine.

The only statement `prove_const_combination`/`rat_theorem` could build from
this certificate is `Rat.zero = Rat.zero` over **zero** free variables. It
would be well-formed, `Kernel::add_declaration` would admit it instantly,
and — this is the part that makes the "hard look" necessary rather than
optional — it would still satisfy `scripts/validate-facts.py`'s
`classify_cas_certificate_fact`: ADR-0601 §2's classifier only asks whether
some evidence row's `cargo test` names `-p axeyum-lean-kernel`, never what
that test actually checked. So registering
`F:varignon-midpoint-parallelogram-kernel-checked` would move the ledger's
`cas-certificate: kernel-reconstructed` counter from 14 to 15 while adding
**zero** bits of kernel-checked geometric content — exactly the failure this
repository's own standing rule names: "a checker that cannot fail is worse
than no checker... it does not slow the flywheel; it makes it manufacture
unfalsifiable claims at full speed."

**Verdict: no `F:varignon-midpoint-parallelogram-kernel-checked` fact was
registered, and none should be, on this route.** The parent fact
`F:geometry-varignon-midpoint-parallelogram` is untouched. If Varignon is
ever worth reconstructing through the kernel, it needs a DIFFERENT
construction entirely — one that builds the RAW midpoint arithmetic
(`Rat.div`/field division by the literal 2, well outside this bridge
family's "ambient ring expression over an already-canonical sparse
polynomial" design) and proves it reduces via `add_assoc`/`add_comm` to
`Rat.zero`, i.e. reconstructing the CAS's OWN cancellation rather than
consuming its already-cancelled output. That is a materially different
(and materially larger) task than anything this file's machinery does, and
it is out of scope here.

This is documented in code too: `cas_geometry_bridge_tests.rs`'s module doc
now carries a "Thales, added 2026-08-30, and Varignon, deliberately NOT
added" section making the same argument, so a future reader hits the
explanation before re-deriving the same "why not just reconstruct it"
question.

## What landed

`crates/axeyum-lean-kernel/src/rat_prelude/cas_geometry_bridge_tests.rs`
(same file orthocentre lives in, no new file, no new visibility changes --
this target needed literally nothing new): one certificate accessor
(`thales_certificate()`), 2 new tests (`translator_reads_the_thales_certificate_the_cas_produced`,
`geometry_thales_cofactor_identity_kernel_checked`), plus the module-doc
section above.

One new fact registered per ADR-0601 §2 (sibling, parent unmodified, scope
disclosed):

- `F:geometry-thales-cofactor-identity-kernel-checked`

    cas-certificate: 42 total -- kernel-reconstructed 14, cas-internal 28
    (up from 41 total -- 13/28 before this lane)

## Cost, measured

Debug, this host, through `scripts/cargo-serialized.sh`, uncontended:

| run | wall clock |
| --- | --- |
| `translator_reads_the_thales_certificate_the_cas_produced` alone | well under 1s |
| `geometry_thales_cofactor_identity_kernel_checked` alone | 7.60s |
| this module's 5-test sweep (orthocentre + thales together) | 7.57s-7.82s across two runs |
| full `rat_prelude::cas_` sweep (30 tests, all bridge modules) | 149.99s |

Cheapest kernel-reconstructed geometry theorem measured so far, as expected:
`prove_const_combination`'s recursion terminates after a single `prove_scale`
call and never reaches `add_poly`/`prove_merge`'s cancellation branch at all,
because there is exactly one generator. No numeral magnitude larger than the
certificate's own small integer coefficients (max magnitude 1) is ever
formed.

## Both checker_command directions verified

Verified standalone with `/usr/bin/grep -cE` explicitly (not the interactive
`ugrep`), both evidence rows:

- `kernel-reconstructed-thales-cofactor-identity`: real test name -> count
  1, exit 0; fabricated test name (`this_test_does_not_exist`) -> count 0,
  exit 1.
- `translator-checked-against-numbers-thales`: real test name -> count 1,
  exit 0; fabricated name -> count 0, exit 1.

## Next cheapest `cas-internal` target

Per `docs/plan/status/327-cas-geometry-pair.md`'s own measurement (not
re-verified independently by this lane, since the two targets it names
after thales/varignon were out of this lane's scope): `pappus-hexagon` (145
terms, 10-term max cofactor, `prove_mul` only, no fractional cast) is next;
`simson-line` (2010 terms, 324-term max cofactor) and `euler-line` (337
terms, 272 non-integer, 74-term max cofactor, needs both cast and
`prove_mul`) are the expensive remainder and should not be attempted without
measuring a smaller slice first.

With this lane's two targets closed (one reconstructed with disclosure, one
correctly left cas-internal), the geometry family's easy tier is exhausted:
every remaining `cas-internal` geometry certificate needs `prove_mul`
(non-constant cofactors) and most also need the fractional cast.

## Gates run (all foreground)

- `cargo check -p axeyum-lean-kernel --lib --tests` -- clean
- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib
  rat_prelude::cas_geometry_bridge_tests` -- **5 passed, 0 failed**
  (nonzero count confirmed), and again as part of the 30-test
  `rat_prelude::cas_` sweep across every bridge module -- **30 passed, 0
  failed** (149.99s; was 28 before this lane, +2 for the new tests)
- Both `checker_command`s re-run standalone through `/usr/bin/grep -cE`
  explicitly, BOTH directions (see above)
- `rustfmt --edition 2024 --check` on the touched file (after one `rustfmt`
  auto-format pass, no functional change), plus `cargo fmt --all --check`
  (workspace-wide, read-only) -- clean
- `scripts/cargo-serialized.sh clippy -p axeyum-lean-kernel --all-targets --
  -D warnings` -- clean
- `python3 scripts/validate-facts.py` -- **2220 facts, 0 errors**;
  `cas-certificate: 42 total -- kernel-reconstructed 14, cas-internal 28`

Not run: the aggregate gate (`just check`/`check.sh`), per the brief.

## Did NOT touch

`crates/axeyum-lean-kernel/src/nat_prelude/`, `int_prelude/`, `creal/`, and
`axeyum-cas` itself (read-only -- the translator only reads existing public
certificate fields via `axeyum_cas::geometry_certify::{certify,
geometry_limits}` and `axeyum_cas::geometry_corpus`, both already-public
APIs). `F:geometry-thales-right-angle-in-semicircle` and
`F:geometry-varignon-midpoint-parallelogram` are both unmodified. No new
file created (extended the existing `cas_geometry_bridge_tests.rs` rather
than adding a sibling module, since thales needed no visibility changes and
no new proof-emitting code). Nothing pushed.

<!-- plan-section: landed-changes -->

| 2026-08-30 | `e91e718a0` | draft: `cas_geometry_bridge_tests.rs` thales addition + varignon exclusion doc -- not yet compiled (committed within first 10 tool calls per lane protocol) |
| 2026-08-30 | `28a77b5c9` | feat: kernel-reconstruct thales cofactor identity, full disclosure of its refl-shaped obligation; register `F:geometry-thales-cofactor-identity-kernel-checked`; `cas-certificate` kernel-reconstructed 13 -> 14 |
