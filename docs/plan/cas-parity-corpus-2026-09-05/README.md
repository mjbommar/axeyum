# CAS SymPy parity corpus

The second half of `docs/math-department/13-computer-algebra.md` item 10: a
SymPy parity corpus with ground truth independent of this repository, plus
a harness reporting per query the verdict, the trust classification, and
the wall time. (The first half, the per-function trust registry, landed
2026-09-05 as `scripts/check-cas-trust-registry.py`.)

**One entry disagrees, and it is the headline finding, not a bug in this
corpus**: `equal()` returns a confidently WRONG, `ZeroTest::Certified{equal:
false}` verdict for `sqrt(2)*sqrt(3)` vs `sqrt(6)` — two equal real numbers
the zero-test's atom algebra treats as provably different because it has no
`sqrt(a)*sqrt(b) = sqrt(a*b)` rewrite rule. See `e1-radical-cross-base`
below.

## Files

| file | what it is |
|---|---|
| [`ground_truth.py`](ground_truth.py) | independent verification of every checkable expected value in `corpus.json`: via SymPy 1.14.0 where installed, else pure-Python hand/cited proofs (75 claims with SymPy, 32 without — see "SymPy availability" below) |
| [`corpus.json`](corpus.json) | the corpus: 71 entries, one per query, each with its area, first-pass-module tag (if any), tier, expected value, and the method that established it |
| [`../../../crates/axeyum-cas/examples/parity_corpus.rs`](../../../crates/axeyum-cas/examples/parity_corpus.rs) | the harness: an `axeyum-cas` example (a workspace-member crate, unlike the SMT corpus's standalone `harness/`) that re-derives each `corpus.json` entry's query directly against `axeyum-cas`, compares to the expected value, and reports verdict / trust / wall time per entry |

## Design, and how it differs from the SMT capability corpus

This corpus follows
[`docs/plan/cas-smt-capability-2026-08-12/`](../cas-smt-capability-2026-08-12/README.md)'s
pattern (ground truth independent of the repository; a control for every
identity; entries chosen to include cases the subject is expected to get
wrong or decline) with two adaptations forced by the difference between an
SMT solver's verdict space (`sat`/`unsat`/`unknown`) and a CAS's:

1. **The corpus is data (`corpus.json`), not inline Rust.** The SMT harness
   hardcodes each query directly in `main.rs`; `axeyum-cas`'s public surface
   (calculus, algebra, number theory, and eight first-pass modules with
   distinct certificate types) is too heterogeneous for one generic query
   builder. `corpus.json` is the single ledger of expected values and their
   justification; the harness's per-entry Rust function reconstructs the
   same query against `axeyum-cas` and looks up the matching id by
   construction (the two are kept in sync by hand: a script cross-check run
   during development confirmed the two id sets are identical — 71 in each).
2. **Trust classification is derived per entry, not from a single verdict
   type.** Some `axeyum-cas` functions return a certificate object directly
   (`CertifiedIntegral`, `Enclosure`, `HomologyCertificate`,
   `TwoSquaresCertificate`, `FundamentalUnitCertificate`, `OrderCertificate`,
   `ConicFiveCertificate`, `DistancePreservingCertificate`,
   probability's `Certificate`/`Trust`, qe's self-verifying `eliminate`); for
   those, trust is read from that certificate's own `verify`/`is_certified`.
   Most functions (`differentiate`, `limit`, `series`, `sum_polynomial`,
   `solve`, `factor`, `factor_expr`, `gosper_sum`, `laplace_transform`,
   `z_transform`, matrix operations, `ntheory::*`) return a plain value with
   no certificate at all — per `scripts/check-cas-trust-registry.py`'s own
   rule, this is exactly what "uncertified" means. For these the harness's
   own correctness check commonly routes through `equal`/`ZeroTest`
   (differentiate a claimed antiderivative back and zero-test it, etc.);
   that `ZeroTest` — `Certified` or `Unknown` — is what the entry reports as
   its trust, since it is the actual re-checkable evidence the entry
   produced, exactly mirroring how `CertifiedIntegral`'s own certificate
   *is* an `equal` call under the hood. An entry with neither a native
   certificate nor a decisive `equal` check reports `uncertified` when it
   decided anything at all, `unknown` when the underlying function declined
   (`None`).

## Corrections this corpus made against its own first draft

Four of this corpus's first-draft entries were WRONG about `axeyum-cas`'s
actual behavior, found only by running the harness — exactly the discipline
CLAUDE.md's "before believing a result" rule asks for. Three turned out to
be flaws in the corpus, not the CAS; one is real:

- **`i4-gaussian-erf`** (was `i4-nonelementary`, expected a decline): a first
  draft assumed `integrate(e^{-x^2}, x)` would decline (no elementary
  closed form, Liouville). It does not — `axeyum-cas` has a dedicated
  Gaussian-integral route that returns `(sqrt(pi)/2) erf(x)`, matching
  SymPy exactly. Corrected to a `core`-tier entry expecting exactly that.
- **`solve3-quintic`** (expected `None`): `solve`'s own rustdoc documents
  that "complex roots and irreducible cubics+" are OMITTED from its result,
  not asserted absent. `solve(x^5-x-1, x)` returns `Some(vec![])`, which is
  the documented, honest (if easy to misread) behavior, not `None`.
  Corrected to expect `Some([])`.
- **`fps2-primes-decline`**: a first draft used only 10 primes, and
  `guess_linear_recurrence` found a spurious order-5 "recurrence" —
  Berlekamp-Massey can always fit `floor(len/2)` unknowns to `len` data
  points, so an order-5 fit on 10 numbers is a trivial overfit, not a
  finding. Fixed to use the same 13-term sample as `axeyum-cas`'s own
  `fps.rs` regression test, which correctly declines.
- **`e1-radical-cross-base`** (the one that stands): a first draft expected
  either `true` or an honest `Unknown` decline. Neither happened — `equal`
  returns `Certified{equal: false}`, printed with its witness via `{:?}` to
  confirm: the zero-test's atom algebra treats `sqrt(2)`, `sqrt(3)`,
  `sqrt(6)` as three independent atoms, so the witness polynomial
  `1*(sqrt:2)*(sqrt:3) - 1*(sqrt:6)` genuinely is nonzero *in that free
  algebra*, even though the real numbers it represents are equal. This is a
  certificate whose label (`Certified`) claims more than what it actually
  establishes — left as the corpus's one confirmed `disagree`.

## Areas and modules (measured 2026-09-05)

```sh
python3 -c "import json,collections; d=json.load(open('corpus.json')); print(collections.Counter(e['area'] for e in d if e.get('area')))"
python3 -c "import json,collections; d=json.load(open('corpus.json')); print(collections.Counter(e['module'] for e in d if e.get('module')))"
python3 -c "import json,collections; d=json.load(open('corpus.json')); print(collections.Counter(e['tier'] for e in d))"
```

| area | n | | area | n |
|---|---:|---|---|---:|
| differentiate | 6 | | number theory | 8 |
| integrate | 5 | | ODE | 3 |
| limit | 4 | | transforms | 3 |
| series | 6 | | | |
| sum | 3 | | **required-area total** | **51** |
| solve | 3 | | | |
| factor | 5 | | | |
| simplify/equal | 5 | | | |
| linear algebra | 4 | | | |

Every required area has at least 3 entries (the rule's floor); `series` and
`number theory` also each carry entries tagged with a first-pass module
(`fps`→series, `numberfield`→number theory), which is why area counts and
the raw per-area total exceed a naive 12×3=36.

| first-pass module | n |
|---|---:|
| fps | 2 |
| enclosure | 2 |
| qe | 3 |
| numberfield | 3 |
| permgroup | 2 |
| homology | 2 |
| probability | 3 |
| geometry_beyond | 4 |
| **total** | **21** (≥ 10 required) |

Tiers: **58 `core`**, **13 `decline_expected`** (≥ 10 required — each entry
cites a classical fact, a source-read capability boundary in `axeyum-cas`,
or this crate's own progress-log finding; see each entry's `justification`
in `corpus.json`).

Total entries: **71**.

## Running it

```sh
scripts/cargo-serialized.sh build -p axeyum-cas --example parity_corpus --release
./target/release/examples/parity_corpus
python3 docs/plan/cas-parity-corpus-2026-09-05/ground_truth.py
python3 -m py_compile docs/plan/cas-parity-corpus-2026-09-05/ground_truth.py
just bench-cas-parity   # registered; also registered in scripts/check.sh (see below)
```

## Measured results (2026-09-05, this host)

Harness, `--release`, single run:

```
entries: 71
verdict: agree=70 disagree=1 decline=0
trust:   certified=53 uncertified=11 unknown=7
total wall time: 177.541ms
```

The one `disagree` is `e1-radical-cross-base` (see above). Exit status is
therefore **1**, on purpose — CLAUDE.md's "make the exit status depend on
the finding" is the whole point of this corpus, and a checker that cannot
fail is worse than no checker.

**`ground_truth.py`**: with SymPy 1.14.0 installed (this host's system
Python has no SymPy; installed into a scratch venv with `uv venv` +
`uv pip install sympy` to run it), **75 claims, 0 failed**. Without SymPy
(plain `python3`, confirmed by re-running with the system interpreter),
**32 claims, 0 failed, exit 0** — every `qe`, `numberfield`, `permgroup`,
`homology`, `probability`, `geometry_beyond`, `fps`, `enclosure`, and
`number theory` claim is checked by pure-Python hand proofs
(`fractions.Fraction` exact arithmetic, brute-force permutation-group
closure, trial-division primality/factorization) with no SymPy dependency
at all; the calculus-heavy required areas (differentiate, integrate, limit,
series, sum, solve, factor, simplify/equal, linear algebra, ODE,
transforms) print `SKIP` and rely on `corpus.json`'s own `justification`
field (most of which also state a hand/cited component, e.g. the power
rule, expand-and-compare, or a cited theorem) rather than a from-scratch
symbolic re-derivation in this file. This is an honest, not a silent, gap:
every skip is printed and named.

**check.sh / justfile**: registered as `bench-cas-parity` in the `justfile`
unconditionally, and as `cas-parity-corpus` / `cas-parity-ground-truth` in
`scripts/check.sh` (177ms measured, far under the 60s threshold the task
sets for inclusion). **This means `scripts/check.sh` currently fails on
this step, by design, because of the confirmed `e1-radical-cross-base`
finding above** — not a flaky or nondeterministic step. A maintainer's next
move is one of: accept the finding and either fix `equal`'s atom algebra to
recognize `sqrt(a)*sqrt(b) = sqrt(a*b)` for concrete rational `a, b > 0`, or
document the scope limitation prominently enough that this entry's tier is
revisited; this corpus does not make that call unilaterally.

## Honesty caveats

- Wall times are single-run, single-host, un-pinned measurements — see
  CLAUDE.md's "Measuring anything" — use them only as "decided quickly"
  versus "took a while", never as a performance claim.
- SymPy is a general-purpose CAS with `sympy.stats`/`sympy.combinatorics`/
  etc. but no direct equivalent of `axeyum-cas`'s exact simplicial homology
  (Smith-form Betti numbers) or its bounded quantifier-elimination fragment
  in `qe`. Those entries are justified by cited classical facts (Betti
  numbers of standard spaces) or elementary hand arguments, not a SymPy
  call — noted per entry in `corpus.json` and in `ground_truth.py`.
- The corpus's own first draft was wrong about `axeyum-cas`'s behavior on
  four entries (see "Corrections" above) until the harness was actually
  run — this is exactly why the harness exists rather than a hand-argued
  capability table, and is recorded rather than quietly fixed.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-05 | Draft: directory, README skeleton, and file layout established. | commit `4f97ce7bc` |
| 2026-09-05 | 71-entry corpus, `ground_truth.py` (73 claims via SymPy 1.14.0), and the full harness landed; merged local `main` (`d8309e8b0`) cleanly. | commit `98d892caa` |
| 2026-09-05 | First harness run found 4 disagreements; 3 were corpus-design errors (`i4-nonelementary`→`i4-gaussian-erf`, `solve3-quintic`'s `None` vs `Some([])`, `fps2-primes-decline`'s undersized sample) fixed against the real behavior; 1 (`e1-radical-cross-base`) is a genuine, confirmed CAS finding, kept as the corpus's one `disagree`. `ground_truth.py` extended with pure-Python (no-SymPy) fallbacks for `qe`, `permgroup`, `probability`, `geometry_beyond` (75→still 75 claims with SymPy, 32 claims/exit 0 without). Registered `bench-cas-parity` in the `justfile` and `cas-parity-corpus`/`cas-parity-ground-truth` in `scripts/check.sh` (177ms, so `check.sh` now fails on the confirmed finding, by design). | `./target/release/examples/parity_corpus`: 71 entries, agree=70 disagree=1 decline=0, certified=53 uncertified=11 unknown=7, 177.541ms; `ground_truth.py`: 75/0 (SymPy) and 32/0 exit 0 (no SymPy); `cargo clippy -p axeyum-cas --example parity_corpus -- -D warnings`: clean |
