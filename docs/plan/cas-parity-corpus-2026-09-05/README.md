# CAS SymPy parity corpus

The second half of `docs/math-department/13-computer-algebra.md` item 10: a
SymPy parity corpus with ground truth independent of this repository, plus
a harness reporting per query the verdict, the trust classification, and
the wall time. (The first half, the per-function trust registry, landed
2026-09-05 as `scripts/check-cas-trust-registry.py`.)

**Update, item 10 wave two (2026-09-05): the `known_defect` this section
used to describe is FIXED.** `equal()` used to return a confidently WRONG,
`ZeroTest::Certified{equal: false}` verdict for `sqrt(2)*sqrt(3)` vs
`sqrt(6)` — two equal real numbers the zero-test's atom algebra treated as
provably different because it had no `sqrt(a)*sqrt(b) = sqrt(a*b)` rewrite
rule. Lane `cas-witness` landed the fix (file 13, item 1 wave two) and the
Rust harness was updated at the time, but `corpus.json`'s own `tier` field
for `e1-radical-cross-base` was never updated to match and stayed
`known_defect` — a silent drift between the two ledgers, found and
corrected during wave two. `e1-radical-cross-base` is now a plain `core`
entry, `known_defect` is empty (`known_defect=0`), and the tier mechanism
described below is kept ready for the next one, not deleted.

## Files

| file | what it is |
|---|---|
| [`ground_truth.py`](ground_truth.py) | independent verification of every checkable expected value in `corpus.json`: via SymPy 1.14.0 where installed, else pure-Python hand/cited proofs (129 claims with SymPy, 75 without — see "SymPy availability" below) |
| [`corpus.json`](corpus.json) | the corpus: 119 entries, one per query, each with its area, module tag (if any), tier, expected value, and the method that established it |
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
   during development confirmed the two id sets are identical — 119 in
   each, re-verified after item 10 wave two's 48-entry growth).
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

## The `known_defect` tier

A third tier alongside `core` and `decline_expected`. It exists for exactly
one situation: a confirmed, real wrong answer whose fix is owned elsewhere
and in flight, where reddening every session's aggregate gate on this box
for a defect nobody dispatched here would just get the whole corpus muted
or skipped. A `known_defect` entry in `corpus.json` carries:

- `expected`: the true answer (as always).
- `observed_wrong_answer`: the specific wrong answer `axeyum-cas` gives,
  recorded so a reader does not have to re-derive it from the harness's
  doc comment.
- `tracked_by`: a string naming who owns the fix (here, `"file 13, item 1
  wave two, lane cas-witness"`).

The harness (`main`'s loop) excludes `known_defect` entries from the
`agree`/`disagree`/`decline` tally that drives most of the exit status —
but it does not let the entry rot unexamined. It still runs the entry's
check every time and asserts the wrong answer **persists**
(`outcome.verdict == Verdict::Disagree`); the instant it does not — the
fix landed, or something else changed the behavior — the harness prints
`FATAL: known defect <id> now agrees: reclassify it to core` and exits
nonzero. A known defect can only ever be (a) still reproducing, silently,
or (b) fixed, loudly demanding reclassification. It cannot silently stop
mattering.

## Corrections this corpus made against its own first draft

Five of this corpus's first-draft entries were WRONG about `axeyum-cas`'s
actual behavior, found only by running the harness — exactly the discipline
CLAUDE.md's "before believing a result" rule asks for. Four turned out to
be flaws in the corpus, or the tool changing under it; one is a real,
standing finding:

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
- **`qe3-large-coefficient`** (was `qe3-overflow-decline`, expected a
  decline): after the four corrections above were committed, a routine
  `git merge main` (local) pulled in `docs/math-department/13-computer-algebra.md`
  item 7's "wave two" — `qe`'s `Atom` coefficients were widened from
  `i128`-backed `Rational` to `BigRational`, fixing exactly the Cauchy-bound
  overflow this entry was built to document (`x^2 - 10^30 = 0` used to
  return `Unknown`; it now returns a certified `true`, correctly). Rebuilding
  after the merge broke the entry's type (a compile error, not a silent
  drift) and running it showed the capability gain directly. Corrected to a
  `core`-tier entry expecting the certified `true`. This is the sharpest
  illustration of why this corpus has to be re-run rather than trusted from
  a stale capability table: the underlying tool changed mid-development, and
  the corpus caught it because it re-derives against the live crate every
  time, not because anyone remembered to update a comment.
- **`e1-radical-cross-base`** (the one that stands): a first draft expected
  either `true` or an honest `Unknown` decline. Neither happened — `equal`
  returns `Certified{equal: false}`, printed with its witness via `{:?}` to
  confirm: the zero-test's atom algebra treats `sqrt(2)`, `sqrt(3)`,
  `sqrt(6)` as three independent atoms, so the witness polynomial
  `1*(sqrt:2)*(sqrt:3) - 1*(sqrt:6)` genuinely is nonzero *in that free
  algebra*, even though the real numbers it represents are equal. This is a
  certificate whose label (`Certified`) claims more than what it actually
  establishes — reclassified `known_defect`, `tracked_by` "file 13, item 1
  wave two, lane cas-witness" (see "The `known_defect` tier" above), the
  corpus's one confirmed, owned finding.

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

The table above is the FIRST-PASS snapshot. Item 10 wave two (2026-09-05)
added 48 more entries, at least 3 per second/third-pass module named in the
brief, each with a near-miss control and ground truth independent of this
repository (SymPy or hand/cited, see `ground_truth.py`):
`enclosure_special` 5, `fps_analytic` 4, `numberfield_ideals` 4,
`permgroup_sylow` 4, `homology_coefficients` 4, `homology_cohomology` 4,
`homology_induced` 3, `homology_persistent` 4, `qe_big` 4 (indirect, through
the public `qe::eliminate`/`eliminate_forall` front door — `qe_big` itself
declares no public items), `qe_dnf` 4, `qe_bivariate` 4, plus 4 more tagged
`probability` for the symbolic-lambda Poisson claims (item 9 wave two: total
mass, mean, and variance all now certify with a SYMBOLIC rate).

Tiers: **109 `core`**, **10 `decline_expected`** (≥ 10 `decline_expected`
required — each entry cites a classical fact, a source-read capability
boundary in `axeyum-cas`, or this crate's own progress-log finding; see
each entry's `justification` in `corpus.json`). `known_defect` is empty:
wave two found `e1-radical-cross-base`'s tier field in `corpus.json` was
STALE at `known_defect` even though the Rust harness already treats it as
a plain `core` agree (the fix landed under lane `cas-witness` and the
harness was updated, but `corpus.json`'s copy never was) — corrected here
so the two ledgers agree again.

Total entries: **119** (was 71 before wave two).

## Running it

```sh
scripts/cargo-serialized.sh build -p axeyum-cas --example parity_corpus --release
./target/release/examples/parity_corpus
python3 docs/plan/cas-parity-corpus-2026-09-05/ground_truth.py
python3 -m py_compile docs/plan/cas-parity-corpus-2026-09-05/ground_truth.py
just bench-cas-parity   # registered; also registered in scripts/check.sh (see below)
```

## Measured results (2026-09-05, this host, item 10 wave two)

Harness, `--release`, single run, after the wave-two growth (48 new entries
covering `enclosure_special`, `fps_analytic`, `numberfield_ideals`,
`permgroup_sylow`, `homology_coefficients`/`cohomology`/`induced`/`persistent`,
`qe_big`/`qe_dnf`/`qe_bivariate`, and the symbolic-lambda Poisson claims — see
the progress log's last row):

```
entries: 119
verdict: agree=119 disagree=0 decline=0 known_defect=0
trust:   certified=99 uncertified=14 unknown=6
total wall time: 330.833ms
```

`known_defect=0` because `e1-radical-cross-base` (see above) was fixed by
lane `cas-witness` and reclassified to `core` before this pass; the tier
and its reclassify-when-it-stops-reproducing alert are kept in the harness
for the next one. Exit status is **0**. CLAUDE.md's "make the exit status
depend on the finding" still holds: any future known defect's entry would
still assert the wrong answer persists every run and exit nonzero the
instant it does not.

**`ground_truth.py`**: with SymPy 1.14.0 installed (this host's system
Python has no SymPy; installed into a scratch venv with `uv venv` +
`uv pip install sympy` to run it), **129 claims, 0 failed** (was 75 before
wave two). Without SymPy (plain `python3`, confirmed by re-running with the
system interpreter), **75 claims, 0 failed, exit 0** (was 32) — every `qe`,
`numberfield`, `permgroup`, `homology`, `probability`, `geometry_beyond`,
`fps`, `enclosure`, `enclosure_special`, `fps_analytic`,
`numberfield_ideals`, `permgroup_sylow`, `homology_coefficients`,
`homology_cohomology`, `homology_induced`, `homology_persistent`, `qe_big`,
`qe_dnf`, `qe_bivariate`, and `number theory` claim is checked by pure-Python hand proofs
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
`scripts/check.sh` (194.7ms measured, far under the 60s threshold the task
sets for inclusion). **This step now exits 0**: `e1-radical-cross-base` is
tier `known_defect`, tracked by lane `cas-witness` (file 13 item 1 wave
two), so it is excluded from the tally that drives the exit status while
its fix is in flight elsewhere — but the harness still asserts the wrong
answer persists every run, and will exit nonzero with a reclassify message
the moment `equal` starts agreeing without this corpus itself being
updated to match.

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
| 2026-09-05 | First harness run found 4 disagreements; 3 were corpus-design errors (`i4-nonelementary`→`i4-gaussian-erf`, `solve3-quintic`'s `None` vs `Some([])`, `fps2-primes-decline`'s undersized sample) fixed against the real behavior; 1 (`e1-radical-cross-base`) is a genuine, confirmed CAS finding, kept as the corpus's one `disagree`. `ground_truth.py` extended with pure-Python (no-SymPy) fallbacks for `qe`, `permgroup`, `probability`, `geometry_beyond` (75 claims with SymPy, 32 claims/exit 0 without). Registered `bench-cas-parity` in the `justfile` and `cas-parity-corpus`/`cas-parity-ground-truth` in `scripts/check.sh`. | `./target/release/examples/parity_corpus`: 71 entries, agree=70 disagree=1, 177.5ms |
| 2026-09-05 | Merged local `main` again (picked up `docs/math-department/13-computer-algebra.md` item 7 "wave two" and item 3 "wave two", `b4d6c9465`): `qe`'s `Atom` widened from `i128`-backed `Rational` to `BigRational` coefficients, a source-level break in `qe1`/`qe2`/`qe3` fixed by switching to `BigRational::from_integer`. Rebuilding after the fix found `qe3-overflow-decline` had flipped from a documented decline to a correct, certified `true` (the exact overflow it was built to test was fixed by the same merge) — renamed `qe3-large-coefficient`, reclassified `core`. | `./target/release/examples/parity_corpus`: 71 entries, agree=70 disagree=1 decline=0, certified=54 uncertified=11 unknown=6, 321.540ms |
| 2026-09-05 | Added the `known_defect` tier (coordinator request, ahead of merging lane `cas-witness`'s fix for `e1-radical-cross-base`): `corpus.json` gained `tracked_by`/`observed_wrong_answer` fields, and the harness excludes `known_defect` entries from the `agree`/`disagree`/`decline` tally but asserts the wrong answer PERSISTS every run, exiting nonzero with a reclassify-to-`core` message the instant it does not (verified by a temporary injected fix simulating the entry agreeing: the harness printed `FATAL: known defect e1-radical-cross-base now agrees: reclassify it to core` and exited 1, then the injection was reverted). `e1-radical-cross-base` moved from `decline_expected` to `known_defect`, `tracked_by` "file 13, item 1 wave two, lane cas-witness". `scripts/check.sh`'s registered step now exits 0 rather than reddening the shared gate. | `./target/release/examples/parity_corpus`: 71 entries, agree=70 disagree=0 decline=0 known_defect=1, certified=54 uncertified=11 unknown=6, 194.716ms; corpus.json tiers now 59 core / 11 decline_expected / 1 known_defect; `cargo clippy -p axeyum-cas --example parity_corpus -- -D warnings`: clean; `rustfmt --edition 2024 --check`: clean; `python3 -m py_compile ground_truth.py`: OK |
| 2026-09-05 | **Item 10 wave two, part (b)** (lane `cas-trust-2`): 48 new entries covering every second/third-pass module the brief named that this corpus predates -- `enclosure_special` (5), `fps_analytic` (4), `numberfield_ideals` (4), `permgroup_sylow` (4), `homology_coefficients` (4), `homology_cohomology` (4), `homology_induced` (3), `homology_persistent` (4), `qe_big` (4, indirect through `qe::eliminate`/`eliminate_forall` since `qe_big` itself has no public items), `qe_dnf` (4), `qe_bivariate` (4), and 4 more tagged `probability` for the symbolic-lambda Poisson claims (item 9 wave two). Every entry's expected value is independent of this repository (SymPy 1.14.0 in a scratch venv, or a cited/hand proof), and every identity carries a near-miss control. **Found and fixed a pre-existing drift**: `corpus.json`'s `e1-radical-cross-base` was still tiered `known_defect` with `tracked_by`/`observed_wrong_answer` fields, even though the Rust harness had already been fixed and reclassified it to a plain `core` agree when lane `cas-witness` landed the underlying fix -- the two ledgers had silently diverged. Corrected `corpus.json` to match. No `disagree` among the 119 entries. | `./target/release/examples/parity_corpus`: 119 entries, agree=119 disagree=0 decline=0 known_defect=0, certified=99 uncertified=14 unknown=6, 330.833ms; corpus.json tiers now 109 core / 10 decline_expected / 0 known_defect; id sets match exactly (119/119); `python3 ground_truth.py`: 129 claims (SymPy)/75 claims (no SymPy), 0 failed both; `cargo clippy -p axeyum-cas --example parity_corpus -- -D warnings`: clean; `rustfmt --edition 2024 --check`: clean; `python3 -m py_compile ground_truth.py`: OK |
