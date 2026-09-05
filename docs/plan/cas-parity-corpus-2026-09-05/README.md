# CAS SymPy parity corpus

The second half of `docs/math-department/13-computer-algebra.md` item 10: a
SymPy parity corpus with ground truth independent of this repository, plus a
harness reporting per query the verdict, the trust classification, and the
wall time. (The first half, the per-function trust registry, landed
2026-09-05 as `scripts/check-cas-trust-registry.py`.)

**STATUS: DRAFT, in progress.** This file is being filled in as the corpus
and harness are built; see the Progress log at the bottom for what is real
right now versus still to come.

## Files

| file | what it is |
|---|---|
| [`ground_truth.py`](ground_truth.py) | independent verification of every expected value in `corpus.json`, via SymPy 1.14.0 where applicable, else a hand proof or a cited classical identity written into the entry itself. Imports nothing from this repository. |
| [`corpus.json`](corpus.json) | the corpus: one entry per query, with its area, its first-pass-module tag (if any), its tier, its expected value, and the method that established it |
| [`../../../crates/axeyum-cas/examples/parity_corpus.rs`](../../../crates/axeyum-cas/examples/parity_corpus.rs) | the harness: an `axeyum-cas` example (workspace member, unlike the SMT corpus's standalone `harness/`) that re-derives each `corpus.json` entry's query directly against `axeyum-cas`, compares to the expected value, and reports verdict / trust / wall time per entry |

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
   same query against `axeyum-cas` and looks up `corpus.json` by `id` to
   compare. The two are kept in sync by hand — a corpus.json entry with no
   matching harness function, or vice versa, is a gate failure (see
   `--selftest`-equivalent check below).
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
   rule, this is what "uncertified" means (a computed answer with no
   attached checkable witness). For these the harness's own correctness
   check commonly routes through `equal`/`ZeroTest` (differentiate a claimed
   antiderivative back and zero-test it, substitute a claimed root, etc.);
   that `ZeroTest` — `Certified` or `Unknown` — is what the entry reports as
   its trust, since it is the actual re-checkable evidence the entry
   produced, exactly mirroring how `CertifiedIntegral`'s own certificate
   *is* an internal `equal` call. An entry with neither a native certificate
   nor a decisive `equal` check reports `uncertified` when it decided
   anything at all, `unknown` when the underlying function declined
   (returned `None`).

## Areas and modules

Twelve required areas (`differentiate`, `integrate`, `limit`, `series`,
`sum`, `solve`, `factor`, `simplify/equal`, `linear algebra`, `number
theory`, `ODE`, `transforms`), each with at least 3 entries; at least 10
entries drawn from the eight first-pass modules (`fps`, `enclosure`, `qe`,
`numberfield`, `permgroup`, `homology`, `probability`, `geometry_beyond`);
at least 10 entries this corpus *expects* `axeyum-cas` to decline or
disagree on, each citing the classical fact, the source-code limitation
found by reading the module, or the progress-log finding that predicts it.
See `corpus.json` for the full, current table — this README is not
duplicating counts that will go stale; run the count commands in "How to
re-measure" instead.

## How to run it

```sh
scripts/cargo-serialized.sh run -p axeyum-cas --example parity_corpus --release
python3 docs/plan/cas-parity-corpus-2026-09-05/ground_truth.py   # must exit 0
python3 -m py_compile docs/plan/cas-parity-corpus-2026-09-05/ground_truth.py
```

## How to re-measure

```sh
python3 -c "import json,collections; d=json.load(open('docs/plan/cas-parity-corpus-2026-09-05/corpus.json')); c=collections.Counter(e['area'] for e in d if e.get('area')); print(c)"
python3 -c "import json,collections; d=json.load(open('docs/plan/cas-parity-corpus-2026-09-05/corpus.json')); c=collections.Counter(e['module'] for e in d if e.get('module')); print(c, sum(1 for e in d if e.get('module')))"
python3 -c "import json; d=json.load(open('docs/plan/cas-parity-corpus-2026-09-05/corpus.json')); print(sum(1 for e in d if e['tier']=='decline_expected'), 'decline-expected of', len(d))"
```

## Honesty caveats

- Wall times are single-run, single-host, un-pinned measurements — see
  CLAUDE.md's "Measuring anything" — use them only as "decided quickly"
  versus "took a while", never as a performance claim.
- Some entries' "expected" was pinned only after running the harness once
  and reading what `axeyum-cas` actually does (e.g., whether a given
  transcendental `equal` call decides or declines) rather than purely from
  an a-priori guess; every such entry says so in its `corpus.json`
  `justification` field and is still independently checked in
  `ground_truth.py` — the corpus records what SymPy (or a hand proof) says
  is *true*, which is a fact about mathematics, not about `axeyum-cas`'s
  behavior, and is unaffected by which way the harness's empirical
  discovery went.
- SymPy is a general-purpose CAS with `sympy.stats`/`sympy.combinatorics`/etc.
  but no direct equivalents of some `axeyum-cas` first-pass modules (exact
  simplicial homology from a boundary-matrix Smith form, this crate's
  qe/QE fragment). Those entries are justified by cited classical facts
  (Betti numbers of standard spaces, Abel–Ruffini, Fermat/Euler two-squares)
  written out in `ground_truth.py`, not by a SymPy call — noted per entry.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-05 | Draft: directory, README skeleton, and file layout established. `corpus.json` and the harness are being filled in next. | this file |
