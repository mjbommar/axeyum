# Versioned corpus manifests

`axeyum-bench` artifact version 20 can bind a run to a versioned corpus
manifest. This is the ingestion boundary for the Glaurung QF_BV client tier:
timing does not begin until the harness proves that the directory contains
exactly the declared queries and that every query still has its declared
SHA-256 digest.

Use a manifest when a result is intended to be reproducible or compared across
commits:

```sh
cargo run --release -p axeyum-bench --features z3 -- \
  /path/to/corpus \
  --corpus-manifest /path/to/manifest-v1.json \
  --corpus-tier representative \
  --backend sat-bv --compare-z3
```

The committed [micro manifest](../../corpus/micro/manifest-v1.json) exercises
the contract, but it is an ingestion smoke and **not** binary-analysis
performance evidence.

## Manifest v1

```json
{
  "version": 1,
  "name": "glaurung-qfbv-2026-07-v1",
  "source": "Glaurung shadow-diff capture; commit and capture procedure here",
  "logic": "QF_BV",
  "files": [
    {
      "path": "handlers/example-0001.smt2",
      "content_hash": "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
      "expected": "sat",
      "family": "register-slice",
      "tiers": ["representative", "full"]
    }
  ]
}
```

The fields are deliberately strict:

- `version` is exactly `1`.
- `name`, `source`, and `logic` are non-empty. `source` should identify the
  producer revision and capture procedure, not merely say “local corpus.”
- `files` is non-empty and has no duplicate paths.
- `path` is a normalized, relative, `/`-separated `.smt2` path. Absolute paths,
  `.`/`..`, empty segments, and backslashes are rejected.
- `content_hash` is `sha256:` followed by 64 lowercase hexadecimal digits.
  Generate the digest from the query bytes, for example with
  `sha256sum query.smt2`.
- `expected` is `sat` or `unsat` and comes from the capture's trusted
  shadow-diff result. It is checked independently of optional SMT-LIB
  `:status` metadata.
- `family` and every `tiers` entry use ASCII letters, digits, `.`, `_`, or `-`.
  Each query belongs to at least one named tier.

Before solving, the harness reads and hashes **all** manifest entries and walks
the corpus root. Missing, modified, duplicate, or unlisted `.smt2` files fail
the run. A selected tier changes only which already-validated entries are
solved; it cannot hide drift elsewhere in the pack. Manifest order is the run's
stable instance order.

`--limit` is intentionally incompatible with a manifest because an anonymous
prefix is not a reproducible tier. Use `--corpus-tier representative` for a
small regular gate and `--corpus-tier full` for the scheduled run. A tier that
selects no entries fails. `--corpus-source` and `--logic`, when also supplied on
the command line, must exactly match the manifest.

## Artifact and acceptance gate

The artifact records the manifest's own SHA-256 digest, name, source, logic,
selected tier, total and selected entry counts, selected family/tier counts, and
each instance's path, digest, expected verdict, family, and tier membership. The
config hash includes the manifest digest and selected tier, so changing metadata
or expectations changes the experiment identity even if query bytes do not.

For every selected entry, `summary.manifest` records `expected`, `compared`,
`agree`, and `disagree`. A manifest-backed run exits nonzero unless every
expected verdict is compared and all agree. This gate composes with the
decided-rate, operational-error, model-replay, SMT-LIB `:status`, and Z3-oracle
gates; it does not replace any of them.

For the Glaurung client lane, publish performance only when the full acceptance
boundary in [Benchmarks](benchmarks.md) passes. A valid manifest proves corpus
identity, not representativeness: the shadow-diff exporter still has to sample
the real width-mixed, extract/concat-heavy, memory-derived query distribution.
