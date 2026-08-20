# Dual-checked Lemire witnesses for degrees 1 through 400

This directory retains the exact output of five deterministic sparse-search
jobs from source commit `6e1372073`, one job per authorized fleet host:

| Host | Degrees | Search time | Archive SHA-256 |
|---|---:|---:|---|
| s1 | 1–80 | 0.08 s | `dd43673565d4f2a5389da4788f1a250e436cbe370d5d74c91ab3d9453effe698` |
| s4 | 81–160 | 0.38 s | `6330a6308c697f850ca263cf8da72266924264f4810fd0c7f94381aef3c6e80e` |
| s5 | 161–240 | 0.79 s | `12f96ff1fb6f1405c838b37962bdecb4083ee3fa2a0ad77a91cf20a8f4e98212` |
| s6 | 241–320 | 2.40 s | `9f01003af8c2113f379228884d819b618836c7fd59fc5b0a1961279ed521c433` |
| s7 | 321–400 | 5.40 s | `0094d50ea3a2ca6a8976f886631d9ff91d0692c17a07b0aca3db20a7c9e3acf8` |

s1 did not have a Rust toolchain. It ran release binaries built from the exact
commit in the integration worktree; the search binary SHA-256 prefix is bound
in every s1 producer identity. s4–s7 cloned the pushed branch, required the
exact full commit hash, and built with `CARGO_BUILD_JOBS=2`. Every search was
single-threaded.

The admitted result is finite and exact:

- 400/400 degrees have canonical artifacts;
- 227 witnesses are trinomials, 172 are pentanomials, and degree 1 is `x`;
- all five shards report zero exhaustion and zero candidate-limit rows;
- 38,679 candidates were tested in total; degree 349 was the hardest at 870;
- each manifest binds its complete ordered degree population, policy, source
  identity, artifact basename, and child SHA-256; and
- the local admission pass rehashed every child and ran both the packed and
  independent dense-coefficient checker.

Run the repository gate with:

```sh
./scripts/check-gf2-lemire-range.sh
```

This establishes the conjecture for every degree `1 <= n <= 400` under the two
implemented checkers. It is not an inductive argument and does not establish
the universal conjecture.

## Derived cubic-composition families

The checked witnesses can also be audited as seeds for the theorem-backed
composition `f(x^3)`. Build the release binary and run:

```sh
find artifacts/gf2/lemire/range-1-400/shards \
  -type f -name 'degree-*.json' -print0 \
  | sort -z \
  | xargs -0 target/release/axeyum-gf2-capell-audit
```

The exact result is 138 criterion-positive seeds, 200 odd-degree structural
rejections, and 62 selected even witnesses whose roots are cubes. For each
positive seed the command produces a fresh certificate for `f(x^3)` and runs
both irreducibility checkers. Capell's criterion plus the retained 3-primary
order condition extends each positive seed to all degrees `d*3^k`. These 138
seeds occupy 95 distinct 3-free rays, not every degree; this derived result is
not a proof of the universal conjecture.
