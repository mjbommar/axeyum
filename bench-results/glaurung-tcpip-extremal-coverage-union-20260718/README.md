# tcpip extremal-model authority coverage union

ADR-0238's preregistered campaign is accepted on its exact bounded protocol.
The result establishes deterministic two-policy union parity under sole Z3 and
sole Axeyum authority. It does not establish exhaustive model or finding
coverage.

## Fixed identities

- Axeyum preregistration commit:
  `6a38079925f6b3c3a76e909138a3b975978b239d`
- Glaurung experiment commit:
  `e5622623ba8d8679d7e4530ff34212a5d993f030`
- tcpip SHA-256:
  `ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`
- Sole-Z3 binary SHA-256:
  `d5d75a683c16b18aaa8015859a42c565f946df95a47bdabd1b3ac0c492575f38`
- Sole-Axeyum binary SHA-256:
  `e5c14c8fdefb708cd2f856e999bbb4ac40cbeb971b32695b89636dd7f0b4ae2e`
- Fixed work: first 15 of 338 reachable functions, 250 ms check wall,
  300,000-solve budget, 1,800-second process wall, and three order-balanced
  repetitions per policy and authority.

## Result

The arbitrary-model control remains rejected: Z3 authority emits 128 stable
findings, Axeyum authority emits 126, and the two Z3-only rows reproduce the
prior divergence. The least-unsigned control reproduces its exact 110-finding
hash and all prior solve/canonical-choice counters.

The new greatest-unsigned policy emits the same ordered 84 findings under both
authorities in all six processes. Each authority records exactly 34,659 solves,
513 canonical attempts/completions, 33,858 probes, and zero infeasible,
inconclusive, unsupported, unknown, or error choices per repetition.

The accepted least/greatest union has 125 findings:

- 69 appear under both policies;
- 41 are least-only;
- 15 are greatest-only.

The arbitrary-model combined union has 128 findings. Comparing it with the
extremal union yields 95 shared, 33 arbitrary-only, and 30 extremal-only rows.
This negative overlap result is important: two deterministic extrema improve
reproducibility and expose additional rows, but do not preserve or subsume the
arbitrary-model population.

## Artifact hashes

- `any-model-report.json`:
  `ff057e876ec6086b7065a5599e6a4573b762d604a406a7512e347af04aa60a4a`
- `min-unsigned-report.json`:
  `3dc7644d9edd169dbe171c15e1bed70c7fcba92346d15954cd97027fdd26933a`
- `max-unsigned-report.json`:
  `2e1063de3d9bbb18bd91b30dfb86e3a350ec86f74890e9a18229cf85d1325e20`
- `coverage-union-report.json`:
  `6040c9f87ef34e44fc3f597ae792cc4172c032f9d670229f3f8ae76b0f381fa4`

The JSON reports retain every ordered finding, policy-only partition, source
and binary identity, solve count, canonical-choice reason, and process result.
The empty stdout logs and expected any-model stderr rejection are retained as
runner provenance. Standalone policy-process times are not solver-performance
evidence because policy-dependent probe counts change the work.
