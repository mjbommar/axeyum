# Lane: capability-assurance — the strand's own metric was unmeasurable

<!-- plan-section: lane-status -->

**The gate hosted CI calls "the authoritative gate for main" has never run, and
could not have** (`WIP`, capability-assurance, 2026-08-18).
`.github/workflows/ci.yml` deliberately keeps only the light checks and says
`scripts/local-ci.sh` is the real one — run on local hardware, because the ~32
z3/cvc5 differential-fuzz binaries starve on 4-core hosted runners. The reasoning
is sound. The gate is not:

```
cargo nextest --version          -> 101  no such command      (s4, s5, s7)
rustup run 1.88.0 cargo --version ->   1  not installed        (s4, s5, s7)
```

`cargo nextest run --profile local --workspace --all-features` *is* the test
sweep, and every step is `run … || rc=$?`, so it would not have stopped — it
would have carried on with the two central steps never executing. Four
independent signals say it had never run at all: `artifacts/local-ci/` absent,
the isolated target dir absent, no crontab and no user systemd timer, and four
tracked files mentioning it, none an entry point. `provision-fleet-host.sh`
installs none of the three prerequisites. **`main` has no heavy pre-merge gate
and has not had one.**

Detail and older landed rows moved to [`../notes/99-capability-assurance.md`](../notes/99-capability-assurance.md).

<!-- plan-section: landed-changes -->

| 2026-08-18 | `pending` | `scripts/cargo-serialized.sh`: heavy cargo now takes an flock and a memory ceiling, because "serialize" was prose and prose does not hold a lock (two dev boxes downed, one agent session OOM-killed). **`MemoryMax` alone does not bite** — it *is* applied (`memory.max` = 67108864) and a 400 MB allocation still succeeds by swapping, on a box whose 7 G of swap is 6 G full. With `MemorySwapMax=0` the same allocation is SIGKILLed by the cgroup (137), host untouched. `--self-check` proves it per host and discriminates: `AXEYUM_CARGO_SWAP=1G` flips it to `SURVIVED`, exit 1. |
| 2026-08-18 | `pending` | `local-ci.sh`, the declared authoritative gate for `main`, cannot run on any fleet host and never has (`cargo nextest` 101, `rustup run 1.88.0` 1, on s4/s5/s7). Now refuses to start rather than limp, `--record` leaves a tracked per-(sha,host) JSON, and `provision-fleet-host.sh` installs the prerequisites (`1.88.0` needs `--profile minimal`, else rustup fails on `miri`/`cranelift` inherited from the nightly profile). The record carries per-step TEST COUNTS and marks a step that exited 0 having run zero tests as `vacuous`. |
