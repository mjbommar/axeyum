# Host setup & machine-transition checklist

What a fresh machine (e.g. **s4**, `192.168.1.114`, 192 GB-class RAM + 2× GPUs)
needs to continue the plan. The git repo carries all source + committed
artifacts; the heavy inputs below are **gitignored** and must be re-fetched.

## 0. Get the code (the only thing that holds this session's work)

All plan work lives on the branch **`docs/readme-plan-parity-roadmap`** (pushed to
`origin` = `github.com/mjbommar/axeyum.git`). On the new host:

```sh
git clone https://github.com/mjbommar/axeyum.git
cd axeyum
git checkout docs/readme-plan-parity-roadmap
```

Then read [`STATUS.md`](../../STATUS.md) for the current focus and
[`PLAN.md`](../../PLAN.md) for the map. (Alternatively, `rsync` the whole working
tree to skip the re-fetches in steps 2–3 — ~43 GB including `references/` +
`corpus/public/`.)

## 1. Toolchain

- **Rust**: nightly is the local default (CLAUDE.md); CI uses stable + **MSRV
  1.85**, edition 2024, resolver 3. `rustup toolchain install nightly stable`.
  (Reference: this session used `rustc 1.98.0-nightly`.)
- **just** (optional; `scripts/check.sh` is the no-`just` fallback gate) and
  **cargo-deny** (`cargo install just cargo-deny`).
- **Z3 4.13.x** — `libz3-dev` (pkg-config `z3`) for the `--features z3` oracle,
  plus the `z3` binary for differential cross-checks. The default build needs no
  C/C++; Z3 is a feature-gated leaf (ADR-0002).

## 2. References (1.6 GB, gitignored) — for reading the reference solvers

```sh
scripts/fetch-references.sh   # clones z3, cvc5, bitwuzla, cadical, kissat,
                              # lean4, nanoda_lib, carcara, drat-trim, … into references/
```
Needed when implementing against the reference distillations in
[`docs/plan/references/`](references/README.md).

## 3. Public corpus (41 GB, gitignored) — only for public benchmarks

```sh
scripts/fetch-corpus.sh qf_bv   # → corpus/public/  (SMT-LIB 2024, Zenodo 11061097)
```
**Not required** for the committed measurement slice `corpus/qfbv-curated/` (36
files, in-repo). Fetch only when running the public-corpus `just bench-public-*`
recipes.

## 4. Verify the build

```sh
./scripts/check.sh    # fmt + clippy -D warnings + test + doc + link check
# or, memory-bounded:
CARGO_BUILD_JOBS=4 cargo test --workspace
```

## 5. Memory hygiene (the lesson from the 26–32 GB host)

The agent's parent process was OOM-killed twice by unbounded bench workers (a
single QF_BV instance can balloon Z3/sat-bv memory). **On any host, cap bench
worker memory** so a runaway solve cannot take down the session:

```sh
# Per-process address-space cap (e.g. 8 GB) around the bench:
( ulimit -v 8000000; cargo run -p axeyum-bench --features z3 -- corpus/qfbv-curated \
    --backend sat-bv --compare-z3 --timeout-ms 2000 --jobs 2 --out <artifact>.json )
# or run under systemd-run --scope --property=MemoryMax=16G  …
```
Also: `CARGO_BUILD_JOBS=4` for builds; scale `--jobs` to RAM, not core count
(each worker = one sat-bv + one Z3, each possibly multi-GB). The harness now gives
each worker a 512 MB **stack** (reserved, not committed) to survive deeply-nested
terms — that is orthogonal to the heap OOM above.

## 6. GPUs (s4) — optional, feature-gated, not yet built

See [`docs/research/03-architecture/gpu-accelerated-untrusted-search.md`](../research/03-architecture/gpu-accelerated-untrusted-search.md).
Before any GPU work: `nvidia-smi` (driver + VRAM), and decide the path —
**CUDA** (C++, feature-gated leaf only, per ADR-0002) vs **wgpu/Vulkan**
(pure-Rust, keeps the no-C/C++ identity). The highest-ROI GPU targets are
inprocessing (BVE/subsumption) and local search — both pure *untrusted search*,
so GPU bugs are caught by CPU replay/DRAT. This is a future track, not scheduled
until the CPU foundation (P1.1–P1.5) is measured.

## Transition summary (do before leaving the old host)

1. Commit all pending work. 2. **Push** `docs/readme-plan-parity-roadmap` to
   `origin` (else the session's work — the whole plan, P3.0/T1.1.1/T1.1.2,
   ADR-0031 — is lost; it is a local branch). 3. On s4: clone, checkout the
   branch, run steps 1–5, then resume from [`STATUS.md`](../../STATUS.md).
