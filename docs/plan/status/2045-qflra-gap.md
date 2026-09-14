# Lane: qflra-gap — the `QF_LRA` board gap

<!-- plan-section: lane-status -->

**Lane block (`DONE`, qflra-gap, 2026-09-14).** [ADR-2045] closes the `QF_LRA`
bound hypothesis with a **clean, sized negative** and relocates the division's
gap onto one engine.

Census, re-derived on the current tree (200 files, 107/93, reproducing the
board's 107 exactly; `--trace` perturbs 0 rows): **74 of 93 undecided rows are
one route** — the offline dense-matrix LRA engine, **40 aborting** on its
allocation and **34 exhausting the clock** inside it. Two give-up labels had to
be split before counting and **both were wrong as written**: `kind=Timeout` is a
relabel whose detail contains `;`, and `lra.rs:159`'s
`"Fourier–Motzkin … exceeded the … budget"` is one string for every
`Decision::TimedOut` — **34 of 34 rows carrying it have `cube_matrices=0`;
Fourier–Motzkin never ran.** The 40 aborts emit no give-up line at all.

The A/B (one binary, two env values, 6 pinned pairs) is **net +0, 0 gains, 0
losses, 0 flips**, against a **row-level noise floor of 0 of 200**; aborts fall
41 → 9. Pre-registered R8 was ≥ +5, so **the lever ships `Off`**. The ordered
probe says why: on the 24 rows the admission screen had refused, **0 remain
refused, 21 reach the engine, 0 are newly decided** — the bound is not the wall.

**Next lane on this division starts here:** **50 of the 61 addressable rows
(82 %) are the offline dense engine**, and two unpriced allocations sit on that
path with no config change needed — `simplex::MAX_TABLEAU_CELLS` is not
consulted by `feasible_within`, and `lra.rs:944` builds an `n × nvars` dense
matrix that `Tableau::new` immediately re-sparsifies. The named capability wall
is `"online CDCL(T) LRA model did not replay (arithmetic outside the incremental
engine)"`.

**Method warning worth more than the result:** the reference pass first read
z3 = 155 against the board's 166 because it ran six concurrent shards on one
host. Re-taking only the rows it called "decided by nobody", on idle hosts,
decided **11 of 43** and restored z3 = 166 and gap = 59 exactly. **A "decided by
nobody" claim measured under load is not evidence** — it would have published a
50/43 split and an abort bucket "worth at most 11" instead of the true 61/32
and 20.

<!-- plan-section: landed-changes -->

| 2026-09-14 | `9467f0780` | qflra-gap: pre-registered rules + four-channel census harness, before any measurement aggregated |
| 2026-09-14 | `d248502a1` | qflra-gap: the census — 74 of 93 undecided `QF_LRA` rows are one offline dense engine; two give-up labels split and both wrong |
| 2026-09-14 | `49ea1d50d` | qflra-gap: A/B is a clean +0 at a 0-of-200 noise floor, and the arm itself causes five new aborts |
