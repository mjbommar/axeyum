# Lane: capability-assurance — the strand's own metric was unmeasurable

<!-- plan-section: lane-status -->

**Open queue, in the order I intend to clear it** (`WIP`,
capability-assurance, 2026-08-19). Two items cleared themselves while it stood,
by the lanes that owned them — a queue listing resolved work is the same defect
as stale prose, so they are struck rather than carried.

1. **`hooks/pre-push` runs `cargo test -p axeyum-lean-kernel` WHOLESALE**
   (line 260), and that package gained two real-Lean suites today —
   `real_lean_creal_carrier_kernel_replay` (~62 s) and
   `real_lean_wellfounded_elaborator_divergence` (~115 s, four Lean
   invocations). `scripts/check-lean-gate.sh` already owns both. Every push in
   the repository pays for them twice, on a step documented at 206-248 s and
   measured at 2,396 s under contention. First, because it taxes every other
   lane continuously.
2. **One guard in `check-lra-hypothesis-binding.py:1244` measurably SURVIVES**
   (`bind_structural`'s opaque-sort check). Needs a control in
   `102-attestation-gap`'s test module; the mutation harness reports it rather
   than the harness having been wrong.
Items 3-4 (the 404 GB target-dir relocation, scheduled because it forces one
cold rebuild; and registering a heavy-cargo suite with the mutation harness)
are in [the lane note](../notes/99-capability-assurance.md).

Cleared by their owners since this list was written: `103-creal-lean-divergence.md`
is under the ceiling (2,958 B), and `PLAN.md` now records the 11 -> 10 ledger
guard-count correction rather than publishing the wrong number.

<!-- plan-section: landed-changes -->

| 2026-08-20 | `e44f9d715` | **QF_NIA `unsat` now carries a refutation, band 2 -> band 1.** The proof-gap matrix loses 60 of 327 instances at "evidence marked certified" — four times what Lean reconstruction costs — and `QF_NIA` ranked *band 2, needs an UNSAT proof format first*. But `nia_square` was already deciding this fragment EXACTLY; the artifact existed and nothing emitted it. Three arguments certified (non-square discriminant, non-integral rational roots, rational-root exhaustion at degree >= 3). **The checker does not call the producer**: the in-tree `fresh == *cert` convention re-runs the matcher, which binds a certificate to its source but cannot discover that the producer's reasoning is wrong — both would be wrong together. Stage 2 re-derives from the coefficients alone, scanning `1..=|a0|` where the producer pairs cofactors to `sqrt|a0|`, so a completeness bug in the step that could turn a `sat` into a wrong `unsat` is not repeated. |
| 2026-08-20 | `119a91c53` | Mutation testing the above, and the first run is the part worth keeping: nine guards, **five killed one test each and four killed nothing** — another guard rejected the same forgery first, the "six of seven were removable while green" shape. Isolating them needed certificates the producer would never emit: a degree-2 argument over `x^3+x^2+x-3 = 0`, which is SATISFIABLE at x=1 and whose leading three coefficients give a genuine non-square 13 with a valid bracket, so every other guard passes and only the degree check prevents certifying a satisfiable query; a constant term of right magnitude and wrong sign, leaving divisor set and recomputed count identical; and two cubics with IDENTICAL reason data so only the coefficient binding separates them. All nine now die individually. Two of my own harness bugs found on the way, both silent — a positional filter that matched no integration test name, and classifying cargo's `error: test failed` as `DID NOT BUILD`, which reported five real kills as compile failures. |

| 2026-08-19 | `417b9216b` | **Finished the `AxReal` rename at the place that publishes the name.** ADR-0522 renamed the axiomatized ordered field's declarations; the ledger kept filing them under prelude `real`, so the table a referee reads said `real 30` about 30 rows all named `AxReal.…` — the label contradicting its contents, and inviting the exact reading the rename existed to prevent (the reals this project ships are `creal`, in the same table at **0**). Landed atomically per that ADR's own warning: `total=30|axreal=30|…`, thirty before and thirty after, never thirty-one. The table now carries a generated paragraph saying what `axreal` is and that ADR-0509's *declared* is not *reached*; it previously assumed the reader knew. Generalises: **a rename is not landed until the thing that publishes the name has moved** — the declaration half is the half a compiler checks, and therefore the half that gets done. |
| 2026-08-19 | `417b9216b` | Two substring bugs of the shape CLAUDE.md warns about, found by the rename and caught by neither gate. `real (\d+), integer (\d+), string (\d+)` matches inside **`creal 0, integer 0, string 0`** — ordinary prose now that the constructed carrier is the one at zero — captured (0,0,0), scored it against `axreal` (30) and reported a stale count, so a document stating the counts CORRECTLY would have redded the gate. And `check-fact-depends-derived.py`'s namespace list contains `Real`, matching at offset 2 of `AxReal.add_comm` to yield a name no kernel declares: `unnamed` never fires because a name WAS found, the lookup misses, and the fact is skipped **in silence** — the very silent-skip that file's header promises to report. Both fixed with `(?<![A-Za-z])`; the first controlled both ways (remove the lookbehind → 1 test dies; make the pattern inert → 5 do). |
| 2026-08-19 | `17df9ba63` | **A control script that nothing invokes, found by a control script.** `scripts/tests/` held 8 controls and `test-check-lean-golden-pins.sh` was run by nothing — not `check.sh`, not the justfile, not the hook, not CI — while passing 6 assertions daily. Fifth instance of this shape here. `check-control-registration.sh` now derives the registry from the filesystem, so a new control is red until a gate names it. Also `lane-push.sh --to <branch>`: landing work is `push HEAD:main`, and without a target the range, the cost estimate and the fast-forward check all read `origin/<current-branch>` — measured on a fixture, the same doc-only landing reads FULL BATTERY instead of FREE. |
| 2026-08-19 | `ad7f99e72` | Two `real-inverse` facts were red because of a lemma about `max`: both pinned `76 declarations admitted` and the lattice work made it 94. **A total every lane increments is not an anchor for a fact about one declaration** — replaced by the invariant the facts are about (trusted surface = 0) plus an explicit `>= 76` floor, demonstrated able to fail. They were also unreplayable: ~19 min in debug against the replay gate's 120 s budget, so it recorded TIMEOUT rather than a result. `--release` is ~12x here. |

| 2026-08-18 | `pending` | `scripts/cargo-serialized.sh`: heavy cargo now takes an flock and a memory ceiling, because "serialize" was prose and prose does not hold a lock (two dev boxes downed, one agent session OOM-killed). **`MemoryMax` alone does not bite** — it *is* applied (`memory.max` = 67108864) and a 400 MB allocation still succeeds by swapping, on a box whose 7 G of swap is 6 G full. With `MemorySwapMax=0` the same allocation is SIGKILLed by the cgroup (137), host untouched. `--self-check` proves it per host and discriminates: `AXEYUM_CARGO_SWAP=1G` flips it to `SURVIVED`, exit 1. |
| 2026-08-18 | `pending` | `local-ci.sh`, the declared authoritative gate for `main`, cannot run on any fleet host and never has (`cargo nextest` 101, `rustup run 1.88.0` 1, on s4/s5/s7). Now refuses to start rather than limp, `--record` leaves a tracked per-(sha,host) JSON, and `provision-fleet-host.sh` installs the prerequisites (`1.88.0` needs `--profile minimal`, else rustup fails on `miri`/`cranelift` inherited from the nightly profile). The record carries per-step TEST COUNTS and marks a step that exited 0 having run zero tests as `vacuous`. |
