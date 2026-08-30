# Lane: flywheel-mathematics — the blockers were found by proving, not by planning

<!-- plan-section: lane-status -->

**A day of parallel mathematical development against the kernel, 3–5 lanes
throughout** (`DONE`, flywheel-mathematics, 2026-08-25). Production moved
**1,096 → 1,175 distinct theorems, all axiom-free, 0 axiom-bearing**; the
trusted base did not move (30, all `axreal`, none reached by any shipped route).
Kernel `--lib` sweep 656 → 695 green. Full write-up:
[`../../mathematics-2026-08/diary-flywheel-2026-08-25.md`](../../mathematics-2026-08/diary-flywheel-2026-08-25.md).

The theorems are the smaller half of the output. **Three structural findings
came from lanes failing to prove things and reporting why**, and none of them
was visible from any plan:

Detail moved to [`../notes/125-flywheel-mathematics.md`](../notes/125-flywheel-mathematics.md).

<!-- plan-section: landed-changes -->

| 2026-08-25 | `0f2fb5fcd` | A doc line beginning with `+` is a Markdown list bullet, so ten `doc_list_item` errors pointed at ordinary prose one line below the cause. |
| 2026-08-25 | `6de1d88f8` | Salvage: **the irrationality of √2** (`Nat.no_rational_sqrt_two`) and **`CReal.geom_tail_within`**, committed on behalf of two lanes killed mid-run by a spend limit. Both verified here: 695 tests, clippy `--all-targets`, axiom-free. |
| 2026-08-25 | `03385d2f7` | **`CReal.monotone_of_nonneg_deriv`** — global from local, constructively, no MVT. Four lanes. The congruence is needed at BOTH endpoints, not just the one the handoff named. |
| 2026-08-25 | `dd1ba4808` | `clippy --all-targets` was red on `main` in a doc comment I wrote; four lanes each reported it and each routed around it to the narrower `--lib --tests`. |
| 2026-08-25 | `9703044b7` | `perfect.rs` shipped unformatted behind a green clippy and a green 679-test sweep; `hooks/pre-push`'s `cargo fmt --all --check` caught it. `--lib` structurally cannot. |
| 2026-08-25 | `4a21cbde7` | Correction to a correction: `Int.prodRange_permute` is full-range (`MapsInto σ n`), so the predicate-scoped primitive genuinely does not exist over any carrier. Production regen 1125 → 1141. |
| 2026-08-25 | `af8340e16` | Held-out contamination and the seven-lane fold finding, recorded. |
| 2026-08-25 | `8aa57e4e8` | The `CReal.sqrt` route: `KRegular` at `c = 3` **uniformly in `x`**, so `sqrt` is total and needs no `PosBound` — which a constructive setting could not have supplied, since `0 ≤ x` is undecidable. |
