# Lane: ax-warm — why the retained IncrementalBvSolver slowed with session age (Glaurung six-cell 2026-09-17), and the repair

<!-- plan-section: lane-status -->

**AX-WARM (`landed`, ax-warm, 2026-09-17).** Glaurung's six-cell rerun found
the warm session's per-check p90 growing 0.1 → 178 ms with session age.
`examples/warm_session_age.rs` replays one real DptfDevGen owner session
verbatim (1,206 checks, 0 verdict disagreements, every `sat` replayed) and
reproduced 0.24 → 269 ms p90; `git bisect` (5,804 commits, 13 steps) landed
on `f019d503f` (ADR-1703: native core becomes the warm engine); the hot frame
was `proof_sat.rs::snapshot_target_phase` re-walking the whole trail at every
decision of a conflict-free descent (O(decisions × retained trail)). Fixed
with stable-prefix marks per phase vector — byte-identical vectors, identical
verdict+model digest, identical conflict counts — the replayed session's last
band is 306 → 7.5 ms p90 back to back (total 34.9 → 1.66 s); the July BatSat
engine measures 3.7 ms / 0.87 s on the same stream. A counter test pins the
linear bound and dies alone on the revert. ADR-2142. **Next:** a Glaurung
re-pin and campaign rerun (not run here); and the remaining linear-in-database
term — the warm core re-derives the whole assignment every solve by design
where z3's `sat::solver::pop` keeps surviving scopes — which changes
trajectories and so needs the pinned-list A/B.

<!-- plan-section: landed-changes -->

| 2026-09-17 | ax-warm | `warm_session_age` reproducer (verbatim trace replay + synthetic explorer walk, verdict+model digest), the `snapshot_target_phase` stable-prefix fix in `axeyum-cnf`, `phase_snapshot_entries` counter and its linear-bound test, `retained_learned_clause_count`/`retained_sat_conflicts` gauges, ADR-2142. |
