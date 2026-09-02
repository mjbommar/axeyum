# Lane: retrieval-audit-0902 — daily retrieval audit for 2026-09-02

<!-- plan-section: lane-status -->

**`DONE`, retrieval-audit-0902, 2026-09-02.** Second daily retrieval-audit
lane (ADR-0608's structural remedy). Window: **81 commits on local `main`
dated 2026-09-02, 28 touching `crates/axeyum-lean-kernel`**, from fourteen
`Agent:` trailers (the eight named lanes plus four gate lanes). **7
candidates (after excluding `retrieval-audit-0901`'s own 4 commits, which
carry today's committer date because that lane ran today), 0 confirmed, 0
literal duplicates.** First clean day in the ledger.

`scripts/check-shape-duplicates.py --prebuilt` against a freshly built
`shape_search` (no prebuilt binary existed in this worktree; rebuilt via
`scripts/cargo-serialized.sh`, 1 m 17 s): **15 groups, all allowlisted,
unchanged from yesterday's post-dedupe baseline.** `kernel_declaration_projection`:
**15,269** rows (up from 14,665; +604 across the day's eleven lanes, none a
duplicate group). Every one of today's 7 candidates read as correct
retrieval, not a miss: two absence checks run and passed before building
(`68f452c23`, and `4b4e90490`'s explicit Int-twin check), one promotion of a
private carrier-typed helper into a bare-`NameId` theorem (`dedab9764`,
consumed by the very next commit `fa87f0320`), and one avoided rebuild of a
pigeonhole search by finding it filed under the least-number principle
(`94373af8a`: `Nat.lnp_bounded_search`). Details, near-misses and the
Int/Nat/Rat twin check (deliverable-specific) in
[2026-09-03-retrieval-audit-for-2026-09-02.md](../research/11-design-review/2026-09-03-retrieval-audit-for-2026-09-02.md);
ledger row appended to the foot of
[2026-08-27-retrieval-is-the-bottleneck.md](../research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md)
(running total unchanged at 21 audited instances / 4 real duplicates, since
today added 0).

**Structural finding, not a lemma finding**: `63f887b89` (lane
`shape-dupes-at-merge`, same day) gave the L0 duplicate gate a no-cargo
`--prebuilt` route and wired it into `check-merge-hygiene.sh` point 7,
defaulting ON — a direct same-day fix for yesterday's 25-hour red-gate
finding. This lane's own `--prebuilt` run exercised exactly that route.

Tool usage: `shape_search` in 0 of 81 (0/28 kernel-path) commit messages;
in 7 of 14 (50.0%) status docs touched today, or 5 of 12 (41.7%) excluding
the two docs that are themselves ABOUT the retrieval tooling
(`retrieval-audit-0901.md`, `shape-dupes-at-merge.md`). `brief-step0`/`just
brief` in 3 of 14 (21.4%), or 1 of 12 (8.3%) on the same exclusion. Both
above yesterday's 7.4%/0% and above the all-time reference (7.0%/2.3%) — one
day, not yet a trend.

Verification, all in this worktree: `nat_prelude::` 365 passed / 0 failed;
`rat_prelude::` 169 passed / 0 failed (179.48 s); `cargo clippy -p
axeyum-lean-kernel --all-targets --all-features -- -D warnings` clean;
`python3 scripts/validate-facts.py` exit 0 (2,606 checked, 0 errors). No
declaration was deleted, so `prelude_fields.rs` was not regenerated.

Next for tomorrow's lane: check the L0 gate's colour in
`check-merge-hygiene.sh`'s own output before anything else — it may already
answer the question this audit exists to ask. State the previous audit
lane's own commit SHAs explicitly as excluded from the candidate set, rather
than leaving the next lane to discover the overlap from `Agent:` trailers.

<!-- plan-section: landed-changes -->

| 2026-09-02 | retrieval-audit-0902 | lane start: status stub, method inherited from retrieval-audit-0901 |
| 2026-09-02 | `a2ab992a8` | daily retrieval audit for 2026-09-02: 7 candidates, 0 confirmed, 0 literal duplicates — first clean day; L0 gate green (15 groups); ledger row appended; write-up at `docs/research/11-design-review/2026-09-03-retrieval-audit-for-2026-09-02.md` |
