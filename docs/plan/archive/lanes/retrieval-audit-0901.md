# Lane: retrieval-audit-0901 — daily retrieval audit for 2026-09-01

<!-- plan-section: lane-status -->

**`DONE`, retrieval-audit-0901, 2026-09-02.** First daily retrieval-audit lane
(ADR-0608's structural remedy: one lane per day audits the previous day's
commits for rederived lemmas). Window 2026-09-01, **240 commits on `main`, 69
touching `crates/axeyum-lean-kernel`** — not the ~465 the brief cited, which is
not reproducible from any ref here. **17 candidates, 4 confirmed, 1 a literal
duplicate, deduped in `b4fb008d8`.**

`Nat.prime_coprime_factorial_of_lt` (`prime_dvd_factorial_lcm.rs`, 2026-09-01
04:25) and `Nat.coprime_factorial_of_lt_prime` (`gauss_lemma.rs`, 2026-08-31
11:56) render byte-identically in `kernel_declaration_projection` and prove the
same statement by the same induction — landed **16 h 29 min apart**. The later
is deleted, its one consumer repointed, and
`F:ml430-nat-prime-coprime-factorial-of-lt-2dbea201` (train partition, not
held-out) repointed under a pin amendment with both digests unchanged.
Projection 14,673 → 14,665: 8 rows removed, 0 added, 8 changed in the
dependency columns only, rendered type and axiom footprint unchanged on every
one. The corroboration arrived on its own —
`check-fact-depends-derived.py` found that the Int mirror's proof term already
used the survivor.

The **L0 duplicate gate `check-shape-duplicates.py` had been red on `main` for
about 25 hours** and no lane ran it; it exits 0 again at `b4fb008d8`. The other
three confirmed instances are all hiding place 2 (inline / private / not
visible) and none is deletable — `dvd_elim` has **13** private per-file copies
in this crate, `absurd` 12, `dvd_intro` 10. That is where the remaining problem
lives, and no index over `kernel.environment()` can see any of it.

Tool usage on the day: `shape_search` in 2 of 27 lane status docs (7.4%),
`brief-step0` in **0**. Write-up:
`docs/research/11-design-review/2026-09-02-retrieval-audit-for-2026-09-01.md`;
the running ledger is now at the foot of
`docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`
(21 audited instances, 4 landed as real duplicates).

Next for tomorrow's lane: check the duplicate gate's colour first, run the tool
before reading commit messages, and scope the phrase sweep to the kernel path.

<!-- plan-section: landed-changes -->

| 2026-09-02 | `b4fb008d8` | `dedupe(nat)`: deleted `Nat.prime_coprime_factorial_of_lt`, a second proof of `gauss_lemma`'s `Nat.coprime_factorial_of_lt_prime`; consumer and fact repointed, pin amended, projection 14,673 → 14,665. |
| 2026-09-02 | `a766acdce` | `docs`: the 2026-09-01 retrieval audit, and the running daily-audit ledger appended to the ADR-0608 write-up. |
