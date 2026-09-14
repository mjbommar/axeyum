# Lane: qf-wall — the eleven are four causes, and the largest is one refused atom

<!-- plan-section: lane-status -->

**Closed** (qf-wall, 2026-09-14). [ADR-2040] and [ADR-2035] converged on "a
small set of quantifier-free queries that cvc5 **and** z3 both refute and we
cannot" — 11 `CAPABILITY-LIMIT` rows. This lane answers what each one needs.
[ADR-2050].

**They re-derive exactly** — 11 `CAPABILITY-LIMIT` / 2 `DECIDED` on the current
tree, row for row, unlike [ADR-2035]'s 8-of-22. **And they are FOUR causes, not
eleven and not one.** Six rows, all `AUFLIRA`, are **one refused atom**:
`lira-dpll` declines the whole query when `lra.rs::linearize` meets a subterm it
cannot linearize — a `select`, or an application of `log`/`divide`, which in
`AUFLIRA` are *declared* functions and so just opaque Real terms. **2 to 4 atoms
per file** discard a 14-conjunct query whose refutation is propositional. The
integer mirror already ships (`IntCollector::allow_opaque_apps`, "sound for
UNSAT transfer"); the Real collector is keyed by `SymbolId` and structurally
cannot hold a term. Simulated outside the solver: **6 of 6 flip `unknown` →
`unsat`, 6/6 STABLE-GAIN over 3 passes per arm**, z3 and cvc5 confirming at 6/6
each, with a non-vacuous negative control. Two more rows are **SELECTION** (we
refute a 3-of-268 and a 1-of-633 subset in 24 s and fail on the whole), two are
a **silent watchdog hang** with no route line at 24 s, 120 s and on the minimal
core, and one **is not a ground-checker gap at all** — we refute its
quantifier-free skeleton standalone while [ADR-2040] scored the file
`CAPABILITY-LIMIT`, so the rung is not handing the ground checker the query the
census describes.

Every row's minimal unsat subset is **one conjunct** (one is 3), median 1
against a pre-registered ≤ 5.

**No lever was built** (pre-registered R10), and the reason is in the ADR: the
site is bounded and named, but the change makes a weakened query reachable by
the ladder — new public route surface with sat-side soundness obligations — and
the abstracted query is consumed by `dl-online`, a route EARLIER than the one
that refuses, so "every `Sat` exit" is not yet an enumerated set. The +6 is a
**simulation**, not a measurement of shipped code.

**Two corrections this lane published against itself.** Its first commit called
a row an instrument artefact because `abstract-quantifiers.py
--fresh-per-occurrence` returns `sat` where the census's shared-by-text map
returns `unsat`. That inference is invalid — no-sharing is strictly weaker than
correct sharing, so its `sat` refutes nothing — and a third instrument that
shares only after `let`-expansion says `unsat` at 11 of 11 measurable rows. **The
control the tool documents for itself cannot decide its own question**, which is
the transferable finding. Second, the instrument's own `set-logic ALL` rewrite
made cvc5 reject 3 of 4 rows at parse; the authority column was measuring the
rewrite.

Also: the two reach levers [ADR-2040] ships `Off` are load-bearing for 3 of 13
rows, refused at INGEST without them.

**An OOM took the dev box.** A `let`-expander with no ceiling reached 63.4 GB on
a 724 KB file with 107 nested `let` bindings; `cargo-serialized.sh` bounds cargo
and nothing bounds a lane's own Python. Recorded in
[`measurement-hazards.md`](../../contributor-guide/measurement-hazards.md) and
in `CLAUDE.md`'s trigger index.

Open, and handed over rather than closed: cause (C)'s hanging route is not
identified (a 444 KB single-conjunct reproducer now exists), cause (D)'s rung
granularity is not diagnosed, and two rows have no abstraction of any kind
because `let`-expansion does not terminate in bounded memory on them.

[ADR-2020]: ../../research/09-decisions/adr-2020-the-ground-checker-mostly-refuses-and-the-set-it-refuses-is-one-we-had-no-need-to-build.md
[ADR-2035]: ../../research/09-decisions/adr-2035-two-populations-reach-one-boundary-and-a-round-cap-can-convert-neither.md
[ADR-2040]: ../../research/09-decisions/adr-2040-the-reach-half-is-worth-two-and-the-whole-remaining-shape-is-the-ground-checker.md
[ADR-2050]: ../../research/09-decisions/adr-2050-the-eleven-are-four-causes-and-the-largest-is-one-refused-atom.md

<!-- plan-section: landed-changes -->

| 2026-09-14 | `2af00d4b2` | `bench-results/qf-wall-20260914/`: the instruments and the preregistration. The preregistration states plainly that the diagnostic phase preceded it and that its rules govern the BUILD decision only. |
| 2026-09-14 | `12589b48d` | Correction of this lane's own first finding: the census's 13 STANDS. `scopeskel.py` — share atoms only after `let`-expansion, which is sound and still shares — says 11 ADMISSIBLE / 0 NOT-ADMISSIBLE / 2 DID-NOT-RUN. Plus the route trails, the current-tree re-derivation, the minimal-core table, the opaque-atom lever simulation and its non-vacuous negative control. Carries the OOM disclosure. |
