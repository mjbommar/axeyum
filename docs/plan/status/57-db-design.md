# Lane: db-design — relational schema design as a certificate-carrying decision problem

<!-- plan-section: lane-status -->

**Database design now has a foothold, and it is the sharpest demonstration in
the tree of this project's own sentence (`WIP`, db-design, 2026-08-15).** The
owner asked for the stack to be pointed at "planning, logistics, database
design, or general numerical approximation"; planning and logistics had the
`infeasibility` lane and database design had nothing. It fits on the merits:
every central question of relational schema design is a *decidable logical
implication problem whose certificate is far smaller than its decision
procedure*. Conjunctive-query containment is the extreme case — finding the
homomorphism is NP-complete, and the certificate for `Q_terse ⊆ Q_verbose` is
four variable-to-element pairs.

Landed: `crates/axeyum-scenarios/src/dbdesign/` (no new crate — ADR-0001, and
ADR-0008's charter is exactly this), deciding FD implication, candidate keys,
BCNF/3NF, lossless join, dependency preservation and CQ containment; two driver
examples in `axeyum-bench`; three committed instances with 28 pinned
expectations; 13 negative controls; and four facts closed by
`scripts/close-fact.py`, which executes every checker. 37 unit tests, one
"tampered certificate is rejected" per family. ADR-0463.

Three things are worth carrying forward from this lane rather than the domain:

1. **The solver's model IS the certificate.** A dependency set is a Horn theory,
   and *any* model of `Horn(F) ∪ X ∪ {¬y}` — not just the least one — is the
   agreement set of a two-row counterexample relation. So `sat` produces the
   object rather than an opinion, and the object goes through `check_model` and
   then through a checker that evaluates all of `F` row by row with no closure
   anywhere.
2. **The negative direction rests on LESS than the positive one**, the reverse
   of the usual asymmetry here. Lossy needs no theorem; lossless needs the
   soundness of the chase. Not-contained never invokes Chandra–Merlin's converse
   (which needs an *infinite* domain). Not-implied does not need the
   completeness half of Armstrong's theorem. Each fact's `axiom_footprint` says
   which half it leans on.
3. **A checker that exits 0 on completion is not evidence.**
   `scripts/check-dbdesign-negative-controls.sh` (22 assertions, 2.1 s warm) is
   an evidence row on all four facts: 13 instances each pinning exactly one
   FALSE answer must all exit non-zero, plus a wrong `--expect-checks` count, an
   instance fed to the wrong checker, a `--verify-formal` script whose negation
   is satisfiable, one that asserts nothing, an instance pinning nothing at all
   — and three assertions that the TRUE instances still pass, without which a
   checker that rejected everything would sail through.

Next, in priority order: (1) **3NF synthesis** — the lane decides 3NF and checks
a given decomposition but does not construct one, and the attribution to get
right is split (Bernstein 1976 gives dependency preservation; the lossless
guarantee is Biskup–Dayal–Bernstein 1979); (2) **an Armstrong derivation
reconstructed into the Lean kernel** — the derivation is already a three-rule
proof object, which is a much shorter path to `kernel-lean` than the 5.1 MB
Farkas term the `infeasibility` lane hit; (3) **unary inclusion dependencies
with FDs**, the decidable fragment (Cosmadakis–Kanellakis–Vardi 1990) — full
FD+IND implication is *undecidable* (Chandra–Vardi 1985 **and**, independently,
Mitchell 1983) and must never be answered silently; (4) **MVDs and 4NF**, one
`Symbol` variant away in the tableau, though a chase with EGDs can fail rather
than terminate so the certificate story needs re-deriving; (5) **scale** — the
candidate-key sweep is `2^n` and refuses above arity 24, which is fine for a
schema and useless for a warehouse.

Full reasoning, including the traps and one design regret (the instance format
is a fifth parser in this tree):
[`docs/mathematics-2026-08/diary-db-design.md`](../../mathematics-2026-08/diary-db-design.md).

<!-- plan-section: landed-changes -->

| 2026-08-15 | `996d10826` | Four database-design facts closed by executing their checkers: FD implication with Armstrong derivations and solver-model counterexample relations (its `formal.statement` machine-checked by `--verify-formal`), candidate keys settled by a 1024-subset sweep with 384 checked counterexamples and absolute minimality per ADR-0455, lossless-join chase traces with spurious-tuple witnesses, and six CQ containments agreeing across three independent routes. |
| 2026-08-15 | `75327842c` | ADR-0463: database design enters the stack as certificates, not verdicts. Records that the negative direction rests on less than the positive one, that "domains have at least two values" is a real assumption, and that inclusion dependencies are excluded because FD+IND implication is undecidable. |
| 2026-08-15 | `b23b0be3f` | Relational schema design decided twice and reported only with a replayable certificate: `axeyum-scenarios/src/dbdesign/` (Armstrong derivations, two-row counterexample relations, the tableau chase, spurious-tuple witnesses, Chandra–Merlin homomorphisms), two `axeyum-bench` certifier examples, three instances that pin their own answers, and a 22-assertion negative-control gate that measures the checkers failing closed. |
