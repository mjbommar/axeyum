# 06 -- Roadmap: research -> implement -> test -> iterate

Sizing: S (<1 day-lane), M (1-3), L (3+). Every phase ends at a gate; a
phase without a passing gate is not done, per Working Stance.

## P0 -- Foundations pilot (M overall; detail in 04)

Doc-IR + assembly + three emitters, exercised by `noh_wt_certificate`
(system genre) and the gf2 fact mini-atlas (result genre).
GATE: the eight P0 exit criteria in 04, including all four fail-closed
negative tests and the byte-determinism check.
RESEARCH ITEMS inside P0 (timeboxed, written up in this folder):
- R-a: layout algorithm for small DAGs in pure Rust (Sugiyama-lite);
  survey petgraph + hand-rolled layering; exit = the atlas graph renders
  legibly for the 18-fact corpus. [S]
- R-b: math typesetting in HTML without external requests: server-side
  render (LaTeX -> MathML via Rust latex2mathml or Python) vs Unicode
  best-effort. Exit = a decision note here; MathML-first is the default
  hypothesis (all modern engines render MathML; zero JS). [S]

## P1 -- Producer breadth + the atlas proper (M)

- `--emit-run`/`--emit-docir` hooks on: 3 more CAS reports (a gf2 Hayes
  report, one acb example, one bench JSON adapter); the fact-ledger
  reader promoted to cover ALL facts; kernel theorem pages via the
  inventory examples (statement from NameId, axiom-footprint badge).
- Dependency-graph atlas over the full ledger; GitHub Pages publishing
  (static output committed or CI-built -- no server).
- ADR #1 lands here: promote `render/` to workspace crate
  `axeyum-render`; Doc-IR schema + run-record format become public
  surface with semantics/replay/checker documented (Hard Rules).
GATE: atlas builds from the real ledger in `just check` extension;
validate-docir.py green on every emitted document; one new producer
added by someone OTHER than the render lane using only the docs
(the boundary-proven-by-use test).

## P2 -- Solver evidence + WASM showcase (M/L)

- Certificate pages for solver artifacts: sat (model + replay verdict),
  unsat (DRAT stats + check_drat certificate box). The SMT/SAT rendering
  gap from 02 is ours here.
- WASM re-verify button per 05 (checker compiled to wasm32, embedded);
  ship the deliberately-broken control page in tests.
- Rewrite-trace Steps producer (axeyum-rewrite hook) -> first real
  calculational-proof rendering.
GATE: a stranger-facing demo page: one sat, one unsat, one rewrite
trace, each re-verifiable in-browser; self-containment lint green;
the broken control page correctly shows failure.

## P3 -- The paper genre + NoH retrofit (M)

- `axeyum.sty` + generated-fragment flow into a real paper build;
  manifest = paper.yaml extension mapping sections' claim/table/figure
  blocks to run records and ledger refs.
- RETROFIT the NoH-p2 paper as the pilot integration: regenerate its
  section-2 d(k)/kappa tables from the pinned examples; add the missing
  polygon and self-loop figures (Rust SVG -> PDF for LaTeX, same SVG
  interactive in the atlas); the verification appendix auto-built from
  run records; labels (AUDITED-CONFIRMED etc.) become resolver-enforced.
GATE: `make pdf` in the paper repo consumes generated fragments; a
seeded wrong digit in a run record fails the paper build (the paper
inherits fail-closed); diff of retrofitted vs hand-made paper reviewed
and the hand-made tables retired.

## P4 -- Verbosity maturity + ecosystem decisions (S/M)

- Reading-level controls polished across all three formats; per-genre
  default tag maps.
- DECIDE (ADR): MyST-flavored markdown emission (interop only; their
  Node toolchain stays out of OUR build) -- adopt, or close as
  unnecessary given own HTML quality.
- Atlas search (build-time static index, no server) if wanted.
GATE: owner reads one artifact at all three verbosity levels in all
three formats and signs off; ADR recorded either way.

## Iteration loop (standing, all phases)

Each phase: (1) build against REAL artifacts only -- no synthetic demo
content ever gets committed as an example, because pretty renderings of
fake evidence are exactly the failure mode; (2) reader test with the
owner; (3) mutation pass on any new guard (exactly-one-test-dies);
(4) update this folder's docs -- they are the strand's plan of record;
(5) status in `docs/plan/status/<lane>.md` per Session Protocol when
this strand gets a lane.

## Risks and mitigations

- **IR ossifies early**: schema_version from day 0; P0 deliberately
  minimal block set; additive evolution only until the P1 ADR.
- **Renderer becomes a trusted liar**: the emitter-total/assembly-judges
  split (03) keeps trusted logic small; negative tests are gate-level.
- **LaTeX generation drifts from paper templates**: generated fragments
  only (never whole documents); the template owns style, we own truth.
- **HTML scope creep toward an app**: the anti-goals list in 05 is
  normative; self-containment lint is a hard gate.
- **Cross-lane contention**: this strand adds new files/dirs only until
  the P1 ADR; producer hooks in existing crates are additive flags.
