# STATUS changelog — 2026-07-03 (archived)

> Archived from STATUS.md on 2026-07-07 to keep the live changelog lean.
> Newer entries live in STATUS.md; entries through 2026-07-02 are in
> [changelog-through-2026-07-02.md](changelog-through-2026-07-02.md).

- **2026-07-03 (evening) — the keystone is banked (ADR-0055), its
  verification debt paid, and the code↔LIA bridge moves strings again:
  QF_S 61, totals 680.**
  - (`5707563b`) **Default-on verification debt paid** (the 5th review's §3):
    CdclT termination under adversarially non-monotone theories proven by a
    20,000-run MockTheory property + a 16M-step budget belt (no livelock
    found — the trigger-literal invariant forces strict backjump progress);
    the congruence checker's substitution expansion was a REAL defect
    (doubling chains stack-overflow at k≥14, reachable per-assert) — now
    size-budgeted (`MAX_EXPANSION_COMPONENTS=4096`, declines in ~100µs);
    closed-universal polarity pinned safe (a ∀ under or/not/ite never
    reaches the lever) + 400 nested-polarity differential cases DISAGREE=0.
  - (`dd732e2b`) **ADR-0055 accepted**: the QF_S online CDCL(T) route is
    default-on (ratifying the landed second-chance ordering that moved the
    scoreboard); QF_UF online stays an opt-in parity twin with recorded
    default-on criteria; new theories arrive online-first.
  - (`122c3c27`) **The code↔LIA bridge** (5th review's #2 lever): `str.to_code`
    twins a fresh Int with the universally-true domain fact (`len=1 ∧
    0≤c≤0x2FFFF` ∨ `len≠1 ∧ c=-1`) + single-char code↔equality links; the
    ADR-0052 abstraction now also upgrades `unknown` verdicts (a sound
    relaxation refuting is unsat regardless of what produced the unknown —
    the three str-code census files were actually blocked on the 32-bit
    bit-blast, not the gate). Faithfulness: the Unicode cap 0x2FFFF, not the
    byte model's 255 — fixing a latent wrong-unsat risk (regression-guarded).
    **QF_S 58→61, QF_SLIA 12→13, totals 676→680 decided, 627
    oracle-compared, DISAGREE=0**; lex-order (`str.<=` over variables) and
    seq.update honestly declined. String day total: **QF_S 52→61 (+9)**.
  - (`c5f181b9`) **T-C.5 REGEX MEMBERSHIP LANDED (ADR-0054)** — the largest
    census demand (15 files) attacked: full SMT-LIB RegLan → code-point
    derivative-engine translation; single-variable DFS witness search with
    MANDATORY independent-matcher replay (sat); **re-checked
    derivative-emptiness certificates** (unsat — complete nullable-free
    closure, independently re-verified); front-door + bench routing.
    **QF_S 61→67 (50%, PAR-2 4.372→2.928), QF_SLIA 13→14; totals 687
    decided / 632 oracle-compared / DISAGREE=0.** Fuzzes vs BOTH oracles:
    z3 627 jointly decided, cvc5 175, plus a 2000-case brute-force
    differential — all zero disagreements. Census remainder honestly
    unknown: membership+extended-fn coupling (Phase D), disjunctive
    membership Boolean shapes (next: membership atoms in the online CDCL(T)
    route), re.all+prefixof. **String day total: QF_S 52→67 (+15, 39%→50%),
    with every verdict oracle-verified and DISAGREE=0 held throughout.**
  - (`f5b00c72`) **P0 incident, resolved same evening — a vacuous-sat HARNESS
    hole, engine exonerated.** CI's corpus_regression reported 1 DISAGREE at
    `c5f181b9` (instance1079-re-loop-cong: declared+z3 unsat, reported sat).
    Direct probes cleared the engine, matcher, translation, and front door
    (all correct on the shape; `solve_smtlib` decides the file unsat). Root
    cause: T-C.5 made membership scripts word-only-fallback eligible (EMPTY
    flat assertion view), and corpus_regression handed that empty view to
    `check_auto` — the vacuous empty conjunction. The same class was fixed
    for the bench in `f5d3e1ec`; this harness was never taught. Fixed:
    empty-flat-view scripts decide via the front door (118 agree, 0
    DISAGREE). **Lessons queued (task #29): audit the other 11 parse_script
    consumers + a structural guard; the pre-push hook must gate the pushed
    SHA, not the working tree (it blocked this validated fix over unrelated
    WIP); corpus_regression joins the standard string-slice gate list.** A
    second suspected wrong-sat (fuzz seed 215) was confined to an
    UNCOMMITTED feature WIP — quarantined on `wip/t-c5-membership-atoms`
    with a do-not-merge note; verified absent at HEAD.
  - Also: the pre-push compile gate is live (`hooks/pre-push`,
    `core.hooksPath`), the cap audit found only two CI-scaled sites (both
    healthy), ADR-0051/0053 flipped to accepted, and the tracker count-rot
    was replaced with scoreboard references (5th review applied, `1cb7155f`).
- **2026-07-03 (afternoon) — the P1.5 keystone opens, UF×NRA lands, Phase C
  engine core lands, and the 4th review is applied.**
  - (`a3460101`) **P1.5 slice (a): the generic online CDCL(T) driver** —
    `CdclT<T: TheorySolver>` with 1-UIP learning over the MIXED implication
    graph (Boolean + theory reason clauses from e-graph `explain` cores),
    lockstep theory push/pop, deadline in the search loop. EufTheory wired
    first, opt-in entry (`check_qf_uf_online_cdclt`), default dispatch
    unchanged. Parity: 2500-instance online-vs-offline house fuzz, 2500
    agree, 0 DISAGREE; the z3-gated QF_UF fuzz (3000) unchanged; no
    TheorySolver trait changes.
  - (`c9d332c1`, `c924fcb0`) **P1.5 slice (b) + front-door wiring: the word
    core runs inside a real CDCL(T) loop.** StringTheory adapter (per-assert
    certified refutation checks; conflict explanations map the checker's
    premise indices to trail literals; sat only via arrangement-search model
    + full replay) — and the fuzz found a REAL CdclT bug (1-UIP path_count
    underflow on non-current-level theory cores; fixed by always including
    the trigger literal — a sound superset). Census str002-class disjunctive
    shapes DECIDE; 1500-case z3 fuzz 549 decided (157 sat/392 unsat)
    DISAGREE=0. Front door + bench wired via the new `word_skeleton` parser
    side channel (Boolean structure over word atoms, all-or-nothing);
    four fuzzes/crosschecks green incl. the cvc5 second oracle. **Honest
    re-measure: three string divisions UNCHANGED** — the 6 reachable census
    unsats need suffix-cancellation/quadratic/length refutation shapes the
    certified refuter deliberately does not close yet (the named next
    lever); the other ~116 declines are regex/length-bridge territory.
  - (`4d039c5a`, `09e40e41`, `5ad952b8`) **Word-unsat hardening COMPLETE
    (all four 4th-review demands):** cvc5 1.3.4 static as a SECOND
    differential oracle (word fuzz 401/401 agree incl. all 305 unsats;
    corpus 90/90; skip-when-absent); the normalize denotation fuzz (24k
    adversarial pairs at the checker's one shared primitive); mutation
    testing (175 mutants — zero dangerous survivors in the accept paths, 21
    killing tests); and Alethe certificates for word-conflict derivations
    (verify-before-record, 7 tamper modes rejected, 600-refutation
    property; the `axeyum_word_clash` custom-rule Carcara hole disclosed
    exactly as `lia_generic`'s).
  - (`881c76f6`) **UF×NRA combination made explicit (P1.6 slice)** — the
    eager-Ackermann→NRA composition existed *accidentally*, four declining
    routes deep; now an intentional, telemetry-recorded route with replay-
    gated sat, threaded deadline, and a documented boundary. NEW 700-case
    `qf_ufnra` differential fuzz DISAGREE=0; both shared-path guards
    (nra/nia fuzzes) DISAGREE=0; issue5836-2 decided; the linear QF_UFLRA
    path provably untouched.
  - (`0acf3535`) **Phase C engine core (T-C.1/2, ADR-0054)** — interval-set
    code-point predicates + transition-regex Brzozowski derivatives with
    native `R{n,m}` (no pre-unrolling: `R{100,200}` closure = 202 states,
    linear) + the independent reference matcher. Trust anchor: the
    fundamental derivative theorem property-tested over 20,000 engine-vs-
    matcher cases, zero disagreements.
  - (`686087cd`, `6b17e70c`, `3c13df63`) **4th periodic review applied +
    the census** — scoreboard counts made rot-proof (links, not copies;
    machine totals 674/992), multi-agent git hygiene promoted from private
    memory to CLAUDE.md + the contributor guide, the CI docs-filter leak
    actually fixed (`scripts/**`/`justfile`), ADR-0054 proposed, and the
    review's sequencing recorded: P1.5 integration outranks Phase-C
    broadening; word-unsat hardening (cvc5 second oracle, mutation testing,
    normalize fuzz, Alethe emitter) queued before any parity language.
- **2026-07-03 — 🟢 FIRST GREEN CI RUN IN 200+ RUNS** (`10e29199`, all 8 jobs).
  Main had been red for 198+ consecutive runs; the repair was an onion peeled
  over two days, each layer only visible after the previous one:
  MSRV 1.88/let-chains, rustdoc intra-doc links, rustfmt drift, cargo-deny
  wildcard paths, ~100 clippy sites plus the final `axeyum-verify`
  `too_many_lines` (red since `70f2dce2`; local scoped clippy never caught
  it — the lesson is the workspace `-D warnings` gate, not scoped runs),
  the evidence-suite exponential DAG walks + budget flakes, the z3-sys
  prebuilt-download 403 (now authenticated via `READ_ONLY_GITHUB_TOKEN`) +
  the missing `/usr/bin/z3`, runner disk exhaustion, hardware-relative
  frontier ratchets + the budget-excused cap, QF_AX `build_model` hash-order
  nondeterminism (a 12% verdict flake → 0/200), route-trace telemetry
  invariants, the uflra fuzz deadline hole, and runner-pool saturation
  (queue-and-complete concurrency + a docs-only CI split + cancelling 11
  doomed runs). The test job runs ~4.5h because the z3 differential fuzzes
  execute at full iteration counts on shared runners — acceptable for now;
  a CI-scaled iteration count is the queued follow-up if it becomes the
  bottleneck.
- **2026-07-03 (early)** — **The nia_unsat frontier regression (40→23) found,
  bisected, and fixed; the uflra fuzz-hang class closed; Phase B started; two
  more CI onion layers.**
  - (`4f27961e`) **nia_unsat frontier regression**: commit `4fe9491f`
    ("certify bounded QF_NIA dominance", 06-25) had put a 10⁶-case
    exhaustive-evaluation probe ahead of the exact int-blast on every
    bounded-int query. UNSAT must walk the whole box, so mid-size boxes ground
    for seconds where the blast decides in tens of ms — the frontier family
    fell **40 → 23** (n=14: 86ms→848ms; whole family 2.2s→46s) and SHIPPED.
    Caught by the frontier ratchet only during a full local sweep, 8 days
    later; git-bisected across 829 commits. Fix: the pre-blast probe caps at
    10⁴ cases (where enumeration genuinely beats blast setup) and the full
    10⁶ budget moves to a post-decline fallback, so boxes the blast cannot
    encode keep their only decider. Frontier restored 40/40 in 2.19s; all 8
    frontier families green; NIA differential fuzz DISAGREE=0 (1500
    instances). **Lesson recorded: the ratchet must become a pre-merge gate —
    a 17-point capability regression should not need post-hoc bisection.**
  - (`3b5bbcf0`) **uflra fuzz-hang class**: the two 600-case UFLRA
    differential fuzzes ran the budget-blind offline reference
    (`check_with_uf_arithmetic`) with no `config.timeout` and hung unbounded
    (a 3.9h binary was observed). Measured first: the *online* path decides
    all 600 in 0.02s — the offline reference was the grinder. Every
    offline-reference test call now carries a per-case budget (expiry →
    `Unknown`, never a wrong verdict), and the latent un-threaded-deadline
    sibling of the UFLIA `3cd6c810` hole in the UFLRA interface-search DFS is
    threaded (checked per DFS node). Suite: unbounded-hang → 44s/21-pass;
    qf_uflra fuzz 1500 instances DISAGREE=0.
  - (`271ecaa2`) budget-excused cap recalibrated 4→12 locally after verifying
    across three commits that the decided/agree counts are byte-identical and
    only wall-clock excusals moved (quiet-box floor is 8/300) — an audit item
    remains: excused-cap loosenings are a place real regressions can hide.
  - (`10e29199`, `424c761c`) two more CI onion layers: the workspace-clippy
    red (`too_many_lines` in `axeyum-verify`, red on every run since
    `70f2dce2` — local scoped clippy never caught it) and the z3-sys prebuilt
    download 403 (anonymous GitHub API rate-limit; now authenticated via
    `READ_ONLY_GITHUB_TOKEN`). Cancelled 11 already-doomed queued runs to
    unclog the runner pool; `424c761c` is the first run carrying the full fix
    stack.
  - (`90592350`, `c5590668`, `bfc32805`) **Strings Phase B started** —
    ADR-0053 + `axeyum-strings` + T-B.1/T-B.2 (see Current focus).

