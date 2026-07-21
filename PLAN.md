# PLAN.md — master index

This is the entry point. The full, end-to-end engineering plan to take axeyum to
**Z3 + Lean parity** lives under [`docs/plan/`](docs/plan/README.md). This file
is the map and the standing rules; **[STATUS.md](STATUS.md)** is the live tracker
(current focus, per-phase state, changelog) and is the only file with mutable
session state.

> The goal is large and deliberately multi-week/multi-month. It is decomposed
> into tracks → phases → tasks, each with concrete reference file paths, sizing,
> and exit criteria, so work can proceed one verifiable increment at a time
> without ever losing the thread. **We do not stop and we do not hand-wave; we
> advance the next task and record it.**

> **Distilled next-10 focus, both lanes (2026-07-19).** Post-refutation reset:
> ADR-0240/0243/0248 closed the concretization-coverage hypothesis -- no
> validated policy difference, no residual coverage gap, symbolic memory not
> admitted. A0 stays as reproducibility infrastructure, not a coverage project.
> The surviving spine is **correctness + deployability + a characterized
> performance regime + reproducibility-for-free**. New levers this cycle: the
> self-owned IOCTL-census stack (Windows + Linux census -> glaurung/ioctlance ->
> axeyum, with 22-CVE ground truth and an LLM-ranked handler worklist) and a
> candidate LLVM-IR Linux frontend. Ranked next actions, balanced across the
> solver lane (STATUS current focus: decide-rate ~73%, reduction-depth
> performance, proofs) and the integration lane (open: broader labeled recall,
> reproducibility, and frontend breadth; the neutral baseline and this exact
> timeout tier are closed):
>
> Critical path (paper evidence):
> 1. [INTEGRATION] Symbolic CVE recall first admitted slice -- ADR-0263--0271
>    preserve the 22-CVE qualification and 4/12 artifact attrition, then accept
>    the only two frontend-eligible vulnerable/fixed pairs at 2/2 paired recall,
>    2/2 fixed-side cleanliness, and byte-identical rerun output. This is bounded
>    selected-pair detection recall, not 22-CVE population recall or precision.
>    Broader labeled evidence remains open when new artifacts/frontends are
>    independently admitted, but it no longer blocks item 2's neutral baseline.
> 2. [BOTH] Fair in-process warm neutral baseline -- the benchmark-only Bitwuzla
>    adapter and six-cell `{z3, axeyum, Bitwuzla} x {cold, warm}` producer are
>    frozen at Glaurung `2961d7c`; ADR-0272 preregisters the four-driver N>=5
>    run, and the v3 analyzer is frozen at Axeyum `5d74283b` with the exact
>    release/linkage registration. ADR-0272 now accepts the exact 20-process
>    result: all six cells decide and agree on all 12,902 checks/pass with zero
>    fallback; Axeyum beats warm Z3 on three drivers and loses on Dptf, while
>    warm Bitwuzla wins all four. The neutral blocker is closed and rules out an
>    Axeyum performance-lead headline; cvc5 remains the external-textual point.
> 3. [INTEGRATION] Timeout-sensitive / harder-driver tier under a deterministic
>    work-bound (not the 250 ms wall); measure the accepted six-cell topology +
>    cold-Z3-authoritative findings at census scale. A1 wiring is complete at
>    Axeyum `72375263` / isolated Glaurung `dc06a37`; ADR-0273 preregisters a
>    zero-row, 14-tier first-20 tcpip calibration with distinct backend units.
>    All 42 processes are validator-clean, but ADR-0273 rejects calibration:
>    Z3 qualifies at rlimit 100,000 and Bitwuzla at 4 polls on their respective
>    tier streams, while Axeyum never reaches 95% in both cells (at 8,192:
>    cold 4,233/4,846, warm 3,280/4,846; all residuals typed resource-limit).
>    No 338-function row is authorized. Because the Z3 authority limit changes
>    the explored check stream, do not combine independently selected tier
>    values. ADR-0274 now preregisters the fixed-Z3-authority correction: hold
>    Z3 at 100,000, require the exact invariant 4,846-check stream, and sweep ten
>    Axeyum/Bitwuzla shadow-limit pairs at N=3 and accepts the invariant-stream
>    triplet Z3 100,000, Axeyum 32,768, Bitwuzla 512. No census row exists;
>    ADR-0275 now preregisters N=3 joint first-20 reproduction and permits an
>    unchanged N=3 338/338 census only if that gate passes. Phase A passes 3/3
>    with all six cells 4,846/4,846 and exact authority/finding reproduction;
>    Phase B executes 3/3 but rejects: only 210/338 functions are analyzed and
>    every row has 102 assertion-cap fallbacks. Byte-identical findings and
>    97,112/97,112 verdict agreement do not rescue dropped work. Close this exact
>    harder-driver protocol negative and advance item 4.
>    Item 2 remains closed; any successor result would be a bounded one-authority
>    census, not labeled recall or cross-authority finding parity.
>
> Solver mission (STATUS central gap):
> 4. [AXEYUM] Cold-path decide-rate + reduction depth (GQ5) -- the measured lever is
>    word-level reduction, not lazy CEGAR (`lazy_ops_total=0`); bit_blast+cnf=84%.
>    The ADR-0259--0261 duplicate-origin mechanism is closed: its selected
>    candidate changed every required construction counter by zero and was
>    removed before timing. Resume with a preregistered leaf-shape/clause-overlap
>    diagnostic that can name a new fixed structural delta, not with another
>    implementation inferred from the same origin counts. ADR-0276 now freezes
>    that zero-row diagnostic: partition parity duplicates into within-leaf,
>    cross-leaf/same-owner, and cross-owner cells with bounded leaf shapes before
>    observing the fixed corpus or authorizing any production change. The
>    artifact-v37 diagnostic is frozen at `b02b6ab4`; its fixed observation
>    passes and puts all 107,000 parity duplicates in one ordinary two-input
>    `within_leaf` cell, with zero cross-leaf/cross-owner overlap. ADR-0277 now
>    tests only a same-positive-direct-root leaf-emission memo. It hits every
>    exact structural delta and a favorable 0.9601 aggregate timing ratio, but
>    fails the preregistered variance and family guards; candidate `9533c508` is
>    removed at `4fc45767`. This fixed duplicate-clause lane stays closed unless
>    a new population independently motivates another mechanism; ADR-0278 has
>    since completed item 5's bounded reviewer cell, so the active queue advances
>    to the structural/deployability items below rather than another inferred
>    clause tweak or an unmeasured proof expansion.
> 5. [BOTH] **Bounded reviewer cell DONE (ADR-0278).** Isolated Glaurung
>    `f01a057` now returns a source-rebound `InfeasiblePathCertificate`; its fixed
>    bundle rechecks internally and under pinned external `drat-trim`, while a
>    satisfiable control is rejected. This closes attachment and downstream
>    consumption only: the retained DRAT is a two-byte empty-clause proof over
>    complementary input units. Broader work now requires a separately
>    preregistered real workload that can measure proof prevalence, nontrivial
>    traces, and second-pass cost. Whole-CFG/SV-COMP witness composition and the
>    full Lean tactic backend P3.7 remain separate evidence-gated lanes.
>
> Conditional structural lever:
> 6. [BOTH] **Direct Glaurung importer DEFERRED; prerequisite selected
>    (ADR-0268/0279).** The measured kernel surface made a general LLVM importer
>    the larger route, so the accepted selected-pair campaign uses Glaurung's
>    existing AArch64 ELF -> LLIR frontend. The LLIR audit finds a reusable
>    `LlirFunction` + `Machine<D: Domain>` center, but not a compiler-IR-neutral
>    contract: temporary/value widths, explicit false successors, ABI/sink
>    policy, and LLVM poison/memory/call semantics remain gaps. Advance Axeyum
>    P5.1/T5.1.2's structured `.ll` parser first. ADR-0280's accepted opening
>    slice now provides a non-panicking function/parameter/block boundary and
>    migrates `param_decls`. ADR-0281 now accepts typed scalar instructions and
>    value+definedness reflection: LLVM poison flags fail visibly instead of
>    being discarded, the semantic witness gates pass, and one proof has moved
>    to the checked path. ADR-0282 now accepts typed PHIs/terminators and exact
>    predecessor/successor validation on real clang/rustc diamonds, without
>    inheriting the legacy executor's unreachable-arm semantics. ADR-0283 now
>    accepts bounded checked acyclic execution with path-conditioned
>    value+definedness joins, selected-edge PHIs, explicit cycle decline, and
>    `unreachable => defined=false`; all total cross-IR fixtures and the
>    unreachable-default proof use the checked path with definedness explicit.
>    ADR-0284 now accepts the scalar syntax reproducibility gate: canonical
>    typed CFG rendering, exact LLVM `\XX` identifier escapes, structural
>    render/reparse fixpoints, and preservation of checked value+definedness.
>    ADR-0286 now accepts the first bounded T5.1.5 memory slice:
>    one initialized non-aliasing byte object, typed `inbounds` byte GEP plus
>    `i8` load/store, explicit pointer/stored-byte definedness, final-memory
>    joins, canonical rendering, compiler fixtures, and replay-checked proofs.
>    It is not general provenance, wide memory,
>    MIR writes, LLIR hardening, or Glaurung lowering. Only
>    after those should LLIR hardening and a same-object binary-vs-IR
>    differential be admitted. ADR-0287 now accepts the immediate T5.1.3
>    prerequisite: exact compiler identity/argv, raw MIR capture, committed
>    source/output/provenance hashes, stable-CI drift detection, pinned-compiler
>    byte replay, and adversarial tamper/regeneration gates before checked MIR
>    writes. Capture adds no semantics;
>    ADR-0288 now accepts that semantic continuation: named selection from
>    the authenticated multi-function module, located non-panicking typed MIR,
>    explicit access panic independent of `assert`, stores, branch memory joins,
>    source replay, migrated bounds proofs, and the same bounded roundtrip
>    specification on MIR and LLVM. Whole-crate build selection and general MIR
>    places remain open. ADR-0289 now accepts the target-build prerequisite:
>    `axeyum-mir-build` explicitly selects a locked Cargo manifest/package/
>    lib-or-bin/function under the registered toolchain, checks before atomic
>    raw retention, and reproduces both 1,438-byte output and deterministic
>    typed/term JSON. The build-backed four-byte contract and source OOB replay
>    pass; precise no-partial-output failures are tested. ADR-0290 now accepts
>    the T5.1.6 standing gate: all 62 source-derived checked LLVM/MIR semantic
>    variants have exact proof/spec plus deterministic fuzz/replay ownership;
>    96 scalar goals, 11,248 exhaustive rows, 11 cross-IR pairs / 110,000 tuples,
>    five refutations, ten checker mutations, and the dedicated local/CI runner
>    pass. ADR-0291 now accepts the smallest automatic reducible-loop bridge
>    (T5.1.4): the real compiler's implicit entry PHI slot is normalized under a
>    strict structural rule; one canonical typed LLVM self-loop preserves scalar
>    value+definedness in a `TransitionSystem`; and the exact `capsum8` fixture
>    reproduces unbounded/bounded safety. Independent formulas, 20,000 concrete
>    recurrence tuples at zero disagreement, poison/UB negatives, precise shape
>    errors, and source-replayed abstract reachability pass in the standing
>    gate. ADR-0292 now accepts the selected continuation: one exact
>    clang-21 single-latch natural loop with deterministic `%6 -> %15` and
>    `%6 -> %11 -> %15` relations, predecessor-selected simultaneous PHIs, and
>    path-conditioned division UB. Independent formulas, 50,000 recurrence
>    tuples at zero disagreement, an eager-UB refutation, unbounded/bounded
>    safety, precise boundary errors, and source replay pass; the standing gate
>    is eight binaries / 81 tests. Existing replay-checked BMC supplies bounded
>    k-unrolling for accepted relations rather than a second textual-CFG engine.
>    ADR-0293 now accepts that measurement: the exact 12-source result
>    reproduces byte-for-byte with 12 loops in 12 functions, 11 matching the
>    existing ADR-0291 structural shape and one early-exit row in
>    `mathlib_is_prime`. The sole rejected profile occurs in only one function
>    and one source, fails the frozen diversity rule, and authorizes no code.
>    Structural matching is not semantic acceptance. T5.1.4 remains WIP: next
>    ADR-0294 preregisters semantic eligibility/rejection measurement over all
>    12 exact functions. It recompiles and
>    hash-matches every source, extracts functions with pinned LLVM, preserves
>    the checked parser/loop error class and diagnostic, and forbids dropped
>    rows; its cross-function/source plurality rule can select only a later
>    audit lane, not code. Its first formal artifact observed 0 accepted / 12
>    typed-CFG `unsupported_instruction` declines, but the immediate rerun
>    rejected all 12 raw extracted-file hashes: `llvm-extract` embeds the random
>    temporary input path in its ModuleID comment. The rejected artifact is
>    retained. ADR-0294's pushed correction uses a ModuleID-agnostic hash over
>    the otherwise exact bytes and source-qualified function identities. Its
>    fresh corrected result creates then reproduces byte-for-byte: 0/12 accepted,
>    all 12 stop at typed-CFG `unsupported_instruction`. The frozen bucket
>    selects only a T5.1.2 audit lane. Exact causes split into seven one-source
>    wide-memory rows, three cross-source call rows, one `alloca`, and one
>    non-scalar result; no mechanism receives code authorization. Next
>    preregister a broader cross-source semantic population or an executable
>    call-boundary experiment, not a syntax-only shim. ADR-0295 now
>    accepts the latter: an opt-in checked direct-body resolver for the two
>    exact PAC `@leaf` callers, with the unchanged default still rejecting
>    ordinary calls. Exact compiler/source/function identity reproduces live;
>    value+definedness-preserving callee execution equals an independent
>    transition specification over 100,000 tuples at zero disagreement; source
>    replay, canonical syntax, precise negative boundaries, and the expanded
>    nine-binary/88-test standing gate pass. This is now the inlined baseline
>    required by P5.2's modular-versus-inlined differential, not contracts,
>    external effects, a cross-source acceptance claim, or a revised 12-row
>    census. ADR-0296 now accepts the next call step: one explicit exact scalar
>    `leaf` contract verifies against its body once, retains only the checked
>    summary in caller reflection, and matches the inlined route over exact
>    normalized formulas plus 100,000 tuples at zero disagreement.
>    Its first slice requires a universally true precondition so a failed
>    `requires` cannot be hidden by pruning a transition. General call-site
>    obligations, relational havoc, annotations, recursion, memory, and
>    external effects remain separate work; do not widen syntax around them.
>    The general nonlinear-equivalence proof attempted during validation is
>    rejected after a disclosed 67.4 GiB anonymous-RSS OOM; the accepted exact
>    checker uses term identity plus conjunction associativity/`true`, a
>    two-second fallback, and a dedicated `loops/contracts.rs` module. At
>    ADR-0296 acceptance the standing gate was nine binaries / 94 tests.
>    ADR-0297 now accepts explicit call-site requirement
>    failures as path-conditioned obligations/bad states: a nontrivial
>    `requires` enters the transition only after its reached complement is
>    replayable and source-attributed through `bad`. The 100,000-row result is
>    33,334 valid / 33,334 defined violation / 33,332 source undefined, with
>    zero disagreement or dropped work; depth-1 PAC and internal-path/later-UB
>    controls pass. The standing gate is now nine binaries / 98 tests.
>    ADR-0298 now accepts the relational scalar result/havoc rule on the
>    checksum module: a fresh internal result, a separate verified `ensures`
>    constraint (never fabricated LLVM poison), exact-body checking, and a
>    replayed weak-contract havoc countermodel. Its 100,000 inputs classify
>    100,000 valid plus 100,000 violating result choices with zero dropped work;
>    the standing gate is 76 variants / 16 groups / ten binaries / 108 tests.
>    No annotation syntax, loop havoc, or external effects are yet authorized.
>    ADR-0299 now accepts the equivalent MIR-side modular checksum call: the
>    located typed scalar path verifies the same relation against the checked
>    MIR callee body, independently proves its panic predicate false, discards
>    that body, and retains a distinct havoc symbol plus relation. Separate MIR/
>    LLVM weak-contract countermodels and 100,000 valid plus 100,000 violating
>    choices per route pass with zero dropped work. The standing gate is now 81
>    variants / 17 groups / ten binaries / 114 tests, and the complete package
>    route passes at 1.8 GiB peak with zero swap inside the 4 GiB cap. General
>    panic contracts, annotations, unwind handling, memory/effectful calls, and
>    loops remain later boundaries; an LLVM definedness proof cannot replace
>    the MIR panic proof.
>    ADR-0315 now accepts the smallest remaining P5.2 runtime boundary:
>    one explicit input-dependent checked-MIR `panic_when` summary must be
>    proved against the exact callee, propagated into the caller panic term, and
>    used to guard the normal-return relation. Exact modular/inlined panic
>    equality, all 256 `u8` rows at exactly 255 normal/one panic, a concrete
>    callee-panic witness, mutation teeth, and the 117-test standing semantics
>    gate pass.
>    Existing constructors remain total (`panic_when = false`), and annotations,
>    unwind cleanup, memory/effects, loops, and LLVM panic inference stay out of
>    scope. This independent local lane advances while PLAN item 7 still awaits
>    a genuinely different second machine; it does not substitute for that row.
>    ADR-0316 now accepts the smallest source-annotation prerequisite after the
>    macro audit found two missing semantic seams: the source-AST path discarded
>    its tail result and assumed every witness must panic. Outer `#[verify]`
>    consumes typed `requires`/`ensures` markers for one straight-line scalar
>    function, retains the result, and gives normally returning postcondition
>    violations a distinct replay path. The exhaustive lowered-term gate covers
>    all 256 `u8` rows at exactly 255 admitted, zero safe violations, and 255
>    mutated violations with zero evaluation errors or drops; the complete
>    package, doctests, strict gates, and unchanged 117-test reflection gate
>    pass. It emits no modular summary and makes no source-to-MIR identity claim.
>    ADR-0317 now accepts the smallest authenticated source-contract-to-
>    checked-MIR bridge. One total annotated `u8::wrapping_add` function
>    translates into the existing relational contract AST, equals a hand-built
>    declaration, and both independently verify against 10,124 byte-identical
>    checked-MIR bytes captured from the exact registered source through its
>    owning Cargo build. The exact compiler-qualified wrapping-add intrinsic is
>    admitted only as typed two-`u8`/`u8` BV addition and does not consume the
>    one relational-call slot. Both resolvers match the inlined control over all
>    256 inputs at 256 normal/zero panic; removing the relation and source/body/
>    intrinsic/resource mutations fail closed. The root-independent scalar
>    summary reproduces under the pinned nightly, and the 123-test standing
>    semantics gate passes. This closes the bounded P5.2 v1 exit criteria:
>    additive source annotations, modular checksum composition on both checked
>    IRs, authenticated total source-to-MIR summary binding, and a committed
>    modular-vs-inlined differential. It deliberately avoids the MIR route's
>    unsupported nontrivial-`requires` boundary and adds no panic-summary
>    authoring. Do not widen branches, calls, effects, or unwind cleanup to make
>    the bridge useful.
>    ADR-0318 rejects the first roadmap-owned P5.3 page-table cell before any
>    capture or proof. Its operation/block audit fit ADR-0288, but the real
>    owning-Cargo path strictly rejected compiler-emitted nested `scope`
>    metadata for the named walk locals at `scope 1 {`. No raw artifact was
>    retained, the exact fixture source was restored, and no parser/test/code
>    change survives. Do not rewrite the source to dodge this result or widen
>    the parser retroactively; audit and preregister the exact semantically
>    inert scope grammar separately before retrying the bounded obligation.
>    ADR-0319 now accepts that exact prerequisite. Only bare decimal nested
>    `scope N {}` metadata containing admitted `let` declarations, debug
>    declarations, and child scopes flattens into the existing local inventory;
>    scope/debug metadata contributes no checked execution term. The 64-level
>    cap, strict brace/header/content/duplicate/type mutations, and 1,000-case
>    structured-noise gate pass. The exact owning-Cargo selection of
>    `walk_permissions` reaches the existing checked-memory profile from an
>    8,218-byte live compiler capture without adding an executable semantics
>    variant. No raw walk artifact or page-table proof is admitted; any retry
>    requires a fresh preregistered successor to rejected ADR-0318.
>    ADR-0320 now accepts that evidence-only successor without a production
>    semantic change. Four fresh owning-Cargo copies are byte-identical to the
>    authenticated 8,218-byte raw module; seven universal panic/spec/alignment/
>    permission claims pass, all three broken controls yield replayed source
>    witnesses, and the exact 4,096-row sampler has zero disagreement, error,
>    panic, or drop. Twelve semantic/authentication mutations have teeth, with
>    the redundant first mask truthfully rejected by artifact identity rather
>    than credited as a semantic delta. This closes bounded T5.3.2 v1 only;
>    continue P5.3 with FSM refinement and the obligation catalog, not a real-
>    MMU claim or an unpreregistered memory-model expansion.
>    ADR-0321 now accepts bounded deterministic scalar T5.3.3 v1. Four fresh
>    owning-Cargo captures are byte-identical to one authenticated 2,691-byte
>    MIR module; eight universal per-event proof groups and complete transition-
>    relation equality pass; spec and reflected systems are PDR-safe; and the
>    blind-injection control is PDR/BMC/source replayed. Exactly 2,048 exhaustive
>    reflection/spec/Rust rows have zero disagreement, error, panic, or drop.
>    No production semantics or public refinement API changed. Continue with
>    T5.3.4's obligation catalog, not an unpreregistered general protocol,
>    liveness, or real-network claim.
>    ADR-0322 now accepts that documentation-only closeout. Separate pages for
>    control-flow constant-time, bounded memory/page-table math, and FSM
>    refinement expose exact goals, evidence/authenticity routes, controls,
>    reproductions, and residuals; a comparison index is linked from Track 5
>    and the Verify scoreboard. T5.3.4 and bounded P5.3 v1 are complete without
>    upgrading the MIR-text T5.3.1 cell to compiler-authenticated evidence or
>    expanding the other two cells into real-system claims. Return to the
>    ranked Track 5 trajectory; the next phase-level milestone is P5.5 external-
>    target measurement, not an unpreregistered P5.3 residual.
>    P5.5 T5.5.1 now selects Maestro revision `650a3f62` and exactly three
>    device-number functions (`major`, `minor`, `makedev`) as the smallest
>    viable external cell. A pinned owning-kernel feasibility build emitted all
>    three as straight-line scalar LLVM, but that temporary output earns no
>    result. The next action is a zero-row T5.5.2 ADR freezing reproducible
>    whole-module capture, deterministic extraction, source replay, failure
>    taxonomy, and the GPL-derived-artifact no-vendoring boundary before any
>    target bytes or proof result are retained.
>    ADR-0323 now preregisters that capture without running it: two isolated
>    roots must produce byte-identical complete kernel LLVM modules; the exact
>    three symbols must extract, assemble, and pass the existing checked scalar
>    parser; only `llvm-extract`'s known input-path `ModuleID` line is excluded
>    from extracted identity. Third-party bytes stay local. Implement and run
>    this T5.5.2 gate next; no inverse-property query is authorized yet.
>    The corrected official ADR-0323 run is negative at the earlier full-module
>    gate: both isolated builds finish below 1 GiB peak RSS, but root A emits
>    36,037,712 bytes and root B 36,038,199 bytes with distinct hashes. The run
>    stops before extraction/parser admission and atomically retains no target
>    bytes. Next preregister a non-crediting byte/line root-drift diagnostic;
>    do not retroactively normalize, extract only the selected functions, or
>    run an inverse-property query.
>    ADR-0324 now preregisters that diagnostic without rerunning the builds. It
>    must retain the two modules locally, classify every complete-diff line,
>    detect absolute roots and symbol drift, and compare all three extracted
>    checked typed projections. Even exact selected-function equality cannot
>    revise ADR-0323 or accept T5.5.2; it may select only a later independently
>    specified canonical-identity proposal.
>    ADR-0324's result diagnoses broad build-root drift: 319,598 changed lines,
>    seven absolute `utils` dependency paths in each module, and different
>    mangled symbols/current canonical hashes for all three selected functions.
>    The registered trailing rustc remap reached only the final kernel crate;
>    each selected body still admits at 6/5/13 instructions, but that earns no
>    capture credit. Next preregister a fresh two-root build with dependency-
>    wide remapping and require raw full-module equality before extraction;
>    never normalize the observed modules or erase names after the fact.
>    ADR-0325 now preregisters that fresh v2 build. Exact Cargo-encoded flags
>    preserve `-Zexport-executable-symbols` and apply the root remap to every
>    target dependency; the final rustc tail carries no remap. Both full
>    modules must contain zero real-root tokens and match as raw bytes before
>    symbol rediscovery or parser admission. Implement/run this capture next;
>    inverse-property construction remains unauthorized.
>    ADR-0325 v2 is negative. Dependency-wide remapping removes all real-root
>    tokens and emits the shared prefix seven times in each module, but raw
>    outputs still differ at 36,037,894 vs 36,038,325 bytes. Extraction never
>    runs. The remaining variable is the distinct remap-rule input itself.
>    Next preregister separate physical roots/targets mounted sequentially at
>    identical in-namespace paths (working unprivileged `bwrap` is available),
>    with raw equality still required and no output normalization.
>    ADR-0326 preregisters v3: exact Bubblewrap identity/argv, distinct physical
>    source and target roots at identical `/axeyum-vroot/{source,target}` paths,
>    no remap flags, zero host-path tokens, and raw full-module equality before
>    extraction. Implement/run this final bounded build-route correction next;
>    no proof query is authorized.
>    ADR-0326 closes that final route negative before LLVM emission. The
>    corrected constructed-root namespace reaches Cargo, but Maestro's owning
>    build unconditionally downloads the configured GNU Unifont input; the
>    registered network-isolated namespace fails name resolution. Zero builds
>    complete, no module/extraction/parser/solver stage exists, and no OOM or
>    partial output occurs. Do not add a v4 font cache, network exception, or
>    output normalization after observation. T5.5.2 now returns to replacement
>    external-target/build-route selection under a fresh zero-row decision.
>    ADR-0327 now makes that replacement decision without running an external
>    result: Tock revision `ac5d597d` and its source-used 32/64-bit integer-log
>    helpers win the bounded comparison. Their owning LLVM 22 build is small and
>    build-script-free, but the strict frontend correctly declines call-result
>    `range` poison and `llvm.ctlz` zero-poison semantics. Implement only that
>    typed/canonical/proved/fuzzed prerequisite over existing BV terms next;
>    it adds no IR operator and external capture remains separately gated.
>    ADR-0327 now accepts that prerequisite. Typed syntax preserves the exact
>    range/signature/tail/flag, checked lowering keeps zero/range poison in
>    definedness, exhaustive widths 1--8 and deterministic 32/64-bit rows agree
>    with independent oracles, threshold-partition proofs pass, and four
>    mutation classes replay. The standing gate is 82 variants / 18 groups /
>    12 binaries / 129 tests. Next preregister the zero-row authenticated Tock
>    capture with stable virtual roots, validated locked cache, offline raw-
>    module equality, LLVM-22 extraction, exact admission, and atomic output;
>    do not retain target bytes or construct proof obligations before it.
>    ADR-0328 now preregisters that zero-row capture. It requires two complete
>    exact Git archives at identical Bubblewrap paths, a validated read-only
>    locked cache, no network, raw full LLVM-module identity, compiler-matched
>    hash-pinned LLVM 22 extraction, exact two-function checked admission, and
>    atomic local-only output under the 4 GiB cap. Implement producer/tests/
>    registration and commit them before the first official build; LLVM 21,
>    text slicing, feasibility-hash seeding, and early proof queries are barred.
>    `puts` remains rejected because it neither has a supplied body nor unlocks
>    the rest of `hello.c`'s memory/call surface. Do not build early-exit
>    support from the ADR-0293 singleton. General rejected-loop unrolling, MIR,
>    multi-latch/
>    early-exit/switch/memory loops, general places, and LLIR remain open, and
>    the accepted Linux recall route stays untouched.
>
> Convert survived strengths (cheap):
> 7. [INTEGRATION] Reproducibility-for-free, measured -- work-bound + canonical
>    policy -> identical findings run/machine/backend on the recall corpus.
>    ADR-0302 now preregisters the exact distinction that claim needs before a
>    full row exists: two rotated repetitions of Axeyum and Z3 authority per
>    machine; exact report identity within each authority/run/machine; exact
>    backend identity for finding, work, and stop projections; and separately
>    retained replay-valid witness/model diversity. Glaurung candidate
>    `31f7ebe` removes the machine-local Axeyum dependency and absolute report
>    path and emits the actual selected authority. At least two genuine
>    machines are mandatory; one host can close only run stability and backend
>    finding parity. The first registered `server0` observation now closes those
>    local gates: both repetitions are exact within each authority and all four
>    runs have one finding/work digest, while two distinct replay-valid model
>    digests remain. Its analysis is correctly `accepted=false` solely for
>    `cross_machine_population_missing`. A second genuine machine is the next
>    action; do not call containers or two labels cross-machine, or require
>    arbitrary SMT witnesses to be identical. A deterministic, fail-closed
>    eight-object transfer bundle now removes the machine-local artifact-root
>    obstacle; verification binds its full path/hash set to both frozen
>    registrations before extraction. The next step is collection on a genuinely
>    different host, not more server0 sampling.
> 8. [AXEYUM] **DONE (ADR-0227).** Executable Node and Chromium runs cover
>    75,000 measured solves each with zero mismatch/trap; small-query medians are
>    13--71 us. The release browser runtime is 1,801,662 bytes / 541,248 bytes
>    as separately gzip-9-compressed assets. This is absolute deployment
>    evidence, not native parity or a minimum parser footprint.
>
> Rigor / defense:
> 9. [BOTH] **DONE (ADR-0303 rejected; ADR-0304 accepted).** Warm-reuse
>    additivity vs a GREEN/GreenTrie engine cache is now measured with 120 fresh
>    processes and 387,060 replay-checked executions over four fixed Glaurung
>    drivers. The corrected canonical opportunity is 8,001/12,902 exact hits
>    (62.01%) and 8,563/12,902 exact-plus-implication hits (66.37%). The frozen
>    successor passes every correctness/work/classification/resource gate with
>    zero replay failure, eviction, bypass, or owner leak. Warm state remains
>    additive under exact caching on 2/4 drivers and structural caching on 3/4;
>    the remaining cells are inconclusive under the preregistered 3% CV gate.
>    But engine cache-on slows the already-warm solver on all three drivers with
>    conclusive warm cache contrasts, and raises mean maximum RSS by 7.6%--67.3%.
>    Therefore keep Axeyum warm reuse as the product mechanism and leave the
>    Glaurung engine cache experimental/cold-policy-specific. Report only the
>    per-driver intervals in the committed result, never a pooled headline. The
>    first ADR-0303 campaign remains rejected and contributes no timing claim.
> 10. [AXEYUM] **DONE.** Staged artifact cleanup (split `reconstruct.rs` 18.5k,
>    namespace the ~567-item public API, dedup repeated term walkers, and model
>    config as types), plus related-work positioning vs Veritas,
>    attacker-control, and the MS agentic system. The first bounded cleanup
>    consolidates 15 byte-equivalent binary `collect_top_conjuncts` copies into
>    one tested crate-private helper, removing 102 net source lines with no
>    public API change. `auto` intentionally keeps its arbitrary-arity walker;
>    `array_axiom` intentionally keeps BV1 asserted-conjunction semantics. All
>    883 full-profile solver library tests and clippy `-D warnings` pass. The
>    measured reconstruction inventory then classifies all 34 direct variants:
>    5 custom constructive encodings and 29 checked validators sharing one
>    deterministic wrapper. R1 routes all 26 formerly inline emission tails
>    through that helper, shrinking `reconstruct.rs` by 130 lines / 8,924 bytes.
>    A legacy-equivalence test covers every registered stem/role pair; all 884
>    full-profile tests and clippy pass. R2 then moves the entire 34-variant
>    direct lane behind one explicit `reconstruct/direct.rs` seam, reducing the
>    main file from 18,387 to 16,999 lines. Only a boolean finite-domain scan
>    predicate crosses back to the parent; private certificate types stay
>    private. All 884 tests, byte-equivalence checks, and clippy remain green.
>    R3's first family is now complete: the Alethe equality builders live in
>    `reconstruct/equality.rs`, while shared literal parsing and the universal
>    kernel gate remain parent-owned. The public `reconstruct_eq_step` surface is
>    unchanged; only three narrow clausal-walk helpers cross back to the parent.
>    Transitivity and congruence generated-source snapshots remain byte-identical,
>    and all 885 full-profile tests plus clippy pass. `reconstruct.rs` is now
>    16,476 lines / 720,714 bytes. The follow-on census separates the two names:
>    direct array certificates already moved in R2 and the remaining ABV path is
>    only 44 lines of orchestration, while datatype owns a cohesive proof family.
>    That 2,313-line family now lives in `reconstruct/datatype.rs`; tester,
>    distinctness, injectivity, and acyclicity source snapshots are byte-identical,
>    and all 886 tests, clippy, and rustdoc pass. The parent is 14,189 lines /
>    618,110 bytes. The quantifier census then identifies one cohesive 853-line
>    universal-instantiation/existential-elimination family; it now lives in
>    `reconstruct/quantifier.rs`, while the existing 3,665-line quantified-BV
>    instance-set module remains separate. The public forall/exists entry points
>    are unchanged, only the existing test-only forall-axiom helper crosses the
>    seam, and universal plus existential generated-source snapshots are
>    byte-identical. All 887 tests, clippy, and rustdoc pass. The parent is now
>    13,350 lines / 580,831 bytes. The resolution/CNF census confirms two proof
>    families rather than one broad move. The 2,150-line propositional
>    resolution/RUP family now lives in `reconstruct/resolution.rs`; CNF gate
>    introduction remains parent-owned for the next slice. Four shared context
>    methods, two clausal types, and thirteen helper seams are `pub(super)` only,
>    each with a measured CNF, quantified-BV, direct-certificate, or bit-blast
>    consumer. The public resolution entry point is unchanged, a representative
>    generated-source snapshot remains byte-identical, and all 888 tests,
>    clippy, and rustdoc pass. The parent is now 11,225 lines / 498,127 bytes.
>    The separate 1,578-line CNF gate-introduction family now lives in
>    `reconstruct/cnf.rs`. Eight shared context methods, one assignment
>    type/constructor, and six proof helpers are `pub(super)` only, each with an
>    existing resolution-test, quantified-BV, direct-certificate, or bit-blast
>    consumer. The public CNF-rule entry point is unchanged; specialized n-ary
>    `and_pos` and general `xor_neg1` generated-source snapshots remain
>    byte-identical. All 889 tests, clippy, and rustdoc pass. The parent is now
>    9,680 lines / 433,992 bytes. The 1,956-line bit-blast/QF_BV family now
>    lives in `reconstruct/bitblast.rs`, with all five public entry points
>    unchanged. Five production-only sibling seams serve CNF or quantified-BV;
>    three additional parent-visible items preserve an existing datatype-
>    projection audit test. Pointwise BVAND and ripple-carry-add generated-source
>    snapshots remain byte-identical; all 890 tests, clippy, and rustdoc pass.
>    The final R3 census confirms one cohesive arithmetic family: LRA, SOS,
>    Farkas, the shared arithmetic kernel context/ring normalizer, and
>    disjunctive-LRA scanning are coupled by exact-linear invariants rather than
>    being separate projects. Its 4,970 lines now live in
>    `reconstruct/arithmetic.rs`; all three public LRA/SOS entry points are
>    unchanged, while only four production functions plus the private
>    exact-linear form and two test-only Farkas helpers cross the parent seam.
>    Representative LRA and SOS Lean modules remain byte-identical; all 891
>    tests, clippy, and rustdoc pass. The parent is now 2,793 lines / 122,834
>    bytes. R3 is complete. Continue with R4's measured visibility/root-API
>    audit; keep the thin ABV orchestration parent-owned and do not mix public
>    renaming with solver behavior. R4a now introduces the canonical
>    `axeyum_solver::proofs` facade without deleting or changing any historical
>    root path: old aliases remain callable and type-identical but are hidden
>    from rustdoc. The all-feature documented root falls from 549 to 442 items;
>    minimal `qfbv` falls from 36 to 26, while 113 proof-facing entries are
>    organized under the facade. Default-`qfbv` and all-feature compatibility
>    gates, 891 solver-library tests, strict clippy, and warning-denied rustdoc
>    pass under the bounded one-job profile. ADR-0305 records the compatibility
>    policy. Continue R4 with separate measured `theories` and `certificates`
>    censuses; do not perform a broad rename or combine API organization with
>    solver behavior. R4b now completes the certificate-catalog census: 31
>    array and 72 quantified entries live under the full-only
>    `certificates::{arrays, quantifiers}` facade, while the two finite-
>    quantifier Alethe emitters join `proofs::alethe`. General `check_model`
>    replay and array decision procedures stay documented at the root for the
>    separate theory census. The all-feature root falls from 442 to 338 items;
>    the certificate subtree owns 105 entries, the proof subtree now owns 115,
>    and minimal `qfbv` remains unchanged at 26. Historical paths remain
>    callable and type-identical. All 891 solver-library tests, strict clippy,
>    compatibility gates, and warning-denied rustdoc pass under the bounded
>    profile. ADR-0306 records the boundary. Continue R4 with the theory API
>    census, not a source-file-based sweep or behavior change. R4c now completes
>    that census: 63 direct contracts/procedures live under seven semantic
>    `theories` submodules, reducing the all-feature documented root 338→276
>    while minimal `qfbv` remains 26 and does not expose the full-only facade.
>    Model replay, auto-dispatch, SMT-LIB, optimization, interpolation, symbolic
>    execution, verification, proofs, and certificates stay outside the theory
>    namespace; historical paths remain callable and type-identical. Dedicated
>    compatibility gates, all 891 solver-library tests, strict clippy, and both
>    warning-denied rustdoc profiles pass under the bounded profile. ADR-0307
>    records the boundary. The three review-requested facades are now measured;
>    next census the remaining cross-cutting root domains independently before
>    deciding on another facade. Do not turn `theories` into a catch-all or mix
>    this artifact-readiness lane with solver/concretization behavior. R4d now
>    accepts the first independent cross-cutting boundary: 66 existing BMC/
>    k-induction, Horn, IMC, PDR, symbolic-execution, and tiny-BV reference-VM
>    contracts live under six full-only `verification` submodules. The
>    all-feature documented root falls 276→211, the subtree contains 72 entries
>    including its grouping modules, and minimal `qfbv` remains 26 with no
>    verification surface. Historical paths remain callable and type-identical;
>    all 891 solver-library tests, strict clippy, compatibility gates, and both
>    warning-denied rustdoc profiles pass under the bounded profile. ADR-0308
>    records the boundary. Continue with separate censuses for optimization,
>    SMT-LIB, interpolation, and general refutation utilities; do not create a
>    miscellaneous catch-all or change solver behavior. R4e now groups 40
>    existing model-minimization, MaxSAT, and scalar/multi-objective contracts
>    under three full-only `optimization` submodules. The all-feature documented
>    root falls 211→172 and the subtree contains 43 entries including its
>    grouping modules; minimal `qfbv` remains 26 with no optimization surface.
>    Pbls remains a SAT decision backend, SMT-LIB optimization commands remain
>    with the textual front door, and `Solver` remains a compact consumer facade.
>    Historical paths remain callable and type-identical; all 891 solver-library
>    tests, strict clippy, compatibility gates, and both warning-denied rustdoc
>    profiles pass under the bounded profile. ADR-0309 records the boundary.
>    Next census SMT-LIB independently, followed by interpolation and general
>    refutation utilities; continue to keep API cleanup behavior-neutral. R4f
>    now exposes the existing full-only `smtlib` module after confirming its
>    exact 25 public items equal the complete root-exported text-front-door
>    surface with no public helper leakage. Duplicate root aliases remain
>    callable and type-identical but are hidden from rustdoc. The all-feature
>    documented root falls 172→148; minimal `qfbv` remains 26 and has no SMT-LIB
>    module. All 891 solver-library tests, strict clippy, compatibility gates,
>    and both warning-denied rustdoc profiles pass under the bounded profile.
>    ADR-0310 records the boundary. Next census interpolation independently,
>    followed by the remaining general refutation utilities. R4g now groups the
>    existing common outcome plus QF_BV, QF_UF, LIA, LRA, UFLIA, and UFLRA
>    interpolation contracts under a full-only `interpolation` facade. Twenty-one
>    root entries move into a 27-entry subtree including six grouping modules;
>    the all-feature documented root falls 148→128, while minimal `qfbv`
>    remains 26 with no interpolation surface. Model-based projection and two
>    previously unreachable verifier functions stay outside the facade.
>    Historical paths remain callable and type-identical; all 891
>    solver-library tests, strict clippy, compatibility gates, and both
>    warning-denied rustdoc profiles pass under the bounded profile. ADR-0311
>    records the boundary. Next census the remaining general
>    refutation/certificate utilities and core solver helpers without inventing
>    a miscellaneous namespace. R4h now extends `certificates` with four
>    semantic catalogs for 51 existing checked arithmetic, finite-domain,
>    structural, and UF refutation contracts. The previously root-only QF_UF
>    Alethe emitter also joins `proofs::alethe`. The all-feature documented root
>    falls 128→77, the certificate subtree grows 105→160, and the proof
>    subtree grows 115→116; minimal `qfbv` remains 26 with no certificate
>    module. General decision procedures, `check_model`, SAT backends, and solver
>    front doors remain outside the catalogs. Historical paths remain callable
>    and type-identical; all 891 solver-library tests, strict clippy,
>    compatibility gates, and both warning-denied rustdoc profiles pass under
>    the bounded profile. ADR-0312 records the boundary. Perform one final
>    residual query-construction/core-helper census, preserving the compact
>    solver front door and stopping R4 if no independent non-catch-all boundary
>    is justified. R4i identifies exactly one final independent family: 12
>    existing `distinct`, cardinality, and pseudo-Boolean term constructors now
>    live under a 14-entry full-only `constraints` subtree. The all-feature
>    documented root falls 77→66, while minimal `qfbv` remains 26 with no
>    constraints module. Abduction, model-based projection, model replay,
>    backends, incremental state, strategies, and solver front doors stay at the
>    root. Historical paths remain callable and type-identical; all 891
>    solver-library tests, strict clippy, compatibility gates, and both
>    warning-denied rustdoc profiles pass under the bounded profile. ADR-0313
>    records the boundary and closes R4. Further namespace work requires new
>    consumer evidence. Continue item 10 with the separate typed-configuration
>    audit; do not combine behavior-bearing configuration changes with this
>    documentation-only series. That audit is now complete in ADR-0314. The one
>    real illegal state -- simultaneous dense-demand and range-demand cold
>    lowering -- is unrepresentable as
>    `BitLoweringMode::{Eager, DemandSliced, RangeSliced(policy)}`. Existing
>    fluent selectors remain with explicit last-call-wins semantics; the
>    benchmark keeps its historical CLI flags, JSON keys, and hash bytes, and
>    the actual Glaurung minimal-`qfbv` consumer compiles unchanged. The rest of
>    the configuration census found independent options or documented harmless
>    no-ops, so do not broaden this into a boolean-grouping sweep. This closes
>    the Axeyum half of reviewer item 8. Next re-rank the remaining item-10
>    artifact work from measured duplication/module review cost rather than
>    reopening R4 or changing solver policy without a separate ADR. The measured
>    residual inventory is now recorded in
>    [`artifact-readiness-refactor-inventory.md`](docs/research/08-planning/artifact-readiness-refactor-inventory.md).
>    `abv.rs` remains the largest reviewer-facing wall at 14,953 lines, but its
>    exact 3,514-line inline test module is the lowest-risk first cut: move it to
>    `abv/tests.rs` for a 23.5% visible reduction with no production seam or API
>    change. Follow with the 334-line eager array-elimination certificate, then
>    census the 4,968-line lazy-ext lane before exposing helpers. The
>    1,196-line integer-inequality reconstruction tail follows; CAD
>    parameterization remains later because it changes correctness-sensitive
>    solver code and needs a semantic differential gate. Execute each as a
>    separate add/commit/push checkpoint. A1 is now complete: the unchanged ABV
>    test bodies live in `abv/tests.rs`, six compile-time corpus paths gained the
>    required relative parent component, and `abv.rs` falls 14,953→11,443 lines
>    (23.5%). All 891 solver-library tests keep their `abv::tests::*` identities;
>    strict Clippy and both strict rustdoc profiles pass. Continue with A2's
>    334-line eager array-elimination certificate as a distinct trust-boundary
>    module, preserving its two public paths and limiting the parent seam to the
>    two measured helpers. A2 is now complete: the 333-line certificate body
>    lives in the private 340-line `abv/array_elim_certificate.rs`; both public
>    paths are unchanged, the two parent helpers remain private, and dedicated
>    mutation/recheck, Ackermann-control, Lean, namespace, 891-library-test,
>    Clippy, and rustdoc gates pass. `abv.rs` is now 11,112 lines, down 25.7%
>    across A1--A2. A3's census rejects a monolithic 4,968-line move: the replay
>    and repair diagnostics are shared with preceding ROW projection code and 16
>    of their private items are reached directly by the existing test child. The
>    clean 446-line lazy-ext CEGAR orchestration/refinement unit now lives in
>    `abv/lazy_ext.rs` with ten private items and exactly one `pub(super)` parent
>    entry point; no test seam or public path changed. `abv.rs` is 10,675 lines,
>    down 28.6% across A1--A3. I1 is now complete: the 1,196-line
>    integer-inequality body lives in the private 1,201-line
>    `int_reconstruct/inequality.rs` child; its three public functions retain
>    exact paths and only `lt_lit_lit` crosses back as a `pub(super)` helper for
>    six earlier proof sites. A representative rendered Lean module is
>    byte-identical before/after (SHA-256 `27edf9b0...205de`), all 14 focused
>    interval tests including three real-Lean checks pass, and the UFLIA,
>    namespace, 891-library-test, Clippy, and rustdoc gates remain green.
>    `int_reconstruct.rs` is 7,683 lines, down 13.4%. N1's CAD census is now
>    frozen in
>    [`cad-parameterization-gate.md`](docs/research/08-planning/cad-parameterization-gate.md):
>    the repetition is not one triplicated algorithm, and algebraic lifting
>    remains separate. N1a is authorized narrowly to share the duplicated
>    rational substitution/univariate cell decision behind the existing strict
>    and non-strict wrappers. Projection, cell selection, budget charges,
>    deadline polls, algebraic fallback, witness order, and public paths do not
>    change in that checkpoint. N1a is now complete: one private helper owns
>    rational substitution/constant folding/univariate decision while the two
>    semantic wrappers remain. Exact models stay `(x=1,y=1)` for the strict
>    quarter-disk and `(x=1,y=0)` for the non-strict boundary. All 86 focused
>    NRA tests, the 2,000-seed Z3 differential sweep (1,807/1,807 joint
>    agreements, 1,293 replayed SAT, `DISAGREEMENTS: 0`), all 891 library tests,
>    strict Clippy, both rustdoc profiles, links, and the OOM audit pass. The
>    file falls 7,544→7,521 lines. N1b is now complete as a second independent
>    checkpoint: `two_var_critical_roots` owns only projection, isolation,
>    ordering/deduplication, and the cap. Strict retains its explicit entry poll;
>    non-strict retains its caller behavior; sampling/lifting remain separate.
>    Exact critical roots `[0,1]` are pinned, removing the strict poll makes its
>    mutation control fail, the 2,000-seed tally is exactly unchanged, and all
>    893 library tests plus strict lint/doc/OOM gates pass. The file is 7,485
>    lines, down 59 across N1a--N1b. N1c is now complete and closes N1: one
>    `visit_rational_cells` recursion takes an explicit
>    `RationalCellSelection::{OpenOnly, OpenAndRationalSections}` behind the
>    historical strict/non-strict wrappers, while algebraic traversal stays
>    separate. Exact `(1,1,1)`, `(1,-1,-1)`, and required zero-cell
>    `(0,-1,-1)` witnesses pin strict, non-strict ordering, and boundary
>    coverage; dropping rational sections or visiting them before open cells
>    trips the corresponding mutation control. The fixed 2,000-seed tally is
>    exactly unchanged for a third run, all 895 library tests and strict
>    lint/doc/OOM gates pass, and production falls 7,077→6,944 lines across N1.
>    Added semantic controls make the whole file 7,503 lines, still 41 below
>    baseline. Re-rank the remaining artifact residuals before authorizing a new
>    structural slice; do not genericize the algebraic value-domain traversal
>    without new evidence.
>    That post-N1 ranking is now complete. The ABV replay/repair residual remains
>    deferred because 16 private items are test-reached and ROW/extensional
>    replay ownership is shared; further CAD consolidation remains barred at the
>    rational/algebraic boundary. I2 is now complete: the contiguous ADR-0108
>    quantified-counterexample-cover proof family lives in the private
>    1,465-line `int_reconstruct/counterexample_cover.rs` child with explicit
>    imports and the same crate-visible router/public reconstructor paths. A new
>    byte-identity control reproduces the pre-move 7,197-byte Lean module at
>    FNV-1a `e592f1787653a4bf`; all seven ordinary cover controls, the explicitly
>    exercised real-corpus Lean reconstruction, all 895 library tests, strict
>    Clippy, and both rustdoc profiles pass. `int_reconstruct.rs` falls
>    7,683→6,233 lines (18.9% in I2; 29.8% from its original 8,876). Remeasure
>    reviewer navigation and dependency seams before authorizing a successor.
>    Do not promote `incremental.rs`, `qinst_egraph.rs`, or `auto.rs` merely
>    because they are large.
>    I3 is now complete: the ADR-0101/0106 single-pivot equality-partition
>    reconstruction family lives in private 1,200-line
>    `int_reconstruct/equality_partition.rs` with explicit imports and the same
>    crate-visible router/public reconstructor paths. The SDLX generated module
>    remains exactly 30,644 bytes at FNV-1a `84fe8e457b9b6b27`; all twelve
>    focused reconstruction/evidence controls pass, including every 64-seed Z3
>    differential row. All 895 library tests, strict Clippy, and both rustdoc
>    profiles pass. `int_reconstruct.rs` falls 6,233→5,045 lines in I3 and is
>    now 43.2% below its original 8,876 lines. Remeasure reviewer navigation and
>    dependency seams before authorizing any successor. No ABV replay,
>    algebraic CAD, generic large-file, performance, or concretization work is
>    implied by completion.
>    I4 is now complete: the ADR-0095/0104 Euclidean-residue reconstruction
>    family lives in private 354-line `int_reconstruct/euclidean_residue.rs`
>    with explicit imports, unchanged router/public paths, and only the existing
>    private `peel_closed_foralls` parent helper. The committed `clock-3` module
>    remains exactly 16,025 bytes at FNV-1a `4e97fa307a29d1d0`; all six focused
>    reconstruction/evidence controls, all 895 library tests, strict Clippy, and
>    both rustdoc profiles pass. `int_reconstruct.rs` falls 5,045→4,701 lines
>    and is now 47.0% below its original 8,876 lines. Remeasure before any
>    successor; affine growth remains an independent candidate, not implied.
>    I5 is now complete: the ADR-0097/0105 affine-growth reconstruction family
>    lives in private 467-line `int_reconstruct/affine_growth.rs` with explicit
>    imports, unchanged router/public paths, and only the existing private
>    `peel_closed_foralls` parent helper. `repair-const-nterm` remains exactly
>    43,108 generated Lean bytes at FNV-1a `dd4d24cdf0168fb9`; all nine focused
>    controls pass, including every 64-seed Z3 positive and satisfiable-near-
>    miss row. All 895 library tests, strict Clippy, and both rustdoc profiles
>    pass. `int_reconstruct.rs` falls 4,701→4,246 lines and is now 52.2% below
>    its original 8,876 lines. Remeasure before any successor; no further
>    integer-family split is implied.
>    I6 is now complete: the original ADR-0042 Diophantine reconstruction lives
>    in private 767-line `int_reconstruct/diophantine.rs` with its two public
>    paths unchanged and eight family-only context methods.
>    Seventeen context methods already used by the parent or sibling proof
>    families remain in the parent without visibility widening. The first
>    compile gate corrected the initial same-file-only census by identifying
>    four sibling-consumed methods and four transitive helpers before
>    acceptance. The canonical `two_x_eq_one` Lean module remains exactly
>    868,243 bytes at FNV-1a `d2f76675b12631ea`; all 5 reconstruction, 4
>    evidence, 19 committed math-resource, and 10 namespace controls pass, as
>    do all 895 library tests, strict Clippy, and both rustdoc profiles.
>    `int_reconstruct.rs` falls 4,246→3,489 lines / 141,804 bytes, 60.7% below
>    its original 8,876 lines. I6 closes the integer structural lane; do not
>    turn residual size into a queue.
>    Closed-universal and nested-XOR reconstruction remain parent-owned because
>    their distinct entry points share a large kernel-helper region; do not hide
>    both behind one cosmetic module.
>    Revisit the 4,531-line ABV replay/repair residual only
>    with a seam that preserves its shared ROW ownership and test privacy rather
>    than widening dozens of helpers for a cosmetic file move.
>    The final closure audit is recorded in the completed
>    [`artifact-readiness-refactor-inventory.md`](docs/research/08-planning/artifact-readiness-refactor-inventory.md).
>    Related-work positioning against Veritas and Microsoft codename MDASH, plus
>    the explicit separation of attacker provenance, region ownership,
>    concretization choice, reachability, violation, and exploitability, now
>    lives in
>    [`agentic-binary-security-positioning.md`](docs/research/02-ecosystems/agentic-binary-security-positioning.md).
>    This closes the bounded Axeyum artifact/code blocker, not the paper's open
>    cross-machine reproducibility, broader recall/generality, proof-prevalence,
>    or performance questions. Any structural successor needs new consumer
>    evidence; raw file size does not reopen item 10.
>
> Do NOT reopen symbolic memory / concretization coverage, chase raw-union
> coverage, or claim performance leadership: the neutral warm baseline (#2) has
> landed and rejects that framing. Full downstream/SOTA rationale and sequencing:
> [`docs/research/08-planning/axeyum-glaurung-pareto-strategy.md`](docs/research/08-planning/axeyum-glaurung-pareto-strategy.md).
> The 2026-07-16 consumer feedback remains binding where later evidence did not
> supersede it: preserve strict sort checking and precise `IrError`s, structural
> `Unknown`, lean scalar-model construction, shared replay memoization, and
> self-rechecked DRAT. Its historical 2.8--4x warm claim is integration evidence,
> not a paper headline after the fair six-cell Bitwuzla/Z3 result. The durable
> item-by-item disposition, including the difference between closed safeguards,
> superseded claims, and genuinely open work, is recorded in
> [`glaurung-feedback-reconciliation-2026-07-20.md`](docs/research/08-planning/glaurung-feedback-reconciliation-2026-07-20.md).
> The user-provided July 16 copy and current Glaurung reviewer checklist were
> rechecked on 2026-07-21; the evidence-based dispositions did not change.
> In particular, A0 remains completed reproducibility infrastructure whose
> five-policy sweep found no validated coverage delta; it is not the active
> research lane, and ADR-0326's external-target result does not reopen it.

> **WASM-safe speed: do not invest in SIMD (reviewed 2026-07-20).** A reported
> scratch prototype explored portable SIMD against the WASM constraint, but its
> named source directories are absent and its numbers are not accepted evidence.
> The reported finding was: (1) portable SIMD is WASM-safe
> -- one pure-Rust `wide`/`+simd128` source lowers to AVX2 on native and simd128
> on wasm32, and clean loops autovectorize under `+simd128` (the free win, plus a
> scalar-fallback build for WASM's lack of runtime SIMD detection); BUT (2)
> axeyum's dominant cold cost (AIG `AndUniqueTable` hash-probe + CNF
> `tseitin_encode` fingerprint/clause work, ADR-0200/0259) is
> pointer-chasing/hashing and does NOT vectorize -- near-zero SIMD surface on the
> 84%. **Decision:** do not invest in SIMD. A future simd128/scalar dual build is
> permissible only behind its own committed gate; it is not a landed
> configuration or speed claim. The cold-path lever stays algorithmic reduction (word-level
> / abstraction-refinement per GQ5/B2), which is inherently WASM-safe because
> "do fewer operations" helps every target. **Forbidden as envelope-breaking:**
> linking a C SAT core, AVX-512 / `pulp`-style native-only multiversioning, and
> SharedArrayBuffer threading (parallel exploration is a native-throughput play,
> not a WASM lever). The WASM-safe lever and the actual-bottleneck lever coincide
> (both are *do less work*), so keeping WASM and pursuing cold parity point the
> same direction. Detail + prototype evidence:
> [`axeyum-glaurung-pareto-strategy.md`](docs/research/08-planning/axeyum-glaurung-pareto-strategy.md)
> Pillar B4.

> **Cold-path layout tested and rejected at its fixed gate (2026-07-20).** A
> scratch prototype motivated a data-structure alternative on a real-derived
> cold hot path. `axeyum-cnf`'s `CnfClause { lits: Vec<CnfLit> }` is one heap
> allocation per clause (~272k tiny clauses, ADR-0259) -- the classic SAT
> anti-pattern. A flat clause arena (Kissat/CaDiCaL; Varisat in Rust) measured, on
> the real distribution, **3.9x faster construction, 1.61x faster fragmented-heap
> scan, 2.4x less memory**; the DB is append-only (grep-confirmed: `clauses.push`,
> no remove/retain), so no compaction downside. Pure-Rust, WASM-safe, and the
> memory win doubles as a deployability win (amplified under wasm `dlmalloc`).
> Honest scope: emission/allocation sub-phase only, not all of CNF -- measure
> end-to-end in-tree before any number; do NOT touch the fingerprint map (ADR-0200
> regressed 8.55%) or the AIG table (already index-based). Net: the cold-path lever
> is **algorithmic reduction + memory layout** (both "do less work", WASM-safe by
> nature); SIMD stays ruled out. That historical implementation recommendation
> is superseded by ADR-0285. Context:
> [`cold-path-data-structures.md`](docs/research/08-planning/cold-path-data-structures.md).
> ADR-0285's in-tree production test is now **closed negative before timing**.
> The implementation and artifact-v38 validator passed pre-observation at
> `725858b1` / `a57d5ace`; the one clean 162-query process then preserved every
> decision, replay, construction count, and offset invariant. Aggregate logical
> storage was favorable at 54.08% of the legacy lower bound, but the frozen
> per-instance <=80% gate failed on five payload-dominated singleton clauses
> (92.86--96.27%). Do not relax that rule post-observation or time the candidate.
> The artifact is retained and production is restored at `56936920` /
> `f3456365`. The named scratch prototypes are absent and remain motivating
> history, not reproducible or accepted evidence; any successor requires a new
> independently justified zero-row ADR.

> **Data-structure candidate sweep closes the dense-memo candidate negative
> (2026-07-20, ADR-0300).** After ADR-0285 closed the flat clause arena, the
> follow-up audit found one independent mechanism: `axeyum-bv` uses
> `BTreeMap<TermId, Vec<AigLit>>` for exact lookups on dense insertion-order
> `u32` IDs and never iterates it for semantic output. The reported 3.89x
> dense-plus-`Rc` scratch result is not accepted evidence: every named
> scratchpad and diary path is absent from this checkout, and it combines two
> mechanisms. ADR-0300 therefore preregisters only `Vec<Option<Vec<AigLit>>>`,
> retaining all literal-vector clones and lift maps. Representation-neutral
> artifact-v39 telemetry now records the BTree baseline representation, exact
> lookup/hit/write and payload/storage accounting, root-width invariants, and
> deterministic ordered lowering/CNF regression digests. A separate fail-closed
> analyzer re-sums every row and permits only the registered representation
> deltas. The clean detached BTree profile is now frozen from `d13d1f92`:
> artifact v39 decides 162/162 (88 SAT, 74 UNSAT), agrees with the manifest and
> in-process Z3 on 162/162, replays every SAT model, and passes all per-instance
> memo invariants. Its aggregate memo accounts for 24,470 occupied/source terms,
> 656,638 payload literals, 5,938,264 conservative logical bytes, and 162
> deterministic structure-digest samples. The independent analysis accepts it;
> artifact/analysis SHA-256 values are `d8258399...b39f5` and
> `205bdfcf...4f25`. The isolated dense implementation is now committed at
> `2c9209fe`, and its clean detached profile passes the exact structural gate:
> all 162 rows preserve outcomes, replay, every neutral memo counter, and both
> ordered structure digests. Conservative logical memo bytes fall
> 5,938,264 -> 5,840,384 (-1.65%), below the preregistered 110% ceiling; the
> fail-closed analysis sets `timing_authorized=true`. Candidate artifact/analysis
> hashes are `e4db458f...f0eac` and `dbb2d65c...56256`. The registered six
> order-balanced unprofiled pairs are now complete. The runner and analyzer pin
> both source revisions, both prebuilt binary hashes, the exact
> `B,C,C,B,B,C,C,B,B,C,C,B` schedule, all structural/correctness gates, paired
> exhaustive-bootstrap bounds, family tails, CV, cold total, and per-pair RSS
> limits. All correctness, structure, point-estimate, family, cold-total, and RSS
> gates pass: bit-blast paired geometric mean is 0.9222 with bootstrap upper
> 0.9774; cold total is 0.9927 with upper 1.0183; maximum paired RSS is 1.0052.
> The candidate nevertheless fails the frozen variance gate: baseline
> bit-blast CV is 3.0023% and candidate CV is 6.8664%, both above 3%. The
> favorable point estimate cannot rescue that preregistered failure. ADR-0300
> is therefore a closed negative result, production is restored to the BTree
> representation, and the exact 12-run artifacts are retained. Do not rerun to
> select a quieter sample or reopen the same mechanism. Clause storage, scratch
> reuse, reverse traversal, and capacity hints remain closed; interning and
> packed-literal ideas require
> separate ADRs. This is bounded cold engineering, not a performance headline.
> Full ranked context:
> [`cold-path-datastructure-candidates.md`](docs/research/08-planning/cold-path-datastructure-candidates.md).

> **Glaurung publication-evidence reset (2026-07-17, ADR-0213).** The reviewer
> checklist confirms that the integration evidence is correctness-strong but
> not yet sufficient for headline performance claims. Strict typed translation
> and the three consumer soundness defects it exposed are the lead result.
> Before another paper speedup, add per-query paired fixed-work statistics with
> decided-population and warm/fallback partitions, a topology-equivalent warm
> Z3 control plus a neutral solver, and authoritative finding parity with
> canonical model selection where required. Existing exact-work/replay/RSS/CV
> gates remain mandatory engineering admission controls; they are not
> confidence intervals. GQ5 remains the leading pure-solver optimization lane,
> but its next candidate follows the paired measurement harness. ADR-0214 now
> lands that mechanism: Glaurung emits both outcome classes and a named Axeyum
> execution population per check, while Axeyum performs fail-closed N>=5
> both-decided geomean/bootstrap/quantile/CDF analysis. A clean three-cell
> DptfDevGen sweep exercises that path end to end. ADR-0215 then closes the
> topology-equivalent mechanism and first clean control: five v2 traces time
> `{Z3, Axeyum} x {cold, warm}` on the same 561-check stream with no fallback or
> nondecision. Fair warm Z3/Axeyum is 0.7875x [0.6893, 0.8977], so Axeyum is
> about 1.27x slower on this easy driver; the old 7.0678x cold-Z3/warm-Axeyum
> alias is explicitly not a solver headline. GQ5 may resume. A neutral baseline,
> harder timeout-sensitive marked sweep, finding parity, and the remaining
> publication gates are open.

> **Ranked review consolidation (2026-07-17).** The fair controls retire a
> blanket "Axeyum is faster" thesis. The paper spine is now **correctness +
> deployability + a rigorously characterized performance regime**. ADR-0217's
> completed small-driver experiment finds decisive warm Axeyum wins on IntcSST
> and SurfacePen, parity on vwififlt, and the earlier Z3 win on Dptf. The next
> experiment is causal feature attribution: cold results also split, so fixed
> FFI cost versus formula hardness remains a hypothesis rather than a finding.
> In parallel, promote the consumer bugs into a standing
> well-typed multi-oracle fuzzer, add cvc5/Bitwuzla as correctness and cold
> performance controls, and close authoritative finding parity. Enforce the
> already-tested `qfbv` profile in real consumers and measure WASM/RSS/proof
> deployment before making footprint claims. Large solver-module/API
> restructuring, table-driven reconstruction cleanup, and typed policy/config
> consolidation remain important artifact work, but must be staged behind these
> publication blockers so broad refactors do not invalidate the active evidence
> baseline. ADR-0216 completes the first artifact correction: `qfbv` is now the
> solver default, every full in-tree consumer opts in explicitly, Glaurung's
> production backend is QF_BV-only with its reference text bridge quarantined,
> and `axeyum-wasm` is a tested workspace member with a real wasm32 CI build.
> The browser binding keeps its SMT-LIB JSON API through a narrow QF_BV route;
> its parser dependencies mean bundle size and latency still require
> measurement rather than a blanket minimum-footprint claim.
> ADR-0217 completes the named small-driver fair map. Five fixed-work runs per
> driver preserve every four-cell decision with no fallback: warm Axeyum beats
> warm Z3 on IntcSST (1.5315x [1.4512, 1.6167]) and SurfacePen (1.5584x
> [1.5069, 1.6096]), while vwififlt is parity (1.0030x [0.9731, 1.0350]).
> Together with Dptf's Z3 win, this proves a workload-dependent Axeyum-winning
> regime but rejects a blanket speed claim. Because the cold cells split too,
> the data do not yet justify calling the cause merely small-formula FFI cost.
> This selects a feature join before the neutral and timeout-sensitive
> controls rather than a preselected size-based explanation.
> ADR-0218 completes the trace-available half of that join over 9,526 stable
> occurrences. Formula size alone does not explain the reversal. All four
> drivers favor Axeyum on SAT checks; UNSAT ranges from 0.3324x on Dptf to
> 2.0382x on SurfacePen. Purpose and query-reuse composition are material, and
> IntcSST/SurfacePen retain 1.4763x/1.4883x Axeyum wins after excluding session
> creation. Marginal reweighting is descriptive, not causal. Add per-check
> rewrite/AIG/CNF/SAT work and timing next, then compare matched
> outcome/purpose/reuse strata.
> ADR-0219 completes that internal diagnostic join. Retention removes 98--99%
> of cold per-check AIG/CNF construction and makes SAT the largest Axeyum phase
> on all four drivers (48--70%). Dptf's losing UNSAT stratum still adds the
> most warm structure (148 AIG nodes/258 clauses per check) and spends
> 36.6%/51.9% in CNF/SAT. The next mechanism control is repeated identical
> retained Dptf UNSAT CNF across Axeyum, Z3, and a neutral solver, without
> synchronous profile output; do not resume broad construction tuning from
> cold shares.
> ADR-0220 completes the fresh exact-CNF control: all 244 Dptf UNSAT snapshots
> agree across BatSat, the proof core, Z3 Boolean, and Kissat. The proof core is
> 2.627x faster than BatSat before checking; proof+self-recheck is near BatSat
> by geometric ratio. Fresh Z3 is much slower on the same CNF, so the warm Z3
> reversal is not a simple intrinsic-core result. Next replay the ordered clause
> stream through matched persistent cores; neutral end-to-end SMT remains open.
> ADR-0221 completes that ordered control without the invalid UNSAT-only
> shortcut. The 561 decisions contain 130 replay-cache hits and 431 actual core
> calls; five complete per-path replays preserve every SAT/UNSAT verdict.
> Retained BatSat beats retained Z3 Boolean by a 3.5527x per-call solve
> geomean on Axeyum's CNF, so Dptf's native warm-Z3 win is not evidence for a
> faster Z3 Boolean core or for prioritizing a custom SAT rewrite. The causal
> boundary is now word-level representation/integration. Add a neutral
> end-to-end SMT cell next, then the timeout-sensitive and finding-authoritative
> gates; multi-oracle fuzzing remains the parallel correctness blocker.
> ADR-0222 adds the first neutral word-level point without pretending an
> external protocol is an in-process warm cell. One cvc5 1.3.4 process replays
> the exact 561-check Dptf stream with a full reset per query and model output
> enabled. All 317 SAT / 244 UNSAT verdicts and 206 SAT value responses agree
> over N=5; the 2.593056-second batch median has 0.4222% CV. This closes a
> neutral Dptf oracle and cold-reset external-SMT point, not the remaining warm
> representation mechanism. Widen the same replay across the three accepted
> small-driver traces, then pursue a neutral in-process/topology-equivalent
> cell; timeout, finding parity, and standing multi-oracle fuzz remain open.
> ADR-0223 completes that breadth: cvc5 agrees on all 9,526 checks across Dptf,
> vwififlt, IntcSST, and SurfacePen (6,801 SAT / 2,725 UNSAT / 0 Unknown), with
> exact model-output counts, byte-stable output, and 0.16--0.42% timing CV.
> cvc5's per-check difficulty ordering does not mirror the Axeyum/Z3 warm map,
> further rejecting a universal formula-size or FFI explanation. Neutral
> cold-reset breadth is done; a topology-equivalent neutral cell remains open,
> while correctness priority returns to the standing typed multi-oracle fuzzer.
> ADR-0224 completes the first standing fuzz tranche without conflating
> consumer-state bugs with valid-formula semantics. All 4,000 deterministic
> QF_BV rows agree between Axeyum and direct Z3; all 1,487 Axeyum SAT models
> replay on the original IR; and a fixed 250-row cvc5 sample decides and agrees
> three ways with zero skips. Named strict-negative concat/extension/constant
> controls, legitimate empty-SAT versus model-less-UNSAT behavior, normalized
> width controls, and the linked-adapter W128 case are permanent. Fail-closed
> oracle accounting also found and fixed a nonstandard `!=` fuzz renderer that
> the old coarse skip bucket hid. Continue with additional fixed-seed/coverage
> rounds and proof-coverage measurement; do not claim well-typed fuzz alone
> tests Glaurung's invalid post-UNSAT exploration state.
> ADR-0225 completes the exhaustive-neutral continuation for this seed round:
> all 4,000 formulas decide and agree in Axeyum, direct Z3, and cvc5, with zero
> oracle/process/parser skip. The generator now fails unless it covers all five
> declared random widths and all 35 required operator classes. Routine CI keeps
> the 250-row cvc5 sample; the publication command explicitly sets stride one.
> Next correctness work must add independent seeds/edge-case frequencies, a
> proof-coverage denominator, or another neutral implementation—not rerun the
> same bounded formulas and call that new coverage.
> ADR-0237 now preregisters that independent continuation before full results:
> untouched `uniform-v1` ranges at 1,000,000..1,004,000 and
> 2,000,000..2,004,000 plus an `edge-v1` range at
> 3,000,000..3,004,000. All 12,000 rows must decide and agree across Axeyum,
> direct Z3, cvc5 1.3.4, and Bitwuzla 0.9.1; every Axeyum SAT must replay, and
> the edge round must report nonzero frequencies for all 14 declared semantic
> corners. The 256-row engineering pilot is excluded. Run and retain this exact
> campaign next; do not change seeds in response to its outcomes. The first
> full attempt did fail closed after 3,999 `uniform-a` agreements when seed
> 1,002,261 exceeded an unstated inherited 5-second Axeyum worker cap. Preserve
> that attempt. The amended committed protocol leaves every seed unchanged,
> names a 30-second cap under which the seed decides, records exact nondecision
> seeds/reproducers, and asserts all-decided directly before the full rerun. The
> second attempt completed `uniform-a` 4,000/4,000, then failed closed at
> `uniform-b` seed 2,003,009 because cvc5 exhausted the inherited 2-second
> external limit. Its exact script decides `sat` in cvc5/Bitwuzla under 30
> seconds. Preserve that attempt too; the next committed rerun applies and
> records 30 seconds for every engine, with every formula and seed unchanged.
> That third attempt closes both uniform rounds, then retains `edge-c` seed
> 3,000,881 after Axeyum exceeds 120 seconds. The unchanged formula is UNSAT in
> all four engines under 600 seconds (isolated Z3 25.225 s, cvc5 41.67 s,
> Bitwuzla 12.62 s; Axeyum between 120 and 600 s). The final committed rerun
> uses the same 600-second correctness cap for all engines. Do not reuse this
> hard-seed diagnostic as comparative timing evidence.
> The final same-commit run is accepted: all 12,000 formulas decide and agree
> four ways, all 4,471 Axeyum SAT models replay, and the edge round observes all
> 14 declared semantic-corner families. Unknown, timeout, crash, external
> failure, replay-indeterminate, and disagreement counts are all zero. This
> closes independent seeds, edge-frequency accounting, and the second neutral
> implementation; it remains a bounded correctness result, not completeness or
> performance evidence.
> ADR-0238 accepts the preregistered authority control without changing its
> exact tcpip prefix, source/input identities, work
> bounds, and N=3 order-balanced protocol, it adds a greatest-unsigned model
> policy beside the accepted least-unsigned policy and measures their finding
> set union under sole Z3 and sole Axeyum authority. Acceptance requires exact
> reproduction of the rejected arbitrary-model and accepted least-model
> controls, per-policy ordered-output/counter/telemetry parity, and identical
> extremal unions. All gates pass. Maximum produces 84 identical findings and
> the least/greatest union contains 125: 69 common, 41 least-only, and 15
> greatest-only. Against the arbitrary-model combined union, 95 rows are
> shared, 33 are arbitrary-only, and 30 are extremal-only. This establishes a
> bounded deterministic ensemble with authority parity, while directly
> rejecting an exhaustive-coverage or finding-preservation claim. Next widen
> fixed work or add genuinely broader deterministic model exploration.
> ADR-0239 accepts the latter after preregistration. Two
> complementary site-hash policies select min/max from only the fixed choice
> purpose and instruction address, excluding solver models, expression IDs,
> mutable counters, and process order. Combined with global minimum/maximum,
> they form a four-schedule ensemble on ADR-0238's exact source/input/work
> boundary. Acceptance requires exact reproduction of all three prior controls,
> per-policy output/work/telemetry parity, and an identical four-policy union;
> union growth and recovery of the 33 arbitrary-only rows were explicitly not
> preselected. The first exact attempt reproduced the rejected arbitrary-model
> and all six minimum controls, then failed closed when a concurrent tracked
> planning-document edit changed Axeyum source identity; maximum and both site
> schedules were never observed. That inadmissible attempt is preserved; the
> unchanged committed campaign was rerun from detached preregistration commit
> `57ee6720`. Every gate passes: site-hash-zero and site-hash-one produce 95 and
> 98 identical findings; their addition grows the two-extremum union from 125
> to 128, but recovers none of the 33 arbitrary-only rows. Preserve the bounded
> parity result without claiming preservation.
> The cross-repository Pareto strategy now makes the next boundary explicit:
> concretization value selection is one pluggable policy knob, not a sequence of
> new algorithms. Glaurung A0 is implemented and accepted on isolated branch
> `axeyum-concretization-policy-a0` at `07ea0c1`: one public
> `ConcretizationPolicy` covers `concretize_addr` and `eval_concrete`, and its
> `AnyModel` default exactly reproduces all three accepted pre-A0 Axeyum controls
> (126 raw diagnostics, 2,991 solves, and ordered hash
> `a67d7bca28602ab20bbc46d9a5d42705463bd340067dc8e6ec660b35d58ba265`).
> ADR-0240 then corrects the finding baseline at Glaurung `845239f`: exact trace
> inspection shows the two Z3-only tcpip rows are generic-`Arg0` internal-tree
> diagnostics laundered to `*attacker` by uninitialized-load propagation. After
> preserving exact provenance they become `**Arg0`; both authorities have zero
> high-confidence findings on the first-15-function slice. The isolated branch
> head is `b79f269` after the confidence protocol and WDM SystemBuffer-model
> corrections. Integrate that clean branch after coordination with the active
> Glaurung owner; do not reimplement
> A0. Treat AnyModel, least/greatest, and the two site-hash choices plus
> deterministic work bounds as configurations to sweep under one harness, but
> select a nonzero
> labeled-positive corpus and report raw/confidence/validated partitions before
> setting recall gates. Those are the five executable scalar-policy cells at
> `b79f269`; preregister them rather than claiming unimplemented coverage.
> `BoundarySet`/`DiverseEnum` remain later settings of the same A0 knob, not new
> algorithms, but require bounded multi-successor explorer mechanics before they
> are runnable and must not be simulated by choosing one boundary. Only begin
> deferred symbolic memory if that cheap,
> corrected sweep leaves validated coverage headroom; symbolic memory changes
> the memory model and is the sole architectural item in Pillar A.
> ADR-0241 makes that partition executable. Glaurung `931d8a8` emits an opt-in,
> exhaustive `glaurung-ioctlance-confidence-v1` classification without changing
> legacy finding bytes; Axeyum's v5 authority harness records raw,
> high-confidence, and diagnostic sets from the same process and fails closed
> when high-confidence acceptance lacks the producer partition. Rebaselining all
> five existing tcpip settings leaves 0/0 high-confidence rows in every cell and
> classifies the former 33 AnyModel-only remainder as diagnostic `Arg0`/`Arg1`
> ancestry. ADR-0242 independently rejects the apparent complete x64
> `usbprint.sys` target: all five producer-high-confidence rows came from
> treating the I/O-manager-owned `METHOD_BUFFERED` SystemBuffer pointer as a
> free attacker address. Glaurung `b79f269` separates fixed pointer ownership
> from tainted buffer contents; the same complete N=2 control is now accepted at
> 0/0 high-confidence rows and 16,537 solves per process. Usbprint is retired as
> a recall denominator. ADR-0243 closes the missing nonzero positive-control
> gate without undoing that correction: direct source and machine-code review
> defines 14 finding rows at 12 sites across nine planted IOCTLance fixtures,
> and a fail-closed join verifies all 18 source/binary paths plus exact N=2 sole-
> authority parity at 14/14. This is a regression denominator, not real-world
> recall or evidence that a policy improves discovery. Preregister the
> configuration sweep with 14/14 as a hard control and keep policy-dependent
> real-driver rows unlabeled until independently validated; producer confidence
> remains a partition, not ground truth.
> ADR-0244 now preregisters the exact corrected sweep before observing its new
> cells. It fixes five executable policies in order (AnyModel, minimum, maximum,
> site-hash-zero, site-hash-one), Glaurung `b79f269`, both authority binary
> hashes, 11 driver inputs, and three N=2 fixed-work strata. The nine-fixture
> stratum must remain exactly 14/14; tcpip-prefix-15 and complete usbprint are
> separately retained as unlabeled discovery populations with no direction or
> magnitude gate. The runner refuses overwrite and the analyzer rejects source,
> environment, policy, telemetry, work, coverage, partition, cost, or report-
> hash drift. Commit this protocol, run it from that clean detached Axeyum
> revision against the clean isolated Glaurung branch, and preserve any partial
> failed attempt without adapting the remaining matrix. BoundarySet/DiverseEnum
> remain future cells after bounded successor forking; symbolic memory remains
> conditional on a validated residual gap.
> The exact `234c6678` run rejects ADR-0244 v1 at the intended fail-closed
> boundary. AnyModel passes all three strata and 14/14 validation. Minimum also
> preserves 14/14 and exact tcpip high/raw/work parity, but raises positive-
> control work from 2,322 to 60,064 solves and tcpip work to 80,563 solves per
> authority/repetition. All four minimum/complete-usbprint processes hit the
> declared 300-second wall deadline, so the runner preserves the rejected cell
> and never observes maximum/site policies. Do not raise that deadline or count
> usbprint as zero. ADR-0245 preregisters v2 with all five policies unchanged
> over the validated positive and tcpip fixed-work strata; complete usbprint is
> now a separately tracked policy-resource frontier that needs its own bounded-
> function/work preregistration. The exact clean-detached `e11a2157` v2 run
> clears AnyModel and minimum, then fails closed at maximum's positive-control
> validation. Maximum retains every expected row (14/14 recall) but adds one
> source-rejected high-confidence `stack-overflow` at the arbitrary-pointer
> `RtlCopyMemory` in `test_physical_memory.sys` (14/15 precision). Both
> authorities and repetitions reproduce it. Glaurung `b79f269` derives “stack”
> from policy-chosen `dst`/`rsp` values landing within +/-64 KiB, so maximum can
> manufacture a semantic region label from accidental concrete proximity. The
> site-hash cells remain unobserved. Prioritize a model-independent stack-region
> predicate and regression first; only then preregister the corrected full
> scalar sweep. Do not advance symbolic memory from this classifier artifact.
> ADR-0246 now closes that prerequisite on the isolated Glaurung branch. Two
> deliberately retained candidates first removed the false row but missed the
> genuine `[rbp-0x70]` stack sink because the real executor uses a constant-base
> expression DAG with no free stack symbol. Glaurung `0581f57` adds non-leaf
> DAG ancestry; the exact N=2 maximum control returns to 14/14 with precision
> and recall 1.0, zero unexpected high-confidence rows, and exact authority
> parity. The final documented clean tree is `7f682e5`, whose dual-backend
> library suite passes 992/994 with only the two unchanged baseline WinAPI
> rendering failures. ADR-0247's exact clean-detached `f2af8b40` v3 run is now
> accepted at that revision with rebuilt authority hashes and the unchanged
> positive/tcpip work bounds. All five policies preserve the exact 14-row set
> with precision/recall 1.0 and zero unexpected high rows. Deterministic tcpip
> diagnostics vary from 84 to 110 with exact authority parity; AnyModel remains
> 128 Z3 / 126 Axeyum, and every tcpip row is producer-diagnostic. Policy work
> varies materially (2,991--80,563 solves on tcpip; site-hash-one reaches about
> 264 seconds / 235 MiB under Axeyum). This closes the scalar sweep without
> demonstrating validated coverage headroom. Keep symbolic memory deferred;
> next preregister independent source adjudication of policy-varying real-driver
> output or add a real labeled population capable of measuring misses.
> ADR-0248 takes the strongest immediately available version of that next step:
> the source-backed positive population's complete five-policy difference is
> only 54 rows at 43 sites across seven drivers, so it freezes all of them with
> no sampling. The completed fail-closed review re-reads every source range and
> instruction from 14 clean, hash-exact IOCTLance files: 30 rows are ordinary
> fixed IRP/request plumbing and 24 are duplicate presentations of already
> validated sinks. Zero are independent primitives and zero are indeterminate.
> No scalar policy has a validated finding difference or residual coverage gap.
> This closes the cheap A0 evidence lane without selecting a new default. Keep
> symbolic-address memory gated off; only genuinely broader labeled evidence
> can reopen that one architectural project. BoundarySet/DiverseEnum remain
> settings of the same A0 surface, not follow-on research programs.
> ADR-0249's exact clean-detached `f9511525` run now rejects at its protocol
> gate after executing all 15 cells. Fourteen cells complete, all five policies
> establish a common prefix of 10, and four complete prefix 15; the final
> prefix-15/site-hash-one cell has identical 91/0 raw/high output across both
> authorities and repetitions but Axeyum canonical work drifts from
> 522,032 solves / 7,951 attempts to 522,296 / 7,955. This is not the
> preregistered exact four-run resource bracket, so the aggregate records no
> resource bound and remains rejected. Post-result-only Glaurung instrumentation
> at isolated candidate `ff3c0a7` attributes the drift to a concealed inner
> symbolic-worklist wall deadline: 40 worklists partition as 36 complete, three
> state-budget stops, and one deadline stop, while the same 91 diagnostics and
> zero high-confidence rows remain. Outer analyzed-function count is therefore
> not a sufficient fixed-work boundary. Preserve the rejected artifact; future
> evidence must require explicit exploration-stop telemetry and zero deadline/
> timeout stops rather than adapting ADR-0249's observed bounds. This result
> makes no solver-speed or recall claim and does not reopen symbolic memory.
> ADR-0250 implements that next fail-closed boundary in Axeyum's authoritative-
> finding harness. Opt-in `--require-deterministic-worklists` requires exactly
> one machine-readable exploration-stop partition per process, checks that all
> stop classes sum to the worklist count, rejects any deadline/timeout stop,
> and requires the complete partition to reproduce within each backend. These
> required reports advance to schema v6; historical/default v5 invocations stay
> stable and cannot be retroactively relabeled. The parser accepts the real
> one-function Dptf footer from isolated Glaurung candidate `ff3c0a7`, and all
> 26 focused producer tests pass. The source-backed finding-population validator
> independently rechecks every v6 run rather than trusting the summary; its
> eight tests pass. Coordinate that candidate with the Glaurung owner
> before any full v6 campaign; do not edit the live dirty checkout. This closes
> the harness-side dropped-work gap but does not rehabilitate ADR-0249 or reopen
> symbolic memory. Resume publication work with wider corrected real proof
> manifests or a genuinely broader labeled population, not another policy-
> tuning cell.
> ADR-0226 adds the first explicit proof denominator. Of 2,513 generated UNSAT
> rows, a predeclared width<=8/seed-divisible-by-4 subset selects 169 (6.725030%):
> all 169 carry independently rechecked CNF DRAT and end-to-end
> faithfulness-plus-DRAT certificates. The other 2,344 are unmeasured, not
> failures. A complete width<=8 diagnostic isolates seed 83: CNF DRAT rechecks,
> but end-to-end certification has no cooperative deadline and exceeds a
> 15-second process bound. Add deadline/process isolation before widening this
> denominator, then measure proof coverage on real Glaurung UNSAT rows.
> ADR-0227 closes the first WebAssembly deployability measurement and fixes a
> build-only blind spot discovered by executing it. The pre-fix wasm32 artifact
> compiled but trapped on its first solve because the AIG hash fold retained a
> 64-bit value before converting to 32-bit `usize`; the repaired CI now
> instantiates generated glue and executes SAT/UNSAT. Stable release evidence
> reports a 1,801,662-byte browser runtime (541,248-byte sum under `gzip -9`)
> and real Node/Chromium small-query latency in the 13--71 microsecond range.
> This establishes an executable pure-Rust QF_BV browser artifact, not native
> parity or minimum total footprint: the shared parser still pulls FP/string
> crates. Next deployability work is the warm time/RSS Pareto and real-query
> proof denominator; a narrower parser surface is a measured size candidate.
> ADR-0228 closes cold-path/warm-hit/RSS honesty on two current, matched
> deployment controls without corrupting the four-cell claim shape. Dptf and
> SurfacePen preserve every Z3-authoritative verdict and finding count across
> five order-balanced one-shot/adaptive processes. Adaptive cumulative Axeyum
> work falls by 6.829x/5.465x while paired median RSS rises 25.58%/14.77%; the
> latter is the clean SurfacePen result, while Dptf one-shot RSS has 9.20% CV.
> Retained-owner hits are 98.75%/98.31% and fallback is zero, so the paper must
> name this as a high-reuse policy Pareto, not a per-query solver speedup or an
> owner-churn result. Real-query proof coverage and timeout-sensitive/wider
> finding-authority coverage remain ahead of optional four-driver RSS widening.
> ADR-0229 closes authoritative finding parity for the current bounded
> four-driver tier. Separate sole-authority binaries emit the same 302 raw
> sinks byte for byte across three order-balanced repetitions each (24
> processes, 1,812 stable output rows). Dptf and SurfacePen also preserve solve
> counts; Axeyum reaches the same vwififlt/IntcSST output with 8/4 fewer solve
> calls, so this is exact user-visible output parity rather than an identical
> exploration claim. No canonical model policy is justified on this tier.
> Keep timeout-sensitive/wider authority parity open, and do not reuse the
> standalone authority timers as fair four-cell performance evidence.
> ADR-0230 closes the first real-query proof deployment denominator. The
> complete 128-query representative Glaurung manifest decides 64 SAT/64 UNSAT
> with 128/128 Z3 and manifest agreement; all SAT models replay, and all 64
> UNSAT rows carry independently rechecked inline CNF DRAT with zero missing.
> This is the concrete client proof use case requested by review, but it is not
> term-to-CNF faithfulness: keep it separate from ADR-0226's 169-row generated
> end-to-end denominator. Next proof work is deadline-aware faithfulness on real
> rows and wider captured manifests, not relabeling proof-core timings as fair
> solver performance.
> ADR-0231 removes the generated denominator's indefinite proof-search block.
> A public bounded miter/composed API maps expiry only to
> `Inconclusive`/`NotCertified`, and the standing harness records exact seeds.
> The complete width<=8 cohort selects 1,505/2,513 generated UNSAT
> (59.888579%): CNF DRAT rechecks for all 1,505, while 1,487 stronger
> faithfulness-plus-DRAT certificates recheck (98.803987%) and 18 remain
> uncovered under 100 ms. Keep those 18 in the denominator. The remaining
> deadline work is whole-certificate process isolation and real-query
> faithfulness, not excluding slow rows or claiming a hard 100 ms API wall.
> ADR-0232 closes the accepted four-driver neutral-warm control without
> conflating an external SMT stream with an in-process API. cvc5 follows the
> exact source owner, identity-derived persistent-prefix LCP, and temporary
> assumption partition over all 9,526 checks. N=5 preserves 6,801 SAT / 2,725
> UNSAT / 0 Unknown with byte-stable output and 0.28--1.61% CV. Within the same
> external protocol, retained medians are 16.4x--57.0x below the accepted
> full-reset totals; this proves session/representation retention is a
> first-order mechanism, not a cross-solver speed ranking. Continue with
> timeout-sensitive neutral/authority tiers, real-query faithfulness,
> independent fuzz seeds and another neutral implementation, and
> whole-certificate process isolation.
> ADR-0233 closes the timeout-sensitive neutral **formula** control. Artifact
> v32 now runs in-process Z3 even after an Axeyum `unknown` and accounts for
> both-decided, Axeyum-only, Z3-only, and neither on every query. Five clean
> repetitions over the exact 52-formula tcpip frontier at 50/100/250/1000 ms
> have zero error, replay failure, decided disagreement, or three-solver
> SAT/UNSAT contradiction. Decision coverage converges from Axeyum/Z3/cvc5
> 28/13/46 to 52/52/52; the all-decided 1000 ms paired Axeyum/Z3 geomean is
> 0.21095 [0.14904, 0.29644], establishing a cold one-shot Axeyum-winning
> formula regime without reviving a retained-warm headline. Wider/timeout-
> sensitive sole-authority findings remain open, as do real-query
> faithfulness, independent fuzz seeds plus another neutral implementation,
> and whole-certificate process isolation.
> ADR-0234 closes representative real-query term-to-CNF faithfulness. Artifact
> v33 attempts every primary UNSAT in ADR-0187's corrected 162-query manifest
> and independently rechecks both stored certificate texts. Two clean,
> identity-matched repetitions decide 88 SAT / 74 UNSAT, replay every SAT
> model, recheck all 74 CNF DRAT proofs, and certify all 74 UNSAT end to end
> under a declared 1000 ms cooperative proof-search deadline, with zero
> non-certification or alarm row. This is a 74-row representative denominator,
> not the full corpus or a hard one-second API guarantee. Next proof work is
> killable whole-certificate process isolation and wider real manifests;
> independent fuzz seeds/another neutral implementation and timeout-sensitive
> or wider sole-authority findings remain publication work.
> ADR-0235 closes the representative denominator's whole-certificate
> isolation gap. Artifact v34 runs the same pinned executable as a
> source-hashed one-query worker whose parent wall covers parse, construction,
> both proof searches, and both completed-proof self-rechecks. Two clean runs
> again certify 74/74 UNSAT under a 1500 ms process wall; a separate 1 ms
> control retains all 74 rows as `not-certified` plus `hard_timeout`, with zero
> dropped row or alarm. The wall includes scheduler/poll/kill/reap overhead and
> is not a real-time OS guarantee. Next proof work is wider corrected real
> manifests, not more isolation plumbing; independent fuzz/another neutral
> implementation and timeout-sensitive or wider sole-authority findings remain
> publication work.
> ADR-0251 now preregisters that wider real-query proof population before any
> new query is observed. The 1,024-row `proof-holdout-v1` excludes all 162
> accepted representative hashes, then selects the lowest content hashes under
> fixed family/verdict quotas from the exact 30,628-query corrected full
> manifest. It contains 515 SAT / 509 UNSAT and adds every six remaining
> comparison/SAT rows; the combined evidence union will be 1,186 unique real
> queries with complete rare-stratum coverage. Run two clean CPU-3-pinned
> artifact-v34 processes under ADR-0235's unchanged 1000 ms cooperative / 1500
> ms killable-worker policy. Every row must decide and agree with both manifest
> and Z3; all SAT models must replay; all UNSAT CNF DRAT must recheck; every
> UNSAT must remain in the stronger certificate partition. Preserve
> `not-certified`/hard-timeout rows under the fixed policy rather than selecting
> finishers or adapting the bounds. This is a verdict-balanced correctness and
> deployability denominator, not prevalence or performance evidence.
> The first execution attempt is preserved as an ADR-0252 pre-execution
> rejection: the 1,024-row manifest was paired with the 30,628-file full root,
> and the benchmark correctly refused 29,604 unlisted files before reading a
> selected query. The exact reproduction exits 1 with byte-identical stderr and
> no artifact. ADR-0252 preregisters a tested materializer that verifies both
> fixed manifests, every exact selected full-manifest member, all source and
> copied query bytes, and an output root containing exactly the selected 1,024
> `.smt2` paths plus the byte-identical manifest. Commit that boundary before
> corrected execution; do not weaken membership validation or change any
> ADR-0251 selection, resource, repetition, or acceptance field.
> ADR-0253 executes that unchanged correction twice from clean detached commit
> `d8da4a45` and accepts the fail-closed join. Both runs decide all 1,024 rows,
> agree with both manifest and Z3, replay all 515 SAT models, and independently
> recheck CNF DRAT for all 509 UNSAT. The stronger process-isolated route
> certifies 508/509; the same `slice-partial` row hits the fixed 1,500 ms whole-
> worker wall in both runs and remains explicit `not-certified` coverage. The
> combined disjoint representative plus holdout denominator is 1,186 queries,
> 603 SAT replays, 583 CNF DRAT rechecks, and 582/583 stronger certificates.
> Treat this as correctness/deployability evidence only. Do not adapt the wall,
> drop the retained row, infer prevalence, or reopen symbolic memory.
> ADR-0254 begins the next independent-consumer boundary without widening the
> runtime TCB. The new `qfbv-proof-export` command emits a manifest-bound
> standard DIMACS/DRAT bundle only for a flat single-check `QF_BV` UNSAT whose
> text self-rechecks, and refuses scoped ambiguity, SAT/inconclusive outcomes,
> or overwrite. Before real export, ADR-0254 fixes the lowest content hash among
> the 509 holdout UNSAT rows and pins unchanged upstream `drat-trim` source,
> build command, binary hash, positive `s VERIFIED` gate, and a final-step-
> deletion teeth control. Keep access-controlled query/proof bytes out of Git;
> preserve hashes and exact checker evidence. This is interoperability, not a
> coverage or performance sample.
> ADR-0255 preserves the first observation without laundering its failed teeth
> gate. The fixed real query exports a self-rechecked 558-variable/2,166-clause
> CNF, two-byte DRAT, and LRAT; pinned `drat-trim` prints `s VERIFIED`. But the
> CNF is already UNSAT by input unit propagation, so deleting the only `0\n`
> proof line leaves an empty proof that the checker also verifies. Treat
> ADR-0254 as positive interoperability plus a rejected negative-control design.
> Before a corrected control is observed, ADR-0255 fixes the satisfiable DIMACS
> text `p cnf 1 0\n`, reuses the exact real proof unchanged, and requires no
> `s VERIFIED`. Preserve the v1 rejection beside any v2 result; this is a
> post-result checker sanity correction, not a stronger source-proof claim.
> ADR-0256 accepts that corrected bounded result. The unchanged real pair again
> makes pinned `drat-trim` exit zero with `s VERIFIED`; the same two-byte proof
> against preregistered satisfiable DIMACS `p cnf 1 0\n` exits one with
> `s NOT VERIFIED`. This closes one independent standard-format consumer cell
> and its checker-binding sanity control. Keep the limitation prominent: the
> real CNF is input-unit-refutable and its DRAT is only `0\n`, so this is not a
> nontrivial learned-clause-trace, coverage, lowering, or performance claim.
> ADR-0257 preregisters the optional nontrivial follow-on before observing any
> remaining proof shape. Scan at most the first 32 expected-UNSAT holdout rows
> after excluding `0015f5bd...`, in ascending content-hash order; retain every
> attempt. Select only the first DRAT longer than two bytes and one line whose
> real proof verifies externally while an empty proof over the same CNF does
> not. A capped `no-selection` is valid. This is transparent conditioned
> selection for clausal interoperability, never prevalence or performance.
> ADR-0258 retains the completed fixed-cap `no-selection`. All 32 hash-ordered
> exports succeed and self-recheck, but every DRAT is the same two-byte,
> one-line empty-clause proof; both the real and empty proof receive an exact
> `s VERIFIED` line from pinned `drat-trim`. Do not widen or keep mining this
> holdout. The honest claim remains one standard external-consumer cell with a
> separate checker sanity control, not a nontrivial learned-clause trace.
> ADR-0259 returns to the attachment's durable cold-path priority without
> guessing another optimization. Existing CNF timing does not partition
> literal canonicalization from fingerprint-index work, and ADR-0200's direct
> map replacement regressed. Before implementation or real observation, add an
> opt-in, production-zero-overhead detailed profile and bind one clean raw run
> to the accepted 162-query corrected-wide-v3 representative. Require exact
> canonicalization/index invariants and complete verdict/replay identity;
> profiled timing is diagnostic only. Artifact v35 now implements that boundary:
> a zero-sized ordinary profiler and separate counter-carrying monomorph feed
> typed solver stats, per-instance/corpus JSON, and an independent fail-closed
> analyzer that re-sums every row and emits exact family partitions. The 302
> CNF, 880 solver, and 42 bench tests plus strict targeted Clippy pass. The
> clean detached run now accepts all 162 decisions/oracle/replay gates and all
> six identities. Of 391,251 non-tautological attempts, 119,260 (30.4817%) are
> exact duplicates; every one is a primary exact hit, while collision work,
> repeated literals, and complementary tautologies are zero. Slice-partial
> owns 73.4572% of duplicates and register-slice 26.0230%. Counts are not time,
> so ADR-0259 selects no optimization. ADR-0260 preregisters profile-only
> first-origin/duplicate-origin attribution on the same population before any
> generator-elision experiment. Artifact v36 now implements that boundary with
> stable emission sites, actual first-clause provenance through collision
> buckets, same/cross-owner cells, exact length/literal partitions, and an
> independent analyzer that computes the preregistered 50% / 10-query / 50%
> selection gate. The disabled store remains zero-sized. All 304 CNF, 880
> solver, 43 bench, and five analyzer tests plus strict targeted Clippy pass.
> Commit `1bce10fd` preserved that implementation unobserved. Its clean detached
> fixed-population run accepts all 162 decision/oracle/replay and construction-
> identity gates. Exactly one cell passes the preregistered rule: same-owner
> `root/and_tree/forward/parity` accounts for 107,000 duplicates (89.7199%)
> across 29 queries, with the largest query contributing only 9.9738%. All are
> binary, corresponding to 53,500 redundant two-clause private parity-leaf
> encodings. ADR-0260 still selects no production optimization; ADR-0261
> separately preregisters the sole selected experiment, same-owner positive-
> root private-parity-leaf elision, with exact structural and repeated
> unprofiled end-to-end timing gates. Candidate `8b95d42a` passes its local
> tests and every 162-query correctness/shape gate, but changes clause attempts,
> duplicates, and canonical attempted literals by exactly zero instead of the
> required -107,000 / -107,000 / -214,000. The independent analysis is byte-
> identical to ADR-0260. Reject and remove the no-op candidate without running
> timing: equal same-owner parity-origin clauses did not imply identical
> normalized parity leaves. Close this origin lane unless a new preregistered
> leaf-shape/clause-overlap diagnostic supplies a different mechanism.
> ADR-0262 accepts the exact wider tcpip authority matrix: first 20 of 338
> reachable functions, `{AnyModel, LeastUnsigned} x {100, 250, 1000 ms}`, six
> N=3 order-balanced cells. All 36 processes pass exact identity, stable
> findings/work, zero-high-confidence parity, complete policy telemetry, and
> ADR-0250's v6 stop gate. Timeout changes no ordered finding hash or work
> counter. AnyModel remains raw-divergent at 211 Z3 / 209 Axeyum with 11/9
> backend-only rows; LeastUnsigned is exactly 185/185 at all timeouts but costs
> 96,075 solves per process and about 94 s Z3 / 169 s Axeyum authority time.
> Only 147 rows overlap between the 220-row AnyModel union and 185-row canonical
> set, so canonical parity is not finding preservation. This closes the wider
> tcpip timeout-sensitive sole-authority tier; prioritize genuinely broader
> labels and A1 resource-config wiring rather than more unlabeled tcpip cells.
> ADR-0236 closes the first measured canonical-authority cell after tcpip
> activates ADR-0229's reopen condition. On the same current source, binaries,
> first 15 functions, 250 ms check wall, and N=3 order-balanced repetitions,
> unrestricted model choice is stable but differs by two Z3-only raw sinks. The
> opt-in `glaurung-min-unsigned-v1` policy instead gives 110 byte-identical
> sinks, 80,563 solves, and identical complete model-choice telemetry under
> both authorities, with zero inconclusive choice. Canonicalization changes the
> common raw population from 126 to 110, so it remains a reproducible
> experiment policy rather than a production default or a finding-preservation
> claim. ADR-0238 subsequently accepts exact least/greatest union parity but
> retains 33 arbitrary-model-only rows, so wider authority and genuinely
> broader model exploration remain publication work; the standalone canonical
> timers are not performance evidence.

> **Concretization finding baseline corrected (2026-07-18, ADR-0240).** The
> authority-parity work (ADR-0229/0236/0238/0239) remains valid raw determinism
> evidence, but raw sink count is not finding ground truth. Exact PDB,
> disassembly, and ordered-trace inspection classifies tcpip's two Z3-only rows
> at `0x1c000830d`/`0x1c000832e` as internal
> `TcpSendTrackerMarkTransmits` traversal diagnostics derived from generic
> `Arg0`. Glaurung had discarded that provenance on uninitialized loads and
> replaced it with `*attacker`, bypassing its own confidence filter. The TDD fix
> on isolated branch `axeyum-concretization-policy-a0` at `845239f` preserves
> every source label. AnyModel still yields 128 Z3 versus 126 Axeyum raw rows,
> now labeled `**Arg0`; least unsigned still yields exact 110/110 raw parity;
> both policies have zero high-confidence findings on this 15-function slice.
> Therefore do not require BoundarySet/DiverseEnum to recover or exceed the
> arbitrary-model raw union. ADR-0241 rebaselines all existing settings and
> classifies the 33 arbitrary-only rows as producer diagnostics. The corrected
> four-driver tier and a NETwtw10 prefix also have zero accepted rows. ADR-0242
> rejects usbprint's apparent five-versus-four population as a WDM
> environment-model defect: corrected Glaurung `b79f269` fixes the
> I/O-manager-owned SystemBuffer address while preserving content taint, and the
> complete N=2 rerun has 0/0 accepted rows with equal solve counts. ADR-0243
> establishes a separate source-backed planted positive control with 14/14
> exact rows across nine fixtures and zero unexpected producer-high output.
> Preregister recall/precision only on validated rows while
> publishing raw, confidence-gated, validated, work, and cost partitions. Phase
> 0/A0 remains the completed enabling refactor; Phase 2 remains a cheap policy
> sweep; symbolic memory remains the sole architectural item and begins only if
> corrected validated evidence leaves headroom.

> **P0 soundness stop contained (2026-07-15, ADR-0165).** Historical commit
> `2cb298e2` reproduced unrestricted large elimination from a two-constructor
> `Prop` combining with proof irrelevance to make the trusted
> `add_declaration` gate accept `theorem bad : False`. Commit `d26ad887`
> implements Lean's exact syntactic-subsingleton criterion, restricts every
> other potentially-`Prop` recursor to `Sort 0`, inverts the complete exploit,
> and adds positive/negative universe/field coverage. Commit `a10c8cde` pins
> Lean 4.30.0 and makes a real flat-inductive/iota compatibility test mandatory
> in CI rather than skip-as-success. The positive profile covers
> `False`/`True`/`And`/`Eq`/`Iff`, exact exposed indices, and an
> accessibility-style recursive proof field; full `Acc` remains behind the
> existing recursive-indexed deferral. Do not inflate this repaired class into
> a complete kernel-equivalence claim. Commit `de249d48` aligns downstream
> `Or.rec`/`Exists.rec` proof reconstruction with the restricted recursor
> universe arities. The complete serialized `just check` gate then passed under
> the 4 GiB wrapper: format, strict workspace Clippy, all workspace tests and
> doctests, warning-free docs, the pinned Glaurung regular corpus, foundational
> resources, generated dashboards, and link validation. Resume Glaurung GQ7 as
> the leading solver-performance lane while continuing broader
> parametric/indexed external-kernel hardening as a proof-assurance task.

> **Current sequencing (2026-07-15).** The P1.4 e-graph → P1.5 CDCL(T)
> keystone is landed, and the recovery audit has restored P2.6 through the
> checked ADR-0141 source-term Skolem boundary with explicit resource limits.
> The bounded public
> quantified-BV UNSAT slice now reconstructs **18/18** rows in Lean; continue
> the depth-first spine through broader nested/alternating QSAT and quantified-UF
> models while running the Glaurung QF_BV performance lane below as the next
> client-driven measured leaf. The byte-complete Glaurung capture is now
> regenerated and strictly ingested: 128 representative queries plus a 13,462-
> query well-typed full tier both decide at 100% with zero disagreements or
> replay failures. Artifact v27 removes the accidental observational bit-demand
> walk from production: representative raw/canonical medians are 1.65x/1.37x
> Z3, while full raw/canonical single trials are 3.17x/2.71x. Canonical v2 is a
> valid 13.3% full-tier production win, but CNF encoding is now the largest
> stage. ADR-0144's collision-safe ownership index then cuts canonical full CNF
> 18.5% and total time 8.8%, reaching 19.22 s / 2.47x Z3 without changing a
> clause or decision. ADR-0145 then removes temporary-vector expansion from
> 2.23 million recognized not-AND gates: full CNF falls another 5.6%, total
> falls 2.7% to 18.69 s, and the ratio reaches 2.40x with identical CNF content.
> The next action is not SAT tuning or broad partial lowering: inspect the
> remaining CNF root-emission allocation and planning work for the
> `register-slice` and `slice-partial` families. ADR-0146's reusable direct-root
> leaf scratch failed the representative gate (+1.1% total / +4.9% CNF) and is
> reverted/deferred. Profile planning next; do not retry root scratch without a
> design that avoids the second traversal entirely. ADR-0147 is the first
> planning experiment: zero-copy reverse traversal improves planning 2.5% but
> regresses total 0.5% / CNF 3.6%, so it too is reverted/deferred. Do not spend
> another slice on planning's micro-cost; return to shared gate/root clause
> normalization and allocation, where 53.75 million attempts provide leverage.
> ADR-0148's bounded formula+index capacity hint fails (+2.5% total / +10.0%
> CNF) because sparse pre-sizing slows gate lookup 23.5%; it is
> reverted/deferred. ADR-0149 isolates the contiguous formula-header vector and
> leaves exact-dedup growth unchanged, but it also fails: representative CNF
> median/mean regress 0.83%/0.67%, while the 0.16% total-median change is noise
> contradicted by a 0.07% mean regression. Ordinary vector growth is restored
> without a full run. Close the capacity-hint lane and re-attribute the shared
> clause-normalization/ownership path before selecting a larger GQ5 slice. The
> audit identifies that slice: the accepted index stores a heap-backed
> `Vec<usize>` and performs separate lookup/insertion probes for almost every
> unique fingerprint. ADR-0150 retains one inline primary formula index per
> fingerprint and allocates a side bucket only on a genuine collision. It is
> accepted: representative total/CNF medians improve 13.0%/29.0%; full total/CNF
> improve 11.5%/28.4% to 16.54/5.18 s; and the ratio reaches 2.14x with the exact
> same 49,199,541 clauses and all decisions/replay green. Bit blast is now the
> largest stage at 5.88 s. Re-attribute its residual operator/AIG-construction
> work by family before choosing the next exact GQ3/GQ5 slice; broad GQ4 and SAT
> remain behind their measured opportunity. That audit finds 23,029,676 cold
> term-bit records inserted into an ordered lookup map despite dense term IDs
> and contiguous existing bindings. ADR-0151 replaces only that redundant map
> with per-term ranges into the authoritative binding vector. It is accepted:
> representative total/bit-blast medians improve 5.59%/15.51%, full total/bit
> blast improve 5.71%/16.05% to 15.60/4.94 s, and the full ratio reaches 1.99x
> with identical AIG/CNF structure and replay. CNF is again narrowly largest at
> 5.18 s; audit the remaining dense-ID term memo and shared normalization before
> choosing another bounded ownership slice. The memo audit selects proposed
> ADR-0152: 982,044 completed terms retain a second set of 23,029,676 AIG
> literals in `BTreeMap<TermId, Vec<AigLit>>`, although ADR-0151's ranges and
> authoritative bindings already encode completion and the same literals.
> ADR-0152's range-backed experiment preserves structure and improves bit blast
> only 0.57%, while total p50/mean regress 0.02%/0.38%, CNF p50 regresses 0.88%,
> and variance triples. The ordered memo is restored and ADR-0152 is deferred
> without a full run. Close memo-ownership micro-work. GQ10's
> data-availability-aware representative regression gate is now in
> `just check`: it auto-discovers the pinned access-controlled pack or accepts an
> explicit path, skips visibly only when data is absent, fails incomplete
> configuration, and runs both raw and canonical against the manifest and
> in-process Z3. The first real run is 128/128 decided and agreed under both
> policies with zero errors/replay failures. Five clean canonical full-tier
> processes now establish the scheduled variance boundary: Axeyum/ratio CV are
> both about 0.51%, Z3 CV is 0.31%, and every stage is below 1%. Provisional
> same-environment regression alarms are 3% ratio, 3% Axeyum total, and 2%
> absolute Z3 drift; the guarded comparator applies them. Re-attribute the
> now-close bit-blast/CNF stages by Glaurung family before choosing another
> larger optimization. That attribution is now decisive: `slice-partial` is
> only 1,584/13,462 queries but owns 39.7% of Axeyum time, runs 3.82x behind
> Z3, and creates 16.91 million AIG nodes plus 22.87 million clauses. Its
> 377,320 lexical `bvadd` occurrences expose a precise canonicalizer gap:
> associative flattening sorts mixed symbol/constant chains but does not
> combine their constant leaves. ADR-0153's exact modular
> `bv.add_constant_chain.v1` is now accepted: five full processes improve mean
> total 9.80% to 14.11 seconds, ratio 8.37% to 1.85x Z3, AIG requests 12.13%,
> clauses 17.23%, and `slice-partial` time 24.4%, with every validity gate
> green. SAT and broad GQ4 remain behind fresh post-v3 attribution.
> ADR-0154 advances the harness to artifact v28 and records every scalar
> Bool/QF_BV operator over both original and post-word unique DAGs, including an
> explicit `other` bucket. The clean full v28 process decides 13,462/13,462 at
> 14.215 seconds versus Z3's 7.718 (1.842x). Residual excess is split between
> `register-slice` (+3.441 s) and `slice-partial` (+3.142 s); `slice-partial`
> construction correlates 0.988 with its 44,668 surviving additions. ADR-0155's
> exact modular equality cancellation is now accepted under rewrite identity
> v4. Five clean full processes improve mean Axeyum time 59.7% from 13.946 to
> 5.625 seconds and ratio 60.1% from 1.829x to 0.730x Z3; AIG nodes and clauses
> fall 76.7%/75.4%, all 67,310 executions decide and replay cleanly, and the
> exact v3→v4 guarded comparison passes. Axeyum is now faster than Z3 on this
> cold real-lifter corpus. New client-side evidence nevertheless reports bit
> blast as the dominant native-driver stage and a material driver/bench entry
> gap, so the next Axeyum implementation order is production GQ4 demand
> slicing, causal per-rule telemetry, and exact client-boundary attribution.
> ADR-0156 closes the API mismatch: Glaurung translates a whole query
> but the singular assertion API rewrites each root separately, whereas the
> winning benchmark shares one rewrite memo across all roots. The additive
> `assert_preprocessed_batch`/`assert_configured_batch` methods retain every
> original root for replay and pass focused semantic/Clippy coverage, but the
> pinned fresh-incremental gate is 18.8% slower than one-shot and emits 80.9%
> more clauses with the same AIG. The API remains explicit plumbing and the
> cold recommendation is deferred.
> ADR-0157 landed the first additive GQ4 production candidate behind
> `SolverConfig::demand_bit_slicing` / `--demand-bit-slicing`. Dense backward
> demand propagates exactly through the initial structural class and treats
> every non-local operator as a full conservative barrier; sparse symbol models
> are deterministically zero-completed and replayed against every original
> assertion. The focused 8-of-64 equality lowers 25/25 demanded term bits and
> 8/8 symbol bits rather than the full path's 81/64. Artifact v29 identifies
> observational versus applied demand, and separate whole-tier and
> `register-slice` recipes are executable. The committed micro smoke is 2/2
> decided/agreed with zero errors, disagreements, or replay failures, but it
> demands all bits and is not performance evidence. The subsequent Glaurung
> gate rejects v1: correctness stays green
> at 100% decided / zero disagreements, but the Axeyum/Z3 ratio regresses from
> about 1.42x to 4.49x and bit blast rises from 47% to 83% of time. The exact
> demand analysis costs more than the blast it removes. ADR-0157 is deferred;
> v1 remains opt-in and must never be auto-selected. Redesign GQ4 around a cheap
> syntactic admission precheck, bounded/memoized range demand, and a wide
> predicted-savings threshold with immediate fallback to the full lowerer;
> proposed ADR-0158 defines that contract. The first isolated `axeyum-bv`
> implementation now exists: a conservative single-use/envelope admission
> screen, fixed-capacity inline range propagation with a deterministic work
> budget, exact post-analysis savings rejection, and range-backed sparse
> materialization. Rejection and budget exhaustion invoke the unchanged full
> lowerer; six focused additions bring the BV suite to 32/32 green, including
> dense-v1 equivalence, deterministic fallback, fragmentation promotion,
> replay, and deadline coverage. Keep this path explicit and non-default while
> it is measured on the Glaurung `register-slice` plus whole tiers. That wiring
> is now complete in artifact v30: `SolverConfig` carries a distinct optional
> range policy, v1/v2 conflict rather than receiving implicit precedence, all
> thresholds and the work budget enter `config_hash`, and typed/per-instance/
> aggregate telemetry partitions every admission and fallback result. The
> strict whole-tier and `register-slice` recipes expose explicit calibration
> parameters. The clean pinned representative gate now rejects v2 as well.
> Conservative defaults admit 0/128 and add 0.62% total across five processes;
> a moderate exact policy admits 33/128, removes only 632 AIG nodes and zero CNF
> clauses, and adds 0.61% total / 3.14% bit-blast time. All executions remain
> decided/agreed/replay-clean, and declined admission overhead meets its <2%
> target, but the mandatory `register-slice` improvement does not. ADR-0158 is
> deferred and remains explicit/off. Stop threshold tuning; move next to GQ3's
> affected-family/ablation telemetry and GQ1's native client-path attribution.
> Artifact v31 now supplies the first half of that GQ3 boundary: every firing
> rule reports distinct affected queries/families plus selected-policy DAG/AIG/
> CNF/time totals, explicitly not mislabeled as savings. Repeatable
> `--rewrite-disable-rule` inputs build a validated default-minus-rule manifest
> and enter configuration identity, enabling paired causal artifacts. Focused
> tests and all-feature Clippy are green. The dirty exploratory capture ranks
> the structural rules by reach (`extract_extend` 45/128, `extract_bitwise`
> 12/128, `extract_nested` 9/128, `extract_concat` 4/128); rerun clean base and
> ablations before making any performance claim. ADR-0159 now completes that
> causal boundary with a fail-closed repeated comparator. Five clean paired
> rounds keep all 128 queries decided/agreed/replay-clean. Disabling
> `extract_extend` adds 6,259 lowered term bits and 1.657 ms mean cold time on
> its 45 affected queries; nested/concat effects are small and bitwise is
> timing-neutral. Crucially, all four ablations change zero AIG nodes and zero
> CNF clauses. Keep the exact rules, but close broad extract-rewrite expansion
> on this capture: fire count is not another lowering/encoding lever.
> ADR-0160 now lands GQ1's native Glaurung entry attribution without taxing
> ordinary solvers. An exact Z3-authoritative 13,126-query release stream is
> 100% decided/agreed and attributes native time to bit blast 42.81%,
> incremental CNF 37.58%, translation 4.53%, and SAT 7.23%. Its 7,065 unique
> hashes plus 6,061 duplicate occurrences preserve the reuse signal erased by
> the cold corpus. Exact manifest-overlap hashes retain the standalone AIG size
> but inflate incremental clauses, confirming that Glaurung sharing survives
> translation and that GQ5 gate fusion—not SAT tuning—is the next bounded cold
> implementation target. The run is exploratory/single-driver; clean
> multi-driver repetition remains the GQ1/GQ10 publication gate.
> ADR-0161 now closes the next GQ5 attribution question without taxing ordinary
> solvers. On the pinned 128-query representative corpus, the profiled
> incremental encoder emits 782,716 clauses versus 545,905 one-shot clauses
> over the same 450,498 AIG nodes (+43.38%). Its 508,729 lazy definition halves
> are 49.79% positive-AND-tree, 27.85% inverted-AND, and 18.83% XOR. Direct
> positive roots expose 109,358 AND nodes and 90,149 structural XOR leaves.
> This selects one bounded, selector-guarded direct positive-AND/XOR root
> fusion next; accept it only on fewer clauses plus lower unprofiled native
> Glaurung time with unchanged AIG, scopes, and replay.
> ADR-0162 accepts that bounded fusion. Selector-guarded positive-AND leaves and
> structural XOR truth clauses do not consume global single-use assumptions;
> bypassed nodes retain their ordinary lazy definitions for later reuse. The
> pinned gate stays 128/128 decided/agreed/replay-clean with the same 450,498
> AIG nodes while incremental clauses fall 782,716→615,537 (-21.36%). Two
> alternating 13,126-query native Glaurung pairs reduce mean Axeyum time
> 18.484→17.648 seconds (-4.52%) and the Axeyum/Z3 ratio 2.888x→2.772x (-4.0%).
> ADR-0163 attributes and closes the large residual. The representative cold
> pack has no guarded roots; 64,637 root clauses repeat prior root clauses, and
> 1,981 exact root/selector contexts account for 56,750 of them. Default exact
> context dedup cuts incremental clauses 615,537→558,787 (-9.22%), leaving only
> 12,882 (+2.36%) over one-shot. Two interleaved native Glaurung pairs improve
> mean Axeyum time 17.697→17.325 seconds (-2.10%) and mean normalized ratio
> 2.789x→2.719x (-2.51%), with 13,126/13,126 agreement and unchanged findings.
> A structurally stronger per-clause root index reached 550,900 clauses but
> regressed native Axeyum 2.16%, so it was removed. Treat the remaining GQ5
> clause gap as too small for another unmeasured default structure; shift the
> primary client lane to GQ1 multi-driver publication and GQ7 ordered warm reuse.
> ADR-0164 now lands the first real GQ7 end-to-end bridge without pretending the
> missing lineage exists. Glaurung opt-in snapshot reuse translates complete
> assertion sets into one retained structural arena, maps their longest common
> `TermId` prefix to per-root scopes, and retains AIG/CNF/SAT state across exact,
> extending, shrinking, and sibling snapshots. Three alternating
> `win10-vwififlt.sys` pairs remain 13,126/13,126 agreed with zero unknown splits,
> warm resets, or finding changes. Median Axeyum time falls 17.784→9.426 seconds
> (-47.0%) and the paired ratio 2.648x→1.462x (-44.8%); 679,870 prefix roots are
> retained while only 8,027 are added. Keep it opt-in: the ordered trace is still
> required for worker/path ownership, non-consecutive forks, explicit scopes,
> controlled model choices, multi-driver variance, and a GQ9 default decision.
> The current-client trajectory is consequently explicit: the standalone
> shipped default had remained on a roughly 1.42x plateau; the earlier
> arithmetic rewrites do not fire
> materially on this register-slice-heavy distribution; and the demonstrated
> cold win is the CNF-encoding work that moved the gap from roughly 2.0x to
> 1.4x. The two next credible routes are a much cheaper admitted slice under
> ADR-0158 and persistent warm reuse under GQ7. ADR-0156 alone cannot test the
> latter through Glaurung because its current `Solver` trait is one-shot.
> ADR-0166 now accepts the ordered warm-trace T1 producer and independent T2
> Axeyum replay boundary. The bounded real sample reconstructs 235 paths and
> 784 checks, strictly re-solves all 508 unique QF_BV scripts with original-model
> replay, and proves all 158 unique constraints behind 243 exploration-driving
> choices SAT. It measures 276 duplicate occurrences (35.2%) and 271 prefix
> extensions. This is opt-in downstream corpus evidence, not an Axeyum product
> dependency or warm speed claim. Its concrete producer/consumer contract is
> [ordered warm-trace v1](docs/research/08-planning/glaurung-ordered-trace-v1.md).
> ADR-0167 now accepts the opt-in T3 functionality boundary. One shared parsed
> arena feeds a distinct retained solver per live lineage; forks validate the
> exact parent prefix and replay it into a fresh child, never sharing mutable
> SAT state. The bounded trace remains 784/784 agreed with replay, and all 243
> model reads evaluate (242 recorded-value matches, one legitimate alternative
> model). The naive child strategy replays 7,378 roots across 232 forks and
> spends about 813 ms there, selecting T4 rather than a default. Next compare
> cold occurrence replay, ADR-0164 snapshot inference, and explicit lineage on
> identical bytes; capture all assertion bytes plus peak RSS/resource identity;
> then publish clean multi-driver p50/p95/break-even evidence before GQ8/GQ9.
> ADR-0168 now accepts those opt-in identical-occurrence controls. Three
> separate capped processes remain 784/784 agreed: fresh exact-byte cold takes
> 2.737 s, consecutive snapshot/LCP reuse takes 0.545 s, and naive explicit
> lineage takes 1.371 s. Snapshot retains 24,364 roots while adding 671 and
> peaks at 38.4 MB process RSS; lineage replays 7,378 fork roots and peaks at
> 83.9 MB. This selects snapshot reuse for clean repetition and hardening, not a
> default. The trace's `backend_nanos` includes both shadow backends and cannot
> be mislabeled as Z3 time. Finish T4 with producer-side per-backend timing,
> complete assertion bytes, and repeated multi-driver p50/p95/RSS/break-even.
> ADR-0169 now closes both capture gaps on one clean driver. Glaurung persists
> all 180 assertions with producer-declared free symbols and separately times
> every Z3/Axeyum call. The clean 776-check sample records native Axeyum/Z3 at
> 2.095/0.808 s (2.593x). Independent snapshot replay plus shared-arena build is
> 0.476 s (0.590x recorded Z3), while naive lineage is 1.291 s (1.598x); all
> policies decide and replay 470 SAT / 306 UNSAT, and no assertion remains
> unmaterialized. This reconciles the real client bar and proves bounded
> structural headroom, but snapshot is not yet the native Glaurung path. The
> depth buckets are now explicit: 45/46 observed depths beat Z3, with the lone
> two-check depth-12 bucket slower and every observed depth from 13 onward
> faster. Repeat across drivers and integrate snapshot through the client
> boundary before GQ8/GQ9 or a default claim.
> ADR-0170 now supplies the clean three-driver control and reverses that
> one-driver selection. At one fixed producer revision, 3,769/3,769 ordered
> occurrences decide and replay: exact cold, snapshot, and lineage are
> respectively 1.591x, 1.049x, and 0.698x the weighted same-stream Z3 time.
> Snapshot wins on `vwififlt` (0.974x) but loses on Dptf/IntcSST
> (1.225x/1.063x); lineage loses on `vwififlt` (1.458x) but wins on the other
> two (0.689x/0.242x). Reject a universal snapshot or depth-only policy. Carry
> native per-lineage/delta ownership through the client boundary next, retain
> snapshot as a fixed comparator, and require online topology/cost plus repeated
> variance before GQ9. This remains downstream workload evidence for Axeyum's
> solver interfaces, not product architecture.
> ADR-0171 now accepts that native path-owned integration as the leading opt-in
> GQ7 path. Three alternating three-driver rounds preserve all 41,916 combined
> shadow checks with zero disagreements, unknown splits, warm resets, or finding
> changes. Weighted native snapshot remains 2.093x Z3, while explicit lineage is
> 0.746x with 0.36% ratio CV and cuts Axeyum time 65.5%. Lineage wins every
> driver at the live boundary, but median RSS rises 6.3%--31.0% by driver and
> peaks at 141,124 KiB. Do not default-enable it yet. Bound live-session memory
> and inherited-prefix materialization, expose deterministic fallback reasons,
> and profile native lineage phases before GQ9 or GQ8. Glaurung remains only an
> external solver workload and integration client.
> Glaurung `49f1fe2` now lands the first deterministic lifecycle boundary:
> process-wide live-session and per-snapshot assertion caps reserve atomically,
> close an over-limit retained owner, and fall back to ordinary one-shot solving
> with explicit counters. Cap-zero and cap-one live smokes remain fully agreed
> with Z3 and finish with no retained paths. This closes explicit capacity
> plumbing, not memory admission: calibrate non-regressing limits, attribute the
> native lineage phases, and add a measured memory/fallback policy next.
> ADR-0172 now closes bounded native-lineage phase attribution without taxing
> ordinary solvers. Glaurung `13f4bbe` emits one exact-query/path-bound warm
> record per check; Axeyum's fail-closed summarizer accepts exactly 6,986/6,986
> decided records across three drivers. Weighted internal time is CNF 43.78%,
> bit blast 22.86%, SAT 17.45%, replay 5.79%, translation 3.74%, and model lift
> 3.41%. The stream adds 11.73 million clauses. Lead next with causal warm CNF
> gate/root attribution, then AIG construction per node; SAT remains third.
> Profiled time is diagnostic overhead and never replaces ADR-0171's unprofiled
> 0.746x-Z3 production result.
> ADR-0173 now closes that causal warm CNF attribution. Glaurung `21c01ce`
> emits the exact 38-counter `IncrementalCnfStats` delta in every v2 record;
> the same 6,986-check stream partitions 11,734,335 clauses into 71.75%
> definitions and 28.24% guarded roots. AND-tree shapes own 53.89% of 5.70
> million definition halves, while every positive-root opportunity is already
> fused and all duplicate/tautology counters are zero. Reject another root
> fusion/dedup tranche. Implement one future-reuse-safe positive internal
> AND-tree half-flattening experiment next, and accept it only on lower repeated
> unprofiled native time as well as fewer clauses.
> ADR-0174 now rejects that candidate without changing production defaults. It
> is semantically green, but Dptf's 2,597 applications avoid 83,544 primitive
> clauses only immediately; later helper reuse grows retained clauses
> 429,432→505,090 (+17.62%), raises profiled CNF 8.19%, and regresses three-run
> unprofiled Axeyum mean 3.65%. Keep the explicit option off and stop threshold
> tuning: current freshness cannot predict future sharing in a monotone warm
> AIG. Move GQ5 next to AIG construction cost per added node; reopen internal
> fusion only with retained-future-use evidence or clause replacement.
> ADR-0175 now accepts that AIG tranche. Glaurung `d79010a` and Axeyum
> `17f7747f` add exact v4 request/memo/copy deltas without per-request clocks.
> On Dptf, 39.61% of AND requests reach the ordered unique table and 88.77% of
> those probes insert. Replacing the private `BTreeMap` with a deterministic
> 70%-load open-addressed table preserves every structural counter and cuts
> profiled Dptf bit blast 36.09%. Three order-balanced pairs on each established
> driver decide and agree 20,958/20,958 checks per policy: weighted Axeyum time
> falls 5.487→5.067 seconds (-7.66%) and the actual-client ratio improves
> 0.742x→0.680x, with identical path traffic and effectively flat RSS. The
> accepted-table v4 profile moves bit blast behind CNF/SAT at 18.21% versus
> 46.55%/18.48%. ADR-0176 then accepts the first GQ7 memory envelope. On three
> order-balanced cap-9/cap-12 rounds, the nine-session policy preserves weighted
> Axeyum time (5.088 versus 5.091 seconds) while reducing median RSS 8.0% on
> `vwififlt` and 6.3% on IntcSST; Dptf never reaches the cap. A 128-assertion
> ceiling covers every established occurrence. Glaurung `1f24d5d` makes 9/128
> the visible bounded defaults inside still-opt-in lineage mode, with exact
> one-shot fallback and explicit overrides. Lead next with GQ10 widening; do
> not auto-enable warm reuse or authorize GQ8 caching from this bounded tier.
> Reopen AIG literal-copy ownership only from a fresh isolated gate.
> ADR-0177 records that widening result and supersedes only ADR-0176's
> assertion ceiling. Held-out SurfacePen reaches 479 assertions: 128 falls back
> 965/2,551 checks, while 512 matches unbounded traffic and improves Axeyum
> 1.633→1.063 seconds without an RSS increase. A bounded 23,797-check NETwtw10
> stream has zero assertion fallback at 512; keeping nine rather than 12 live
> sessions saves about 10 MiB for a 1.5% Axeyum cost, with all checks agreed and
> Axeyum still 2.8x faster than Z3. Glaurung `90df708` therefore uses 9/512
> inside explicit lineage. Repeat held-out variance and widen newly available
> families before GQ9; 9/512 is a resource envelope, not an automatic policy.
> ADR-0178 closes that immediate repetition gate. Three SurfacePen processes
> execute identical 2,551-check streams at 0.243x Z3 and 0.34% Axeyum CV. Three
> hard-4-GiB fixed-budget NETwtw10 processes execute identical 28,356-check
> streams at 0.360x Z3 and 0.44% Axeyum CV, with exactly 8,325 path fallbacks,
> zero assertion fallbacks/resets, and 257,736 KiB median RSS. Wall-deadline
> runs with differing query counts are diagnostic only. Automate this exact-work
> per-commit artifact next; GQ9/GQ8 remain separate policy/trust decisions.
> ADR-0179 lands that automation in Glaurung `89aea59`: a hard-4-GiB runner,
> versioned atomic artifact, exact work/finding/lifecycle validation, dirty-tree
> rejection, and homogeneous source/environment/driver/policy comparator. Three
> parser/invariant tests and a real SurfacePen run/validate/self-compare pass.
> Publish a clean baseline and regression alarms next, then fit GQ9's
> topology/cost selector; do not confuse the one-process plumbing smoke with a
> new timing claim.
> ADR-0180 adds the alarms in Glaurung `a0e5f9f`: 3% Axeyum mean, 3%
> normalized ratio, 5% median RSS, and 2% absolute Z3 drift, applied only after
> every exact identity/correctness gate. Four tests and artifact self-compare
> pass. ADR-0181/Glaurung `51666a9` now publish the clean full baseline: six
> hard-4-GiB processes execute all 92,721 exact checks with zero disagreements
> or unknown splits; SurfacePen and NETwtw10 measure 0.242x/0.360x Z3 at
> 82,432/257,632 KiB median RSS. The committed artifact is byte-identical to
> the atomic runner output and passes validation/comparison. Begin GQ9
> detected-reuse topology/cost fitting; thresholds remain investigation alarms,
> not substitutes for causal review.
> ADR-0182/Glaurung `4ae5469` lands the first such opt-in candidate: solve a
> path's first check cold while retaining only its ID, then promote on the
> second live-path check. Single-process SurfacePen/NETwtw10 calibration remains
> 100% agreed and trades 4.5--8.7% time versus eager lineage for 16--21% lower
> RSS. Extend the versioned runner and repeat exact work before any default.
> ADR-0183 closes that repeat: all 92,721 checks and topology counters are
> exact, but auto regresses Axeyum time 7.37%/4.28% while saving
> 20.66%/15.93% RSS. It therefore fails the 3% time alarm and remains an
> explicit low-memory option. Fixed lineage remains the faster opt-in policy;
> the default remains off.
> ADR-0184/Glaurung `fcc2de5` then corrects a more fundamental capture defect:
> native Z3/Axeyum assertions use arbitrary-width truthiness, but the shared
> text/trace producer compared every root with a BV1 literal. A corrected real
> SurfacePen trace validates all 2,551 checks. Keep strict sorting; regenerate
> the GQ1/GQ10 cold corpus because every expected-true byte identity changes and
> the 2,225 previously excluded wide scripts are likely recoverable.
> ADR-0185/Glaurung `95c43cb` is the next explicit GQ9 candidate. Purpose-based
> admission and fixed caps 1/2/3 are measured and rejected. Pressure-adaptive
> lineage starts at two live paths and expands once to the configured cap nine
> after 128 failed reservations. Single clean calibrations clear the time/RSS
> alarms on SurfacePen and NETwtw10, and the fail-closed runner validates exact
> adaptive traffic. Repeat three processes per family before any default claim.
> ADR-0186 closes that repeat and default decision. Glaurung `f99f72b` commits
> the clean 92,721-check artifact; SurfacePen changes +2.07% time/-3.65% RSS and
> NETwtw10 -1.03%/-0.88%, with ratio and Z3 drift also inside every alarm.
> Glaurung `ca12028` makes adaptive the default only for explorer-owned Axeyum
> solves; `off`/`false`/`0` is the explicit one-shot override. GQ9 is complete
> for available families. Return the leading client lane to ADR-0184's corrected
> GQ1/GQ10 cold-corpus regeneration.
> ADR-0187 closes that regeneration and widens it to all five query-producing
> drivers. Glaurung `1b32cb9` plus strict builder `3b64aaf` produce 30,628
> distinct scripts with zero exclusions; 7,953 scripts contain wide roots.
> Four deterministic physical shards form one byte-pinned full tier. Eight
> clean Axeyum `f7f174c5` processes decide and replay all 30,628 under raw and
> canonical v4 policies with zero disagreements or rewrite decision changes.
> Raw is 30.803/69.127 seconds (0.446x Z3); canonical is 18.471/68.556
> (0.269x), cutting AIG nodes 68.16M→32.35M and clauses 72.70M→32.12M while
> staying below 1.42 GiB child RSS. The corrected 162-query representative is
> now the regular semantic gate. Repeat the complete four-shard composite
> before setting variance alarms; shards are partitions, not repetitions.
> ADR-0188 closes that repeat and makes per-commit comparison fail closed. Two
> complete composites execute 122,512 policy/query checks with identical
> outcomes and construction. Raw Axeyum/Z3/ratio CV is
> 0.458%/0.558%/0.100%; canonical is 0.787%/0.150%/0.937%, with 0.039% peak-RSS
> CV. Corrected full-tier commits are now guarded at 3% Axeyum, 3% ratio, 5%
> RSS, and 2% absolute Z3 drift after exact identity gates. GQ1/GQ10 are done
> for current families; select the next cold implementation only from fresh
> canonical causal attribution, or advance GQ8's replay-safe cache contract.
> ADR-0189 now fixes that GQ8 contract. The first cache is explicit/off,
> per-`IncrementalBvSolver`, same-arena, and scalar-SAT-only. Identity is exact
> ordered active assertions, scope boundaries, and one-shot assumptions;
> hashes never substitute for equality, and every hit must replay the model
> against current original terms. Ordinary UNSAT/Unknown/errors and strict prefixes are excluded: UNSAT
> waits for a source-bound checked proof, while prefixes use GQ7 retained
> AIG/CNF/SAT state. Implement deterministic bounded storage and telemetry,
> then measure the ordered same-lineage stream before any Glaurung default.
> ADR-0190 completes that Axeyum implementation: caller-supplied entry/value/
> payload-bit bounds, exact assertion/frame/assumption identity, deterministic LRU,
> fail-closed replay, and public counters are additive and off by default.
> Focused full/minimal-QF_BV plus 876/876 all-feature library tests are green;
> the cache-disabled corrected Glaurung raw/canonical gate remains 162/162
> decided/agreed with zero errors, unknowns, or replay failures.
> That implementation still required an explicit Glaurung cache-off/cache-on
> ordered control; no client default was admissible without exact traffic,
> model/finding, time, and RSS gates.
> ADR-0191 lands that downstream control in Glaurung `d5475f6` without changing
> the adaptive production default. Only path-owned retained solvers may opt in;
> snapshot and one-shot paths remain cache-free. The 64-entry / 4,096-value /
> 262,144-bit per-path policy and every cache counter are versioned in the
> lineage gate. A SurfacePen plumbing smoke decides/agrees 2,551/2,551 and
> records 183 replay-checked hits, 2,368 misses, 269 declined UNSAT results,
> zero replay failures, and zero terminal gauges. It is not a performance
> claim: one process per policy and 3.33% Z3 drift fail the release-evidence
> standard. Run the clean repeated SurfacePen + NETwtw10 off/on gate next.
> ADR-0192 completes that gate. Each policy executes 92,721 clean checks with
> exact work and findings; all 185,442 combined checks agree with Z3 and have
> zero unknown splits or cache replay failures. Cache-on improves Axeyum time
> 1.16%/2.38%, normalized ratio 0.67%/2.08%, and median RSS 6.88%/1.52% on
> SurfacePen/NETwtw10 while absolute Z3 drift stays below 0.50%. Glaurung
> `e177142` therefore defaults only its bounded path-owned warm sessions to the
> fixed cache and retains an explicit off override. Axeyum's generic solver
> constructors remain cache-off.
> The capture and
> implementation audit has been expanded into the dependency-ordered
> [Glaurung QF_BV execution plan](docs/research/08-planning/glaurung-qfbv-execution-plan.md):
> reproduce the current raw one-shot path first, then compare canonical-only
> and configured preprocessing, instrument the measured construction stages,
> and pursue exact extract rewriting, demand-driven lowering, and the separate
> ordered warm-trace integration in that order.
> Keep the trust-ledger proof spine running in parallel. Full BFS-vs-DFS
> traversal analysis + post-keystone ranking:
> [build-sequencing-bfs-dfs.md](docs/research/08-planning/build-sequencing-bfs-dfs.md);
> the ranked steps live in [§ The two engineering keystones](#the-two-engineering-keystones).

## Glaurung QF_BV performance roadmap (2026-07-13)

This is the first-class client performance lane created from ADR-0136 and the
reported **1.7--3.2x Axeyum/Z3 gap** on real binary-analysis formulas. The
target distribution is the lifter's width-mixed, extract/concat-heavy,
memory-derived path conditions, not a synthetic uniformly typed substitute.
The access-controlled SMT-LIB pack is corrected and strictly ingested in
ADR-0187. Glaurung producer `1b32cb9` emits 30,678 five-driver observations;
strict builder `3b64aaf` reconciles them to 30,628 unique hashes, 50 duplicate
observations, zero verdict conflicts, and zero exclusions. The 162-query
representative and exact four-shard full tier replace the stale 128/13,462
identity invalidated by ADR-0184. The old 2,225 malformed hashes cannot be
mapped to current bytes; the current wide-coverage fact is 7,953 scripts with
wide roots. Synthetic timing remains insufficient, and malformed scripts never
count as decisions or speedups.

| ID | Roadmap item | Scope and exit criterion |
|---|---|---|
| **GQ1** | **Capture and profile real queries first** | **Real-query mapping, neutral external controls, the six-cell in-process warm map, four-oracle fuzzing, proof denominators, authoritative policy controls, process-isolated certificates, behavior-preserving Glaurung A0, corrected finding semantics, source-backed controls, symbolic-CVE artifact admission, 2/2 selected-pair recall, deterministic six-cell work-bound calibration, and one bounded downstream infeasible-path certificate are complete through ADR-0278.** ADR-0272 accepts 64,510 repeated occurrences with complete six-way parity and zero fallback: Axeyum beats warm Z3 on three named drivers and loses on Dptf, while warm Bitwuzla leads all four. ADR-0273 rejects independent backend-limit calibration because Axeyum never reaches the fixed 95% gate; ADR-0274 accepts only the invariant-stream triplet (Z3 100,000, Axeyum 32,768, Bitwuzla 512); and ADR-0275 accepts its first-20 reproduction but rejects the attempted 338-function census because every repetition analyzes only 210/338 functions and incurs 102 assertion-cap fallbacks. This exact harder-driver protocol is closed negative despite byte-identical findings and 97,112/97,112 verdict agreement. ADR-0276/0277 close the fixed GQ5 duplicate-clause lane without an accepted change. ADR-0278 then closes only the reviewer-minimum proof attachment/source-rebinding/external-consumption cell; proof prevalence, nontrivial traces, cost, and whole-CFG composition remain unmeasured. Broaden labeled recall only with independently admitted artifacts, keep symbolic memory closed, and reopen proof integration only around a separately preregistered real workload; otherwise advance the next structural or deployability item. |
| **GQ2** | **Cheap always-on cold simplification tier** | Add a bounded, denotation-preserving one-shot tier for constant folding and trivial identities whose own cost is measured. Add a size/shape and cold-vs-warm policy that selects cheap, configured, or no preprocessing. Exit only when cold end-to-end time is non-worse in aggregate and improves the target class at the GQ1 validity gates. |
| **GQ3** | **Coercion-cancellation peepholes and causal telemetry** | **Current measured tranche complete; use ablation as policy evidence.** Exact nested/concat/extension/coercion rules and ADR-0159's repeated default-minus-rule comparator are landed. `extract_extend` improves lowering, but all four measured rules change zero AIG nodes and clauses. Do not globally delete sound rewrites because one corpus does not fire them; instead, keep a Glaurung policy only for rules with measured reach/cost and reopen register-slice-specific work only when an ablation demonstrates downstream AIG/CNF or native-time reduction. |
| **GQ4** | **Cold demand-driven bit-slice reduction** | **Out of the active queue.** ADR-0157 v1 is correct but regresses the real ratio about 1.42x→4.49x; ADR-0158's conservative admission is a safe no-op but does not improve the required family. Both remain explicit/off. Do not tune thresholds further on this corpus; only a qualitatively different constant-cost admission proof and a fresh client gate can reopen GQ4. |
| **GQ5** | **Cheaper AIG construction and measured CNF encoding** | **The fixed duplicate-clause and flat-storage lanes are both CLOSED negative (ADR-0259--0285).** Candidate `9533c508` removes the exact v37 duplicate cell but fails fixed CV/family gates and is removed at `4fc45767`. ADR-0285's independent flat arena preserves all 162 decisions/replays/construction identities and reaches a favorable 0.540824 aggregate logical-storage ratio, but fails the frozen per-instance <=80% rule on 5/162 payload-dominated singleton-clause rows. Timing is forbidden; commits `56936920` / `f3456365` restore production. Reopen only from a new independently motivated mechanism and zero-row ADR, not another partition, rerun, threshold relaxation, or candidate inferred from these failures. |
| **GQ6** | **Cold SAT/CDCL tuning** | **Fresh and retained exact-CNF controls DONE (ADR-0220/0221).** The proof core beats fresh BatSat before checking, while retained BatSat beats retained Z3 Boolean by 3.5527x on the ordered Axeyum CNF stream. Do not select a custom-core rewrite from Dptf; reopen only on a SAT-dominant family with a neutral core gap and deterministic limits. |
| **GQ7** | **Cheaper warm entry and delta preprocessing** | **Source identity, fair map, query/internal attribution, fresh/retained exact-CNF controls, four-driver neutral cold-reset and source-owner-retained SMT, bounded raw finding parity, canonical tcpip authority, four-schedule union, isolated configurable-policy A0, corrected taint/SystemBuffer baselines, versioned confidence partition, 14-row source-backed positive control, v1 resource rejection, v2 maximum-precision rejection, detector repair, corrected sweep, exhaustive source-backed difference adjudication, and a full v6-gated wider authority campaign DONE (ADR-0201--0205/0213--0248/0262 plus Glaurung `7f682e5`; campaign revision `ff3c0a7`).** ADR-0232 shows 16.4x--57.0x within-cvc5 retained/full-reset reductions while preserving the external textual boundary. A0's public `ConcretizationPolicy` covers both concretization seams and preserves default value selection. ADR-0247 completes all five scalar cells; ADR-0248 then proves their 54 varying planted-fixture rows contain zero independent primitives. ADR-0262 confirms on the wider prefix that LeastUnsigned restores exact authority parity but overlaps only 147 rows with AnyModel's 220-row union and costs 96,075 solves / about 191 MiB under Axeyum. Publish raw, confidence-gated, validated, work, and cost partitions; never use raw `>= AnyModel` or producer confidence alone as a recall target. Keep symbolic-address memory gated off pending a genuinely broader labeled residual gap. The companion cross-repository Pareto strategy owns the downstream/SOTA analysis and sequencing. |
| **GQ8** | **Verdict and CNF reuse for duplicate/prefix queries** | **Exact replay-checked SAT reuse is done for available families (ADR-0192); stronger subsumption remains open.** Exact hits replay under fixed bounds; ordinary UNSAT/Unknown and prefix verdict reuse remain forbidden. Investigate only replay-checked stronger-model reuse where a cached model is proven to satisfy the complete weaker later query. |
| **GQ9** | **Auto production policy and API guidance** | **DONE for available serial families (ADR-0186/0199).** Adaptive 2→9 ownership plus serial sibling continuation reuse is the downstream default; ADR-0199 clears every time/ratio/RSS/environment alarm and improves RSS on both accepted drivers. Explicit one-shot, fixed, transfer-only, and serial-off controls remain. Re-gate wider families and never apply serial leases across parallel workers. |
| **GQ10** | **Ordered, wider real-lifter regression corpus** | **Native timeout-continuation admission is DONE; wider direct-delta admission is deferred (ADR-0205--0212).** The accepted tcpip gate still defaults one bounded continuation only inside selected direct-delta sessions. A complete 85,449-event / 17,400-check `dxgkrnl` trace and independent 13,577-query / 8,816-model-read replay prove exact production-topology no-op functionality with zero correctness or lifecycle alarms. The repeated ordinary-core comparison nevertheless fails the declared timing-CV gate (14.430% control, 8.306% candidate); slower-core calibration changes actual outcomes at the 250 ms boundary. Keep direct delta opt-in. `win32k` is now classified as a system-service/callout frontend target, not zero-query IOCTL solver evidence. |

**Post-ADR-0199 Glaurung next-ten mapping (2026-07-16).** This is the current
priority interpretation of the latest client feedback; it supersedes older
stage rankings where the accepted evidence has changed.

| Rank | Client requirement | Current action / gate |
|---:|---|---|
| 1 | Cold CNF/bit-blast micro-optimization | **Current origin-selected lane closed.** ADR-0261 changes all three selected construction counters by zero, so it is rejected before timing and removed. Do not reinterpret ADR-0260 again; reopen GQ5 only after a separately preregistered leaf-shape/clause-overlap diagnostic identifies a new mechanism with a fixed structural delta. |
| 2 | First-class incremental `Solver` trait | **Contract, opt-in explorer wiring, profiling, and dual-control gate done in ADR-0201/0202/0203 and Glaurung ADR-011/012.** Direct entry is correct under exclusive ownership and causally faster than equivalent snapshot entry, but fails production serial-snapshot alarms. Keep it opt-in; `assert_configured` remains warm-only. |
| 3 | Safe automatic warm policy | **Done for current families in ADR-0186/0199.** Adaptive ownership, exact cache, owner transfer, and serial sibling leases default on only in the explicit explorer context; preserve all off/fixed controls and re-gate wider families. |
| 4 | Lineage RSS Pareto knee | ADR-0198 rejects a third retained owner (+7.66% RSS); ADR-0199 instead reduces accepted SurfacePen/NETwtw10 RSS 6.11%/13.36%. Continue only topology/lifetime changes that clear the 5% alarm. |
| 5 | Sibling-prefix structural sharing | **Functionality and production comparison done in ADR-0204/0205.** Exact `Arc` ancestry preserves one mutable session; the two-driver production gate passes. The exclusive-control comparison still rejects +4.06% SurfacePen Z3 drift; rerun only under a same-environment/order-balanced control. |
| 6 | Wider driver corpus and repetitions | **DEFERRED at the wider-default gate; native continuation admission remains done (ADR-0206--0212).** The 71,136-check tcpip gate admits bounded continuation. The complete 17,400-check `dxgkrnl` no-op control preserves exact outcomes, cache behavior, work, findings, and topology, but its ordinary-core Axeyum-time CV is 14.430%/8.306%, above 3%; slower-core repetitions change bounded outcomes and are rejected too. Keep direct delta opt-in and rerun only in a quieter/exclusive environment or on another valid no-timeout IOCTL driver. Route `win32k` to a future system-service/callout frontend. |
| 7 | Warm CNF dominant-cost attack | Historical pre-ADR-0199 warm CNF was 43.8%; serial sharing cuts CNF 66.8% and makes SAT 47.2% of that candidate profile. Re-profile each accepted policy and require retained-future-use or rollback evidence before retrying AND-half flattening. |
| 8 | Stronger-than-exact replay cache | Test only SAT model subsumption: a retained model may answer a weaker later query only after evaluating every complete original assertion. Keep UNSAT/Unknown and unchecked prefix verdict reuse forbidden. |
| 9 | Parallel path exploration | Confirm `Send`/per-worker ownership and benchmark independent path solvers. ADR-0199 leases are serial-only and must never cross workers; determinism, memory caps, and replay remain mandatory. |
| 10 | Harder/large-BV preprocessing parity | Use causal ablation on DptfDevGen-class formulas to select exact large-BV rewrites. Keep GQ4 slicing off and never reintroduce configured one-shot preprocessing without a cold end-to-end win. |

**Glaurung consumer feedback invariants (2026-07-16).** These ten items are
standing product/measurement requirements, not a transient benchmark wish list.
Where a reported headline conflicts with the captured counters, the stricter
artifact evidence below governs.

The [2026-07-20 reconciliation](docs/research/08-planning/glaurung-feedback-reconciliation-2026-07-20.md)
maps the original snapshot to the later fair-baseline, oracle, proof,
deployability, and artifact-readiness results. Consult it before quoting the
historical performance or robustness numbers.

| # | Feedback integrated into the roadmap | Required action / invariant |
|---:|---|---|
| 1 | Strict sorts are a consumer differentiator and have exposed three real Glaurung soundness defects (empty-model steering, extension width, declared concat width). | Never add implicit coercion to IR builders or soften sort errors. Keep `coerce_to` explicit and caller-selected. Preserve strict replay as a correctness-oracle/paper result, including ADR-0207's evidence that Z3's silent coercion changed bit placement rather than merely accepting malformed syntax. |
| 2 | Warm/incremental reuse is workload-dependent: retained rewrite/CNF/learned state yields two fair wins, one tie, and one loss across the measured drivers. | Keep GQ7 first-class, preserve exact delta/source ownership and replay, and widen through captured ordered streams plus fixed-work multi-driver gates before broadening the automatic default. Cold and warm numbers must never be blended, and no blanket speed claim is allowed. |
| 3 | Cold one-shot remains the pure-solver optimization target: historical real-driver attribution is roughly 42% bit blast + 42% CNF versus about 15% SAT, while the deduplicated gate has plateaued around 1.34x. | Lead cold work with term→AIG→CNF construction (GQ5), not SAT tuning. Require fresh stage attribution and repeated end-to-end corpus wins; the exact ratio is revision/corpus-specific, not a timeless constant. |
| 4 | `assert_configured` loses one-shot and wins only when amortized. | Document and test it as a warm-only optimization. Do not auto-select configured preprocessing for fresh one-shot queries; retain raw/canonical one-shot controls and a measured cost model. |
| 5 | Precise `IrError` diagnostics are load-bearing integration tooling. | Keep operation, widths/sorts, and exact invalid ranges in errors; add regression assertions for each consumer-discovered class. An error must remain actionable and must never be reclassified as UNSAT. |
| 6 | Complete scalar-model construction was 94% of measured model-lift time; empty-theory projection cut that work about 99% and median Axeyum time about 25%. | Preserve ADR-0195's lean scalar QF_BV model path as the default when no theory projection is required. Any broader projection skip must prove complete requested-symbol models plus original-term replay. |
| 7 | Per-root replay memo creation consumed 38.8% of warm internal time; shared bounded replay state cut it about 88%. | Preserve ADR-0193's shared memo and deterministic clearing bound. Audit other embedders for root-by-root evaluator recreation, but never trade away original-root replay or unboundedly retain evaluator state. |
| 8 | Robustness holds at large real-driver scale, but decided-rate must be stated exactly. | Maintain zero crashes, hangs, wrong SAT/UNSAT verdicts, and replay failures; keep `Unknown` first-class and cause-partitioned. Do **not** repeat the stronger “every query decided within 250 ms” claim: post-fix tcpip still contains measured bounded timeouts, which are sound nondecisions rather than failures or UNSAT. |
| 9 | Self-rechecked DRAT UNSAT evidence is a deployability/correctness advantage over the current Z3 crate path. | Keep `UnsatProof::recheck()` prominent in examples, capability tables, and performance reporting. No optimization may bypass proof generation/recheck where proof-bearing UNSAT is promised. |
| 10 | Pure Rust/no-C and the `qfbv`-only profile reduce deployment cost; benchmark methodology must reject fast failure. | Preserve the no-native default and lean feature profile; gate WASM claims on an actual target build rather than aspiration. Every comparison must report per-backend SAT, UNSAT, Unknown, Error, decided rate, replay, and exact work/finding identity. A faster number with reduced work or increased nondecisions is invalid until attributed—the pre-fix tcpip/dxgkrnl ratios are explicitly withdrawn. |

The reviewer-facing [Glaurung correctness-oracle case study](docs/research/07-verification/glaurung-correctness-oracle-case-study.md)
now consolidates the three consumer defects plus the wide-value adapter defect,
pins their exact regression ownership, and corrects an important shorthand:
strict width/sort checking exposed the extension and concat bugs, while
fail-closed result typing and ordered model replay exposed empty-model steering.
The standing named controls retain exact actionable diagnostics separately from
the 12,000-row four-oracle valid-formula campaign.

**Publication execution order (2026-07-18, ADR-0213--0239 plus ranked review;
supersedes performance-claim ordering below).** Product admission and paper
evidence are now distinct:

1. **Map the honest performance regime — mechanism, four-driver fair map,
   trace-available feature join, in-process neutral control, and the exact
   deterministic harder-driver protocol DONE (the latter closed negative):**
   the v2 marked path and
   fail-closed analyzer already provide N>=5 fixed-work four-cell outcomes,
   geomean paired ratios, deterministic bootstrap 95% confidence intervals,
   p50/p90/p95/p99, CDFs, process CV, and exact warm/fallback partitions.
   ADR-0217 establishes two Axeyum wins, one tie, and one Z3 win with no
   nondecisions. ADR-0218 shows that SAT/UNSAT outcome, consumer purpose, and
   exact-query reuse composition are material while lexical formula size is
   insufficient. ADR-0219 shows retention removes nearly all repeated
   construction and leaves SAT dominant. ADR-0220 closes fresh exact-CNF
   parity, and ADR-0221 closes all 431 ordered retained core calls: BatSat beats
   Z3 Boolean on Axeyum CNF, so the native-Z3 win moves to word-level
   representation/integration. ADR-0222 adds exact cvc5 verdict parity plus a
   cold-reset external SMT point on Dptf; ADR-0223 widens exact cvc5 parity to
   all 9,526 four-driver checks. ADR-0232 adds a source-owner-retained cvc5
   control over the same stream with exact persistent-prefix and temporary-
   assumption topology. ADR-0272 closes the topology-equivalent in-process
   neutral point: all six Z3/Axeyum/Bitwuzla cold/warm cells decide and agree,
   while warm Bitwuzla leads all four drivers and rules out an Axeyum
   performance-lead headline. ADR-0273--0275 carry the harder tcpip tier through
   backend-specific work calibration, invariant-stream triplet selection, and
   joint reproduction, but reject the 338-function census at 210/338 analyzed
   functions plus 102 assertion-cap fallbacks per repetition. Do not retune
   that protocol or treat identical findings/verdicts as complete work. The
   publication claim is the measured map and only a causally supported boundary,
   never a preselected speedup. Solver work returns to a new GQ5 diagnostic; any
   future harder-driver successor requires a new zero-row ADR.
2. **Correctness as the lead contribution — standing/exhaustive-neutral seed
   round and first proof denominator DONE (ADR-0224--0226), independent/real
   coverage WIP:**
   all 4,000 deterministic rows agree in Axeyum, direct Z3, and cvc5; 1,487 SAT
   models replay on original IR; and executable coverage requires all five
   random widths plus 35 operator classes. Named controls preserve strict
   concat/extension/constant rejection, legitimate empty-SAT versus model-less
   UNSAT, normalized widths, and linked-adapter W128 behavior. ADR-0237 closes
   the independent/edge continuation: 12,000/12,000 formulas agree across
   Axeyum, direct Z3, cvc5, and Bitwuzla; all 4,471 SAT models replay; all 14
   semantic-corner families are nonvacuous. Publish the bounded TCB and retain
   the hard-seed/resource history. The first proof subset is
   169/169 rechecked end to end but only 6.725030% of generated UNSAT; add a
   deadline-aware widening harness. ADR-0230 adds a separate real-query CNF
   DRAT denominator: 64/64 representative UNSAT rows recheck, alongside 64/64
   SAT model replays and complete Z3/manifest agreement. ADR-0231 then widens
   generated proof selection to all 1,505 width<=8 UNSAT rows under a declared
   search deadline: CNF DRAT is 1,505/1,505 and stronger certification is
   1,487/1,505 with 18 exact uncovered seeds retained. ADR-0234 separately
   certifies all 74 UNSAT rows in ADR-0187's corrected representative end to
   end in two clean runs under a 1000 ms cooperative deadline. ADR-0235 then
   repeats 74/74 under killable whole-certificate process isolation and proves
   with a 1 ms control that all 74 expiry rows remain in the denominator.
   ADR-0251/0252 preregister the disjoint 1,024-query holdout and its exact
   materialization. ADR-0253 accepts all 1,024 primary decisions, 515 SAT
   replays, and 509 CNF DRAT rechecks in both repetitions; the stronger route is
   508/509 with one stable retained hard timeout. Never merge the generated and
   real assurance denominators or report the retained row as certified.
   Keep invalid consumer states separate from valid-formula fuzz.
3. **Neutral baselines and oracles — four-driver cold-reset, source-owner-
   retained breadth, the three-solver timeout frontier, and the six-cell
   in-process neutral map DONE (ADR-0222/0223/0232/0233/0272):** cvc5 1.3.4 agrees on all 9,526 accepted checks with exact model-output
   accounting and stable N=5 throughput in both protocols. ADR-0232 matches
   persistent-prefix, temporary-assumption, and owner-session topology while
   remaining explicitly external/textual. ADR-0233 separately sweeps the exact
   52-formula tcpip hard frontier at 50/100/250/1000 ms across Axeyum, Z3, and
   cvc5 and closes the neutral formula-timeout blocker. ADR-0272 adds the fair
   in-process Bitwuzla cold/warm point with complete six-way decisions,
   agreement, and zero fallback. Keep in-process, FFI, and external SMT boundary
   costs separately named; do not use Z3 as both sole oracle and sole comparator.
   ADR-0275's wider sole-authority **finding** attempt is retained as a negative
   completeness result, not a performance or recall row; a successor is not an
   automatic continuation of this protocol.
4. **Authoritative finding parity — bounded four-driver, canonical and wider
   tcpip controls, extremal/mixed-site policy sweeps, corrected taint/SystemBuffer
   semantics, the source-backed positive control, and bounded symbolic-CVE
   recall slice DONE; broader labeled recall remains open only when independently
   admitted (ADR-0229/0236/0238--0248/0262--0271/0273--0275):** sole-authority Z3 and Axeyum
   binaries emit byte-identical ordered raw sink lists on Dptf, vwififlt,
   IntcSST, and SurfacePen across N=3 order-balanced repetitions: 302 canonical
   sinks and 1,812 stable emitted rows. Differing vwififlt/IntcSST solve counts
   prohibit an identical-exploration claim but do not change output. Tcpip
   prefix 15 supplies the measured raw divergence: its AnyModel cells have 126
   stable shared diagnostics plus two Z3-only rows. The opt-in unsigned-minimum policy
   gives both authorities the same 110 sinks, 80,563 solves, and complete
   model-choice telemetry with zero inconclusive choice. Because the policy
   changes the shared population, keep it opt-in. ADR-0238's exact
   least/greatest control passes authority parity with a 125-row union (69
   common, 41 least-only, 15 greatest-only), but comparison with the
   arbitrary-model union leaves 33 arbitrary-only and 30 extremal-only rows.
   Preserve that negative overlap result. ADR-0239's two complementary
   stable-site mixed-extremum schedules pass exact authority parity at 95 and
   98 rows. They add three rows beyond the extrema for a 128-row four-schedule
   union, yet recover none of the 33 arbitrary-only rows. This confirms that
   value selection is a cheap policy knob, not a separate research program.
   Glaurung A0 now extracts a first-class `ConcretizationPolicy` on isolated
   branch `axeyum-concretization-policy-a0` and proves `AnyModel` reproduces the
   accepted pre-A0 value-selection behavior. ADR-0240's follow-up at `845239f`
   preserves exact taint sources and classifies the two Z3-only rows as
   generic-`Arg0` artifacts; both authorities have zero high-confidence findings
   on this prefix. ADR-0241's v5 harness rebaselines all five existing settings,
   proves every tcpip row is diagnostic under the producer policy, and closes
   the former 33-row AnyModel-only remainder as `Arg0`/`Arg1` ancestry. The
   corrected four-driver tier and a NETwtw10 prefix likewise contain zero
   accepted rows. ADR-0242 then rejects usbprint's five apparent rows: its old
   seed made the I/O-manager-owned `METHOD_BUFFERED` pointer attacker-selected.
   Glaurung branch `b79f269` preserves attacker-controlled contents at a fixed
   kernel address, and the complete corrected N=2 control has 0/0 accepted rows,
   214 diagnostics, and 16,537 solves per authority. ADR-0243 independently
   joins tracked source and machine code to 14/14 stable planted-fixture rows
   under both authorities. ADR-0244 then rejects complete usbprint as a policy-
   invariant work boundary. ADR-0245 clears AnyModel/minimum but maximum adds a
   source-rejected `stack-overflow` while preserving all 14 expected rows; the
   detector's concrete +/-64 KiB `dst`/`rsp` proximity is not semantic stack-
   region proof. ADR-0246 repairs that predicate with structural expression-DAG
   ancestry and restores the exact maximum-policy 14-row set. ADR-0247 accepts
   all five executable cells (AnyModel, least, greatest, site-hash-zero, and
   site-hash-one) at Glaurung `7f682e5`: every setting preserves 14/14, while
   tcpip remains an unlabeled zero-high diagnostic population whose exact
   deterministic counts vary 84--110. ADR-0248 exhaustively closes the complete
   source-backed difference as 30 ordinary plumbing rows plus 24 duplicate sink
   presentations, with zero independent primitives. ADR-0262's wider tcpip
   control remains unlabeled and policy-sensitive despite exact LeastUnsigned
   authority parity. ADR-0263--0271 admit only two frontend-eligible symbolic-
   CVE pairs and accept 2/2 vulnerable-side detections with 2/2 fixed sides
   clean; this is selected-pair recall, not 22-CVE population recall or
   precision. ADR-0273--0275 then reject the exact full-census protocol because
   complete function work and zero fallback do not hold. Add
   BoundarySet/DiverseEnum only as later settings of the same policy surface
   after bounded successor forking is executable; do not fake them by collapsing
   a set to one value. Deterministic work bounds are configuration; symbolic-
   address memory remains gated off until a genuinely broader labeled population
   demonstrates residual coverage headroom, not from a detector classification
   artifact.
   Require genuinely broader labeled evidence before any finding-preservation
   claim.
5. **Deployability and artifact readiness — profile, WebAssembly, bounded warm
   Pareto, and representative plus wider-holdout real-query proof deployment
   DONE (ADR-0216/0227/0228/0230/0234/0235/0251--0256):** `qfbv` is the
   exact solver default; Glaurung
   and `axeyum-wasm` select it explicitly; full in-tree consumers opt in; and
   host tests plus an executed wasm32 SAT/UNSAT gate protect the browser
   binding. Stable release size, dependency footprint, and Node/Chromium
   latency are now recorded. Two current same-stream controls report one-shot
   cost, warm time/RSS, retained-owner/cache/core partitions, and zero fallback.
   The corrected 162-row representative proof corpus adds 74/74 independently
   rechecked real-query UNSAT CNF DRAT proofs and 74/74 stronger end-to-end
   certificates, with all 88 SAT models replaying and complete Z3 agreement in
   two clean process-isolated runs, with the kill path separately exercised
   without dropping rows. The disjoint 1,024-query holdout adds 515 SAT replays
   and all 509 CNF DRAT rechecks; its stronger fixed-policy coverage is 508/509
   with one stable retained hard timeout. ADR-0254's independent `drat-trim`
   positive verifies, but its deleted-final-line negative remains verifiable
   because the input CNF is already unit-refutable. ADR-0255 preserves that
   rejection, and ADR-0256 accepts the preregistered satisfiable-CNF checker
   control: the real pair verifies while the same proof against the satisfiable
   input does not. This closes one standard-consumer cell, not a nontrivial
   proof-trace claim. ADR-0258's fixed scan finds 32/32 more trivial two-byte
   proofs and closes further holdout mining. Consider a
   narrow QF_BV parser only against the committed bundle baseline, and widen
   matched RSS only if it outranks the remaining publication blockers.
6. **Supporting artifact work:** contribution ablations, neutral SMT-COMP QF_BV
   and a second workload axis, then measured module/API decomposition,
   table-driven duplicate removal, and typed configuration policies. Preserve
   behavior and evidence identity across each bounded refactor.

No ratio of sums, single-run ratio, timeout-mixed population, or warm aggregate
containing unnamed one-shot fallbacks is a paper speedup. GQ5 resumes with a
new preregistered diagnostic, not with the rejected ADR-0261 candidate or an
unmeasured implementation; it does not wait for every remaining publication
item.

ADR-0200 tests and rejects the first bounded implementation of rank 1. Replacing
only the cold CNF primary fingerprint map with deterministic no-delete open
addressing preserves every decision and structural counter, but five clean
representative processes regress mean/p50 CNF time 8.55%/7.52% and total time
3.67%/3.87%. The accepted `std::HashMap` primary is restored; no full run is
warranted. Do not assume ADR-0175's AIG-table win transfers to clause
fingerprints. Re-attribute a larger CNF subphase or encoding hypothesis before
the next GQ5 candidate, and keep first-class incremental push/pop/assume as the
next structural API item.

ADR-0201 accepts that rank-2 Axeyum API item in `1058cf84`. The always-exported,
object-safe `IncrementalSolver` extension trait represents genuine retained
assert/push/pop/check/check-assuming sessions and is implemented first by
`IncrementalBvSolver`; one-shot `SolverBackend` and snapshot-resubmitting
`Solver<B>` remain semantically distinct. Generic and trait-object conformance,
the existing warm suite, strict Clippy, and warning-denied rustdoc pass under
full and `qfbv`-only profiles. The downstream rank-2 contract and wiring are now
concrete. Glaurung ADR-011/`f5a3b7a` adds the matching object-safe session and
drives it from explorer-owned absolute prefix deltas. Its 41/41 backend group
and both focused explorer ownership tests are green; the selected adapter also
passes with combined Z3+Axeyum features. The route remains behind
`GLAURUNG_AXEYUM_DIRECT_DELTA=1`. Glaurung `00bd660` and accepted ADR-0202 now
export and strictly validate per-check direct versus snapshot translation/root
partitions. ADR-0203 closes the rank-2 gate without a default change. Direct
entry improves time 10.98%/5.08% against topology-equivalent snapshot on
SurfacePen/NETwtw10, but loses the actual serial-snapshot production gate on
SurfacePen time/ratio and NETwtw10 RSS. Keep it opt-in and move GQ7 to sound
source-identity/COW sibling-prefix sharing.

ADR-0204/Glaurung `aee3418` now lands that source-identity candidate. Immutable
append ancestry is shared by `Arc` across forks, divergent siblings receive
distinct nodes, and the direct adapter rewinds by exact common-ancestor identity
before translating the target suffix. The stale equal-depth model regression,
42 backend tests, 12 explorer tests, and combined Z3+Axeyum checks pass. The
next action is gate calibration and repeated real-driver measurement, not a
default change.

ADR-0205/Glaurung `29031f8` closes that current production comparison. The
committed source-prefix artifact passes all alarms against serial snapshot while
improving both held-out drivers' time, normalized ratio, and RSS. A fresh
exclusive-direct control remains rejected solely on +4.06% SurfacePen Z3 drift.
New single-process evidence adds 51,073 disagreement-free `tcpip`/`dxgkrnl`
checks, so direct remains opt-in and GQ10 widening becomes the next gate.

ADR-0206 corrects that widening interpretation. At the standard 600-second
per-function ceiling, `tcpip` reaches 70,639 queries and exposes 973
decided/nondecided splits despite zero SAT/UNSAT disagreements. Glaurung
`a6a5cc0` adds exact content-addressed split capture. Build and attribute the
60-second `tcpip`/`dxgkrnl` split corpora before adding either DriverSpec; do not
equate a truncated zero-disagreement count with complete parity.

ADR-0207 completes that attribution and records another strict-sort soundness
win. The 60-second tcpip pack contains 733 distinct Axeyum errors with the same
`extract [63:8] out of range for width 57` cause: Glaurung ignored declared
concat half-widths in its text, Z3, and Axeyum consumers. Glaurung `d60ed0f`
normalizes both children at that boundary. Exact reruns remove all adapter
errors and resets; tcpip/dxgkrnl retain zero SAT/UNSAT disagreements and run
1.9x/2.7x faster. The nine residual Z3-decided tcpip formulas all decide
correctly cold, but four exceed the production 250 ms cap and are explicit
`Unknown(Timeout)`. Next measure warm-state versus cold timeout/fallback, then
repeat the full findings/RSS/variance gates; do not reopen broad QF_BV
functionality or weaken Axeyum sorts.

ADR-0208 then rejects the first explicit timeout fallback. A synchronized warm
`Unknown` may be retried once through a fresh 250 ms one-shot solver, but the
tcpip run recovers only 4/15 occurrences, leaves 11 nondecisions, and raises RSS
10.46% despite keeping time at +2.38% and all verdict/error gates green. The
dxgkrnl no-timeout control is exactly inert. Keep the diagnostic off; next test
a bounded same-session continuation or a strict recoverability predictor that
avoids whole-snapshot reconstruction, then repeat the full DriverSpec gates.

ADR-0209 completes that bounded same-session experiment without overstating the
result. Glaurung `6e5b255` reuses the synchronized solver and translated
assumptions for exactly one fresh 250 ms check. The full-budget tcpip pair
recovers 5/14 occurrences, reduces nondecisions 14→9, and stays inside the
time/RSS alarms (+1.98%/+0.034%) with zero disagreements, errors, or resets.
Both processes nevertheless hit the analysis deadline: the candidate executes
19 additional queries and retains all 780 control findings plus two later null
dereferences. This is useful functionality evidence, not exact-work causality.
Keep the switch explicit/off and make fixed-work or repeated query/finding
identity the next GQ10 acceptance boundary.

The follow-up shows that a fixed function prefix alone is not exact work.
Glaurung `399c770` makes both processes complete the same 156/338 tcpip
functions without hitting the wall deadline, but bounded Z3 nondecisions differ
47→46 and steer 70,592 versus 70,768 authoritative queries. Findings are also
non-identical (781 shared, one control-only, two candidate-only). Continuation
recovers 3/11 occurrences at +1.47% Axeyum time/+0.18% RSS with every safety
gate green, yet the resource deltas remain descriptive. Glaurung `61b008f`
records the rejection. The next GQ10 artifact must capture one ordered
authoritative occurrence stream and replay both policies over those exact
queries; do not spend another long run on a live-pair causality claim.

ADR-0210 closes that exact-stream mechanism gate. Glaurung `3c3c77e` replaces
recursive trace rendering with deterministic postorder `let` bindings, making
the authoritative tcpip store 3.8 rather than 35 GiB while preserving
cross-pool content identity. Its validated stream contains 301,852 events and
70,823 checks. The matched independent lineage candidate performs 14
continuations = 7 recoveries + 7 repeated unknowns + 0 errors, reduces final
nondecisions 13→7 relative to the separate-process control, and preserves
identical work, structure, model evaluation, and zero decided disagreements.
Warm replay/RSS move +1.97%/+0.034%, inside the alarms. This accepts the bounded
same-instance mechanism, not the downstream default: native admission still
requires the production source-owner/serial-lease topology, repeated exact
traffic/findings, and every existing resource/correctness gate.

ADR-0211 closes that native admission gate without conflating it with broader
direct-delta admission. A clean work-limited tcpip producer publishes 326,364
events / 71,136 checks / 794 finding rows plus 10,515 native packs and the exact
source-owner/serial-lease lifecycle. Independent Axeyum replay validates all
50,687 unique queries and 27,940 model reads. Three interleaved native pairs
then preserve exact work and implementation identity while candidate
continuation recovers 18/29 bounded nondecisions with zero errors, opposite
decisions, resets, replay failures, topology drift, or terminal gauges.
Candidate p50 Axeyum time/RSS changes +2.027%/+1.021%, and time CV remains below
0.4%. Glaurung `9ace064` therefore defaults the single continuation on inside
separately selected direct-delta sessions, with missing=on and explicit or
unrecognized values failing closed to off. Direct delta itself remains opt-in.

ADR-0212 completes the next wider functionality control but defers admission.
Clean `dxgkrnl.sys` publishes 85,449 events / 17,400 exact checks / 312 finding
rows and the complete source-owner/serial-lease lifecycle; independent Axeyum
replay validates all 13,577 unique queries and 8,816 model reads. Three
ordinary-core control/candidate pairs preserve exact work, outcomes, cache
behavior, and zero continuation traffic, but Axeyum-time CV is 14.430%/8.306%
and fails the declared 3% alarm. A relaxed 20% comparison is diagnostic only;
slower-core calibration changes actual outcomes at the 250 ms deadline and is
also rejected. Keep direct delta opt-in and repeat only under a quieter,
predeclared environment or with another valid no-timeout IOCTL driver.
`win32k.sys` is not such a driver: its service-table/callout shape yields no
WDM/KMDF dispatch roots, so it moves to a future system-service/callout
frontend rather than counting as zero-query solver evidence.

The 2026-07-17 verification checkpoint is green for formatting, strict
all-target/all-feature Clippy, the full workspace test and doctest suite,
warning-denied documentation, the QF_BV profile, the pinned 162-query
Glaurung regular gate, foundational resources, rules-as-code generation and
validation, and documentation links. The host lacks `just`, so the aggregate
wrapper and its nine recipe-rendering tests remain unavailable; the underlying
gates were run directly. Current-nightly Clippy required only mechanical,
semantics-preserving test-literal, redundant-pattern, `strip_prefix`, and `?`
cleanups.

**Glaurung engineering evidence history through ADR-0212.** The ADR-0213
publication order above supersedes this section for paper claims. Earlier
evidence reported an approximately 1.34x gated-bench
ratio but roughly 2.5x on one actual `IncrementalBvSolver` stream, with
bit-blast/CNF/SAT near 45%/32%/20%. ADR-0170's fixed-revision driver set now
measures a 1.255x weighted native ratio with a much wider 0.426x--2.679x
per-driver range. ADR-0171's repeated live path-owned policy reaches 0.746x Z3,
while live consecutive snapshot is 2.093x. Treat the pre-parsed bench, native
client, external replay, unprofiled lineage, and diagnostic controls as
distinct bars. ADR-0172 attributes the live internal total to CNF/bit-blast/SAT
at 43.78%/22.86%/17.45%; ADR-0173 partitions the CNF traffic and rejects more
root fusion/dedup work. ADR-0174 then defers internal AND flattening because
immediate savings invert under later helper reuse. ADR-0175 closes the next
AIG tranche: exact v4 attribution selects the ordered unique table, and
deterministic open addressing improves the repeated three-driver actual-client
ratio from 0.742x to 0.680x without structural or memory regression. ADR-0176
then accepts 9 live paths/128 assertions inside explicit lineage reuse: weighted
Axeyum time stays 5.088 versus 5.091 seconds at cap 12, while median RSS falls
8.0%/6.3% on the two drivers whose unbounded peak is 11. ADR-0177 then raises
only the assertion ceiling to 512 after held-out 479-root paths expose a 35%
avoidable Axeyum cost at 128; the nine-session conclusion survives the large
Wi-Fi stress stream. ADR-0178 accepts repeated exact-work held-out variance:
SurfacePen and NETwtw10 are stable at 0.243x/0.360x Z3 with 0.34%/0.44% Axeyum
CV and identical structural counters.
ADR-0193 consumes the subsequent v5 profile rather than relying on that older
stage balance: per-root evaluator memo recreation made mandatory original-term
replay 38.82% of profiled SurfacePen internal time. A same-assignment memo with
a fixed 4,096-entry cross-root retention bound reduces replay 87.78% and a
same-current-client causal gate reduces SurfacePen Axeyum time 36.94% with
lower RSS. The clean two-driver candidate also improves NETwtw10 3.77%, but
the older SurfacePen artifact's RSS control is stale and fails by 6.52%; refresh
the clean same-current baseline before replacing the committed artifact.
The ranked work is:

1. **GQ7 warm end to end:** build on ADR-0164's measured snapshot-LCP bridge,
   ADR-0166's ordered T1/T2 boundary, ADR-0167's per-lineage T3 path, and
   ADR-0168's identical-occurrence controls; ADR-0169 completes assertions and
   per-backend timing. ADR-0170's control selects native per-lineage/delta
   ownership, ADR-0171 accepts its repeated 0.746x-Z3 live result, ADR-0175
   improves the same actual-client bar to 0.680x, ADR-0176 accepts the first
   bounded memory policy, ADR-0177 widens assertion admission to the held-out
   512-root envelope, ADR-0178 accepts repeated fixed-work variance, and
   ADR-0193 removes bounded repeated evaluator work while retaining every
   original replay root. Glaurung `f5a3b7a` now removes snapshot-prefix
   reconstruction from an opt-in direct-delta route while preserving the full
   query for Z3/capture/fallback. Glaurung `00bd660`/ADR-0202 add exact v7
   direct-entry profiling. The first real run catches and `f4da0eb` closes the
   depth-only/serial-sibling correctness conflict. ADR-0203's repeated gate
   accepts the causal direct-entry win but rejects production replacement on
   time/RSS. ADR-0204 supplies exact source-identity sibling prefixes, and
   ADR-0205 accepts the serial-production win. Keep direct opt-in. ADR-0206/0207
   complete exact split capture and close Glaurung's declared-concat error class;
   ADR-0208 rejects cold retry, ADR-0209 establishes low-memory same-session
   continuation, ADR-0210 accepts its exact-stream mechanism gate, and ADR-0211
   accepts the repeated native production-topology gate. Glaurung `9ace064`
   defaults one continuation on only inside a separately selected direct-delta
   session. ADR-0212 proves exact `dxgkrnl` no-op functionality but defers the
   wider default after the standard variance gate fails; slower-core runs also
   fail exact behavior. Keep direct delta opt-in and rerun only in a quieter
   predeclared environment or with another valid no-timeout IOCTL driver.
   Route `win32k` to a system-service/callout frontend;
2. **GQ1/GQ5 measured construction:** ADR-0174 defers internal AND flattening;
   ADR-0175 accepts deterministic open-addressed AIG sharing at a 0.680x
   actual-client ratio. Reopen CNF only with future-use/replacement evidence and
   AIG ownership only with a fresh isolated copy/locality hypothesis;
3. **GQ10 clean baseline after automation:** **DONE for warm lineage in
   ADR-0181 and refreshed for corrected cold bytes in ADR-0187.** Use the clean
   artifacts for their separately named bars and repeat the full cold shard set
   before installing corrected-corpus timing alarms;
4. **Measured CNF work:** continue the proven encoding lane, but only from
   dominant gate-pattern attribution and a native-time gate after ADR-0163;
5. **Causal rewrite policy:** use ablation to select Glaurung-relevant rules and
   require downstream structural/time effects; do not globally erase useful
   rules merely because this capture does not exercise them;
6. **GQ8 duplicate/prefix reuse:** **DONE for available Glaurung families in
   ADR-0192.** Exact same-arena scalar SAT duplicates use mandatory replay and
   fixed bounds in path-owned sessions; prefixes reuse retained state only,
   ordinary UNSAT/Unknown remain uncached, and explicit off is preserved;
7. **GQ6 SAT tuning:** the measured 17.45% weighted share is material; compare exact
   CNF across cores and measure inprocessing/heuristic changes;
8. **GQ9 non-regressing auto mode:** **DONE in ADR-0186/Glaurung `ca12028`.**
   Second-check, purpose, and fixed-small-cap policies are rejected; adaptive
   2→9 pressure admission passes the clean repeated gate and is the downstream
   explorer default with an explicit one-shot override;
9. **GQ10 deeper capture/trending:** **DONE for current families in
   ADR-0187/0188.** Five-driver widening, exact sharded baselines, repeated
   complete-composite variance, and guarded per-commit resource/timing identity
   are executable; re-gate newly added families; and
10. **Dual gap baseline:** report both pre-parsed in-process Z3 and Glaurung's
    actual Z3 AST/context backend, with the user-visible Glaurung-vs-Glaurung
    comparison controlling product claims.

The pre-ADR-0213 highest-leverage engineering trio was (1) refresh the clean same-current
two-driver baseline/candidate artifact for ADR-0193, (2) attribute model-lift
work against the symbols actually required for complete original replay, and
(3) continue measured CNF construction from the new v5 stage balance. No
model-lift optimization may omit completion or weaken replay. GQ8 admission is
complete in ADR-0192, and corrected composite variance is complete in
ADR-0188. ADR-0194 now lands the opt-in Axeyum subphase/counter boundary for
item (2), and Glaurung v6 measures the result: complete-model construction is
165.192/175.049 ms (94.37%) of model lift, versus 7.146 ms for assignment
reconstruction and 2.427 ms for AIG recomputation, across 2,551/2,551 decided
and agreed checks with zero replay failures. This rejects duplicate-AIG-pass
work as the next lever. ADR-0195 accepts the exact scalar-QF_BV completion fast
path: it skips only empty array/UF projection discovery after completing every
user symbol, retains every original replay root, cuts causal median client time
25.45% on SurfacePen and 4.33% on held-out NETwtw10, with non-increasing RSS
and every semantic/traffic gate green. The machine-readable adaptive/cache-on
refresh now passes over 185,442 checks: mean Axeyum/ratio improve
23.82%/24.99% on SurfacePen and 3.55%/4.04% on NETwtw10, with RSS and Z3 drift
inside their alarms and exact findings/traffic. Re-profile the accepted current
native path before selecting another GQ5/GQ6 or model-lift implementation.
ADR-0196 now accepts the selected topology fix. The first candidate transferred
the terminal parent's exact-prefix solver to the earlier fork child and failed:
that owner idled behind the sibling subtree, increasing adaptive pressure,
SurfacePen RSS, and NETwtw10 time. The accepted LIFO-aligned policy transfers
exclusive ownership only to the last-pushed/next-executed child; every sibling
remains fresh, and an unused fresh ID lets ordinary parent cleanup preserve the
transferred solver. The clean adaptive/cache-on gate preserves all 185,442
decisions, findings, traffic partitions, cleanup invariants, and replays while
improving mean Axeyum time/ratio 14.71%/15.04% on SurfacePen and
34.77%/34.36% on NETwtw10. RSS and Z3 drift remain inside alarms. Transfer is
the Glaurung default with an explicit off control; re-profile this accepted
current state before selecting the next GQ7/GQ5 residual.
ADR-0197 makes that accepted-current profile sound for the actual adaptive
policy rather than only its fixed-lineage control. The new fail-closed mixed
summarizer validates all 2,535 warm plus 16 native fallback records in their
original 2,551-check sequence. The production residual is SAT 28.01%, CNF
21.39%, translation 14.77%, bit blast 14.31%, and replay 11.19%. Newly created
warm owners still own 78.4% of warm bit blast and 70.7% of warm CNF, while
retained owners own 94.7% of warm SAT. The 16 bounded fallbacks are 0.63% of
checks but 6.02% of internal time. Investigate the smallest sound fresh-
sibling/fallback prefix-reuse or adaptive-admission lever first; keep SAT
tuning as a separately gated identical-CNF experiment rather than conflating
these populations.
ADR-0198 then rejects the smallest admission-only shortcut before adding a new
policy surface. Three order-balanced SurfacePen pairs show that the no-fallback
three-owner ceiling improves mean Axeyum time 5.50% and ratio 6.30%, but raises
median RSS 7.66% and fails the 5% alarm. Keep the adaptive initial cap at two;
do not spend a NETwtw10 gate or implementation slice on an already-rejected
policy. The next fresh-owner hypothesis must reuse immutable prefix
construction without retaining or sharing another mutable solver.
ADR-0199 refines that requirement after auditing the actual boundary.
Cloning an immutable prefix is not cheap today because `IncrementalCnf` owns an
opaque BatSat instance and would need clause reinsertion plus a new lift-map
contract. The accepted serial DFS sibling lease lets queued siblings hold
references to one logical owner while only the popped state mutates it and the
existing snapshot LCP path restores divergent scopes. All 185,442 checks and
findings remain exact. SurfacePen time/ratio improve 17.08%/18.53% and RSS
falls 6.11%; NETwtw10 improves 0.72%/0.35% and RSS falls 13.36%. All gauges
close at zero and every alarm passes. Serial leasing is now the adaptive
default with explicit off; ADR-0196 remains the transfer-only control.
GQ4 is not an active optimization;
ADR-0157/0158 remain explicit/off. Cold rewrite or CNF work may continue only
when causal/native profiles select it. ADR-0164 permits opt-in consecutive
snapshot reuse now; ADR-0166 supplies the bounded ordered T1/T2 evidence;
ADR-0167 supplies opt-in per-lineage T3 replay. ADR-0169 supplies complete
assertions and per-backend timing; ADR-0170's T4 controls show an external
policy reversal. ADR-0171 completes native per-lineage/delta integration and
repetition: lineage wins all three live streams but costs more memory. ADR-0176
supplies the first bounded lifecycle/fallback envelope, and ADR-0177 corrects
its assertion ceiling on held-out drivers without weakening the live-session
guard. ADR-0178 completes repeated held-out validation; automated per-commit
identity and a topology/cost rule still precede cache capacity or
automatic-policy choices.

**Recorded cold-path sequence.** The detailed task graph and functional acceptance boundary
live in the
[Glaurung QF_BV execution plan](docs/research/08-planning/glaurung-qfbv-execution-plan.md).
The byte-complete representative and well-typed full capture contracts and the
**raw** current-Glaurung one-shot baseline now exist under GQ1/GQ10. Raw,
canonical-only, and configured policies remain explicitly separate; never
silently substitute one for another. Residual-rewrite, demanded-bit,
AIG-hash/rule, and CNF-subphase counters are landed. ADR-0143 and artifact v27
remove the observational demand profiler from production while retaining an
explicit complete diagnostic mode. Corrected full raw/canonical trials are
24.30/21.07 s versus Z3's 7.66/7.76 s; canonical's 13.3% total win comes from a
44.4% bit-blast reduction, while CNF remains 9.40 s and now dominates. Take the
measured GQ5 gate/root-emission and duplicate-handling slice next. ADR-0144's
formula-owned collision-safe dedup index lands the first such win: canonical
full CNF falls 9.40 → 7.66 s and total 21.07 → 19.22 s with identical counts.
ADR-0145 removes not-AND emitter temporaries and further reduces CNF 7.66 →
7.23 s, gate emission 3.56 → 3.19 s, and total 19.22 → 18.69 s with the
same 49,199,541 clauses. Inspect root-emission allocation and planning next;
ADR-0146's reusable direct-root leaf scratch regresses representative median
total/CNF 1.1%/4.9% and is restored as negative evidence without a full run.
ADR-0147 then improves planning 2.5% but regresses whole-pipeline total/CNF
0.5%/3.6% and is likewise restored. Re-attribute shared clause
normalization/allocation before selecting another bounded GQ5 slice. ADR-0148's
combined capacity hint regresses total/CNF 2.5%/10.0% and is restored as
negative evidence. ADR-0149's formula-header-only isolation also regresses CNF
median/mean 0.83%/0.67% and is restored. Capacity hints are exhausted; next
ADR-0150's larger ownership slice replaces the per-fingerprint heap vector and
double common-case map probe with an inline primary index plus a collision-only
side table. It cuts representative total/CNF 13.0%/29.0% and full total/CNF
11.5%/28.4%, reaching 16.54 s / 2.14x Z3 with identical content. CNF is now
5.18 s versus bit blast's 5.88 s; re-attribute residual operator lowering and
AIG construction by family before selecting the next exact circuit-producing
slice. ADR-0151 removes 23.03 million ordered
term-bit lookup insertions via dense ranges while preserving binding order,
public lookup, incremental arena growth, and replay. It cuts representative
total/bit blast 5.59%/15.51% and full total/bit blast 5.71%/16.05%, reaching
15.60 s / 1.99x Z3 with identical structure. CNF (5.18 s) and bit blast
(4.94 s) are now close; audit the remaining dense-ID memo and shared clause
normalization before choosing the next measured slice. ADR-0152 removes
only the redundant ordered memo ownership while keeping operand-vector cloning
unchanged, but fails the representative gate: bit blast improves 0.57% while
total p50/mean regress 0.02%/0.38% and CNF p50 regresses 0.88%. Restore the
ordered memo and close this micro-lane. The access-controlled GQ10 regular
representative gate now runs raw and canonical automatically when data is
available and passes all 128 rows. Five clean full-tier canonical trials now
put total/ratio/Z3 CV at 0.51%/0.51%/0.31% and establish provisional 3%/3%/2%
same-environment alarms. Re-attribute the close bit-blast/CNF stages by family
before another larger measured optimization. That attribution is complete:
`slice-partial` was 11.8% of queries but 39.7% of Axeyum time and 3.82x behind
Z3. Accepted ADR-0153 combines scalar and wide constant leaves in mixed affine
`bvadd` chains under rewrite identity v3. Five full processes improve total
15.644 → 14.111 seconds (-9.80%), ratio 2.022x → 1.852x (-8.37%), AIG requests
12.13%, clauses 17.23%, and `slice-partial` time 24.4%; all 13,462 decisions and
replay gates remain green. The rewrite-aware guarded comparator verifies that
v3 is exactly v2 plus `bv.add_constant_chain.v1` before applying the 3%/3%/2%
alarms. Re-attribute the v3 residual before another cold change.
GQ4 is now closed/off for this distribution after both measured candidates
failed to improve it. GQ6 is relevant at the reported 20% share but remains
ranked after warm/client-boundary work. GQ7--GQ9 require the separate
[ordered warm-trace v1](docs/research/08-planning/glaurung-ordered-trace-v1.md)
because the deduplicated cold corpus erases prefix/frequency information.
ADR-0166 accepts the bounded producer and independent replay gate; next map its
validated lineages to retained solver state and promote capture to a clean
multi-driver publication. GQ8 follows the exact cache/replay contract rather
than treating a prefix as an identical query. Re-run the GQ10 baseline after
every accepted slice and record the result in `STATUS.md` and `bench-results/`.

**GQ1/GQ10 readiness landed (2026-07-13/14, artifact v26).** The client recipe is
now a single-worker cold run. Its artifact separates word preprocessing,
bit-blast, CNF encoding, optional CNF inprocessing, SAT, model lift, and
original-query model replay; reports aggregate and exact p50/p95 timing; and
computes the Axeyum/Z3 ratio with
in-process Z3 solving the untouched parsed assertions. Manifest v1 additionally
pins the capture source/logic, exact directory membership, per-query SHA-256,
expected verdict, family, stable order, and named representative/full tiers;
all bytes are validated before timing and every selected verdict is gated.
Artifact v18 profiles the untouched original DAG before rewriting: formula
p50/p95, BV width diversity, extract/concat/extension and surviving array-op
density, demanded-vs-source extract bits, exact GQ3 cancellation opportunities,
and AIG/CNF p50/p95 sizes. Flattened memory provenance remains manifest metadata,
because it cannot be recovered from an already-lowered BV term. Artifact v19
also exposes `--prove-unsat`: a separate high-assurance companion run uses the
proof-producing core, fails closed unless each UNSAT's DRAT proof checks, and
reports proof-check p50/p95 nested within SAT time rather than double-counting
it. Micro-corpus performance/proof smokes prove the measurement and ingestion
plumbing, including mandatory in-process Z3 coverage, not the client performance
hypothesis. Artifact v20 adds a reproducible-run identity: Axeyum source
revision and clean-tree status, Cargo.lock SHA-256, rustc/cargo versions, build
profile, exact backend names, CPU model, kernel, logical parallelism, and total
memory. A
separate environment hash covers tools/hardware while intentionally excluding
the source revision, so `config_hash + environment_hash` compares consecutive
commits and the revision identifies which commit produced each result.
`--require-reproducible-run` fails before solving if any identity field is
missing or source changes are present; all Glaurung recipes require it.
Artifact v21 replaces the former decorative benchmark `--seed` label with an
executable determinism profile. The artifact and `config_hash` now bind the
actual Cargo.lock-pinned BatSat defaults (seed `91648253`, random branching
frequency `0`, random polarity off, and random initial activity off), an
explicit Z3 `random_seed=0`, and deterministic corpus ordering. Runtime tests
pin the reviewed BatSat values, while repetition ingestion fails closed on any
profile drift. This proves solver seed/configuration identity, not stable wall
time; independent-process variance remains mandatory.
Artifact v22 closes the separate deterministic-resource boundary for the cold
client lane. `--require-deterministic-resources` fails before parsing the corpus
unless positive term-DAG, CNF-variable, CNF-clause, and backend-search limits
are all present. The default BatSat path now consumes `resource_limit` as a
deterministic `within_budget` progress-check cap; the proof-producing core uses
it as a conflict cap; and Z3 continues to use it as `rlimit`. Artifacts record
these backend-specific units and explicitly state that equal numbers are not
cross-backend work-equivalent. The provisional `axeyum-qfbv-cold-bounded-v1`
recipe uses 300k DAG nodes, 3M CNF variables, 8M CNF clauses, and 2M search
units. Wall-clock timeout remains a non-deterministic safety backstop, and the
profile must be versioned—not silently relaxed—if the real capture cannot meet
the 100%-decided gate.
Artifact v23 adds a behavior-preserving before/after shape boundary. Every
parsed query now records the untouched original DAG and the DAG submitted after
the selected raw/canonical/configured word policy. Per-instance and corpus
records classify extract-over-concat into low-side, high-side, straddling, and
whole-operand cases; classify zero/sign-extension extracts into low, high, and
straddling regions; record exact low cancellations and maximum nested-extract
depth; and report before/after/removed/added counts for every GQ3 class. Raw is
therefore expected to prove a zero transition, while canonical/configured runs
show the exact residual opportunity set reaching bit lowering.
Artifact v24 adds behavior-preserving construction attribution. The AIG reports
every primitive AND request as exactly one trivial simplification, absorption
simplification, structural-hash hit, or newly allocated node. The CNF encoder
reports planning, retained-variable allocation, non-root gate emission, and
root-emission time; reachable/helper/direct-root counts; recognized gate-family
counts; and attempted, tautological, duplicate, and emitted clauses. Instance
and corpus records carry explicit partition invariants, and mark CNF subphase
timers as nested within total CNF encode time. These counters identify a GQ5
target; they do not themselves justify changing the AIG table or encoding.
Artifact v25 adds a conservative structural demand profile before changing the
lowering contract. Demand propagates exactly through extract, concat,
zero/sign extension, pointwise BV operations, `ite`, rotations, and FP bit
reinterpretation; unclassified operators conservatively request every operand
bit. Instance and corpus records compare request, unique-demanded, available,
and actually lowered term/symbol bits, publish coverage invariants and ratios,
and separately time the analysis nested within bit-blast. A focused 8-of-64
regression records 25/81 demanded term bits and 8/64 demanded symbol bits while
the current full-child lowerer materializes 81/81 and 64/64. This measures the
GQ4 opportunity without yet changing semantics or model projection.
Artifact v26 charges canonical-only rewrite elapsed to the word-policy stage,
PAR-2, cold total, and Axeyum/Z3 ratio. Artifact-v25 canonical ratios omitted
that cost and are diagnostic-only.
Artifact v27 implements ADR-0143: production lowering skips the observational
demand walk, retains actual lowered-bit counts, and marks structural demand
fields unavailable; separately named diagnostic recipes opt in and include the
profile cost. Five representative raw/canonical production trials have median
ratios 1.65x/1.37x. Full single trials are 3.17x/2.71x, with every validity gate
green. Canonical reduces full production time 13.3% and bit blast 44.4%, but
CNF encoding is now the largest stage at 9.40 s (44.6% of total).
ADR-0144 then removes the duplicate clause copy/ordered-vector lookup without
changing encoding order or content. Five representative canonical trials
improve median CNF 15.3% and total 6.3%; the full confirmation improves CNF
18.5%, total 8.8%, and ratio 2.71x → 2.47x with all 13,462 validity gates green.
Post-change CNF remains the largest stage at 7.66/19.22 s.
**GQ3 exact semantic tranche landed (2026-07-14, ADR-0142).** The default
manifest now composes nested extracts, splits concat-boundary straddles, returns
whole concat operands directly, and reduces low/high/straddling zero/sign
extension slices. Replacement roots receive at most eight exact local rule
applications; a public report counter records a remaining opportunity at fuel
exhaustion while returning the denotation-equivalent partial term. Each rule
has a stable manifest ID, identity model projection, fixed fresh-node bound,
exhaustive small-width and seeded wider evaluator evidence, and lifter-shaped
Z3 SAT/UNSAT differential replay. The expanded default benchmark identity is
`axeyum-rewrite-default-v2`. The real capture now validates the semantic tranche
as a word-DAG/time win: 1,315/1,435 representative opportunities disappear and
materialized term bits fall 57% representative / 72% full. Corrected v27
production timing shows a 17.4% representative median / 13.3% full single-trial
total reduction with all validity gates green. GQ3 remains open because
full-tier AIG/CNF size rises slightly; another word rule must demonstrate a
downstream circuit/CNF benefit, not merely remove word-DAG traversal.
The remaining shadow-diff handoff is also executable: a versioned capture index
contains the producer-owned ordered path, trusted verdict, family, and tier
facts, while `--generate-corpus-manifest` checks exact directory membership,
computes every query digest from disk, rejects exporter-supplied hashes/unknown
fields, and re-validates the deterministic manifest through the ordinary run
ingestion path. The committed micro index proves this handshake only.
For short client runs, `bench-glaurung-qfbv-repeated` now preserves the cold
boundary with a fresh process and artifact per whole-corpus trial. Its
fail-closed summary requires identical configuration and clean experiment
identity plus every validity gate in every trial, then reports p50/p95, sample
standard deviation, and coefficient of variation for corpus-level Axeyum/Z3
totals, their ratio, and each attributed Axeyum stage. This is run-to-run
variance; the per-query distributions remain shape distributions.
A committed three-trial micro repetition smoke exercises this contract from a
clean source revision: every trial is 2/2 decided/manifest-agreed/Z3-agreed,
and the summary reports finite whole-corpus and per-stage variance. Its tiny
timings are plumbing evidence only, not a client ratio.
Cross-commit tracking is likewise fail-closed: the repetition-summary comparator
recomputes both inputs from their trial records, requires the same corpus,
manifest, solver config, environment/toolchain/hardware, and backends, and
permits only the clean source revision to differ. It reports raw Axeyum and Z3
controls beside the ratio and stage deltas; optional regression/drift thresholds
are explicit caller policy rather than synthetic defaults.
The current artifact-v22 cross-commit micro smoke exercises the bounded-resource
comparison boundary between clean revisions `fe65b076` and `01c2441a` with
matching corpus, manifest, config, environment, backends, and resource profile.
Its candidate/baseline ratio mean is +21.78%, but candidate ratio CV is 20.40%,
the descriptive standardized delta is +0.97, and the raw Z3 control is +2.65%.
These sub-millisecond values demonstrate identity/noise reporting and support no
performance or regression claim.
**Real capture ingested and measured (2026-07-14).** Glaurung commit `286f744`
was captured sequentially on the three pinned Windows drivers. The raw audit is
15,710 index rows, 15,687 unique hashes, 23 duplicate rows, and zero verdict
conflicts. Strict parsing found 2,225 ill-sorted producer dumps
(1,429 120-vs-64, 795 96-vs-64, one 160-vs-128); Z3's CLI independently emits
sort errors for them, so their internal capture verdicts do not describe the
dumped scripts. They are excluded from performance without weakening Axeyum's
sort checker. Axeyum-generated hash-free-index manifests bind a 128-query
representative tier (64 SAT / 64 UNSAT) and a 13,462-query well-typed full tier
(1,774 SAT / 11,688 UNSAT). Both were byte-complete and access-controlled.
ADR-0184 later identifies the shared Glaurung renderer as the cause; these
counts/manifests are historical and must be regenerated.

Artifact v26 charges canonical rewrite cost. Five representative trials give
median raw/canonical/configured ratios of 6.53x/3.42x/3.54x; canonical cuts
Axeyum total 48.5%. Every one of the 15 trials is 100% decided and manifest/Z3
agreed with zero errors or replay failures; raw and canonical proof companions
each recheck all 64 UNSAT rows. Same-revision full raw/canonical trials are
15.19x/6.32x and valid on all 13,462 rows. The committed access-controlled
result summary is
[`glaurung-qfbv-2026-07-14.md`](bench-results/glaurung-qfbv-2026-07-14.md).

Artifact v27/ADR-0143 resolves the measurement blocker: structural demand is
opt-in, production records explicit incomplete-profile provenance, and the
corrected representative/full results are valid. The full canonical pipeline
is now 1.84 s word rewrite, 5.85 s bit blast, 9.40 s CNF, and 3.78 s SAT.
`register-slice` and `slice-partial` contributed 20.86/21.07 s before the first
GQ5 slice. ADR-0144 now reduces total to 19.22 s with identical CNF content;
remaining CNF gate emission (3.56 s), root emission (1.40 s), and planning
(1.21 s) dominated that historical tranche. The pre-v4 aggregate diagnostic
demanded 98.16% of term bits and initially moved broad GQ4 behind GQ5; the new
native-client profile and register-slice concentration now supply the required
family-specific evidence to reopen GQ4 as the first implementation priority.
The performance command also exposed a mode mismatch: the producer's v17 result
and Glaurung's current one-shot backend are raw (rewrite off, preprocessing off),
while the former Axeyum recipe forced `--preprocess`. The artifact-v25 recipes
now split raw, canonical-only, and configured policies for single, repeated,
and proof-companion runs; the unsuffixed compatibility entries select raw as the
current-integration baseline. Dry-run regression tests pin every recipe's flags
and prevent the three artifact series from silently converging.

**Validation checkpoint (2026-07-15).** A complete serialized `just check` at
`623cae4c` passes under the hard 4 GiB virtual-memory cap with formatting,
strict all-target/all-feature Clippy, every workspace and doc-test suite,
warning-denied docs, the lean QF_BV profile, all 31 Glaurung recipe/profile
tests, foundational resources, generated-resource drift, and link checks. The
pinned 128-query real Glaurung gate decides every query with zero disagreements,
errors, or replay failures: raw/current integration is 0.181498 s versus Z3's
0.169850 s (1.069x), while canonical v4 is 0.050672 s versus 0.150092 s
(0.338x). The gate refreshed five tracked frontier timing curves, but a
structure-only comparison confirms their frontiers, decisions, and statuses
are unchanged. This validates the current implementation without changing the
GQ ordering: clean multi-driver GQ1/GQ10 publication, the measured GQ5
residual only if new attribution selects it, and GQ7 explicit-lineage warm
solving remain next.

The post-ADR-0166 aggregate gate then exercised the new ordered-trace binary
against the same full verification surface. Formatting, strict workspace
Clippy, every workspace test and doctest, warning-denied documentation, the
QF_BV feature profile, and all 31 Glaurung harness tests passed under the 4 GiB
cap. The run correctly exposed one packaging regression before the pinned
corpus could start: `axeyum-bench` now had two binaries, so legacy unqualified
`cargo run -p axeyum-bench` recipes were ambiguous. Commit `f6fcd81f` restores
the established CLI by declaring `axeyum-bench` as the package default binary.
After that fix, the pinned 128-query raw and canonical policies both decide
128/128 with zero errors, disagreements, or replay failures; this run measures
raw at 0.186834 s versus Z3's 0.152914 s (1.222x) and canonical at 0.051122 s
versus 0.153682 s (0.333x). Foundational resources, generated rules-as-code
drift checks, and link validation also pass. This split rerun closes the exact
failure without pretending it is a fresh single-command performance baseline;
T4 identical-occurrence warm controls remain the next GQ7 action.

**Non-negotiable acceptance gate.** Comparable runs require 100% decided on the
declared client tier, zero operational errors, `DISAGREE=0`, zero model/proof
replay failures, fixed seeds and solver versions, and bounded deterministic
resources. A faster error, `Unknown`, replay failure, or changed query
distribution is not a speedup. The benchmark methodology and layer counters are
defined in
[benchmarking-and-performance-methodology.md](docs/research/08-planning/benchmarking-and-performance-methodology.md).

## Where we are vs the north star — measured reality check (2026-06-28)

**Measured status: the build is well underway, soundness is holding, and there
is a concrete, fully-mapped road to Z3 + Lean parity.** axeyum is a sound,
pure-Rust reasoning stack — *measurably ahead on a growing set of fragments*,
with every remaining fragment decomposed into sized, exit-criteria'd work. The
job is exactly what it has always been: advance the next verifiable increment,
relentlessly. Scored against [the north-star definition of done](docs/plan/00-north-star.md):

| North-star criterion | Status | Evidence (measured, not asserted) |
|---|---|---|
| **Soundness (never a wrong verdict)** | **Strong / holding** | `DISAGREE = 0` across all 35 division baselines (oracle-compared count lives in the generated scoreboard — hand-copies rotted three times) ([SCOREBOARD](bench-results/SCOREBOARD.md)). Two real wrong-safes in the consumer apps were found by new differential fuzzes and fixed. |
| **Feature coverage (breadth)** | **Partial** | Columns exist for ~24 fragments (BV/ABV/UF/LRA/LIA/NRA/NIA/FP/DT/strings/seq/FF/…), but many are shallow. |
| **Completeness / decide-rate** | **Partial — the central gap, narrowing** | decided/total live in the generated [SCOREBOARD](bench-results/SCOREBOARD.md) **Totals** line (authoritative; ~73% as of 2026-07-07 — do not hand-copy the integers, they rotted repeatedly), decide-rate **0%–100%** across divisions. Arithmetic now decide-strong (QF_NIA-cvc5 85%, QF_NRA-cvc5 84%); the dominant remaining wired-fragment gap is strings (QF_SLIA 36%, QF_S 58%). Z3/cvc5 still cover more divisions than the ~35 measured. |
| **Measured performance (PAR-2 head-to-head)** | **Weak — but now measured where it matters most** | The north star says *no parity claim without this number*. The first committed head-to-head exists (`582ecba8`, 2026-07-03, public QF_BV p4dfa lazy-vs-eager at 3s/20s, DISAGREE=0): lazy weakly dominates (7>4 at 20s) but `lazy_ops_total=0` on all 113 — the edge is inherited word-level preprocessing, not CEGAR, and Z3 decides all 113 in ≤1s. Not competitive at scale; the measured lever is reduction depth. |
| **Lean parity (every unsat carries a kernel-checkable proof)** | **Early / narrow** | ~15/35 rows have a Lean route worth auditing; the trusted-reduction ledger is **not yet zero**. The Lean *tactic backend* (P3.7) is unbuilt. |
| **Pareto-dominance on selected fragments** | **Growing — the real, defensible claim** | **23 fragments** carry a committed, audited `dominant%` ([DOMINANCE](bench-results/DOMINANCE.md)). This — not wholesale replacement — is what the strategy actually targets. |

**Full parity across all of Z3/cvc5/Lean is not yet reached — and it is the
destination we are actively building toward, not a wish.** The identity is:
*untrusted fast search, trusted small checking* — sound everywhere measured,
dominant on a growing fragment set, with a pure-Rust/WASM/certifying moat. The
remaining decide-rate, performance, and proof-coverage work is mapped track by
track below and under [`docs/plan/`](docs/plan/README.md); we advance it one
increment at a time and record each one.

**Where the remaining work lives (the two load-bearing fronts + two keystones, below):**
1. **Decide-rate & measured performance (Track 1)** — close the 0–100% spread
   fragment by fragment: SAT inprocessing + word-level reduction, SAT-core
   modernization, and *committed head-to-head PAR-2 numbers* (no parity claim
   without them). This is where Z3/cvc5 parity is actually won. The grounded,
   prioritized per-fragment target list is
   [decide-rate-frontier-2026-06-28](docs/plan/decide-rate-frontier-2026-06-28.md)
   (headline: strings are the largest gap *by count* (~117) but a **depth/encoding**
   gap — bounded length ≤16, not missing operators — so the **best ROI is the
   uninterpreted-sort IR keystone (QF_UF)**; try the cheap string-bound lever
   before the big unbounded-string DP; NRA/CAD depth is the genuine catch-up, last).
   **Landed (2026-06-29, measured on the accessible curated corpus vs z3,
   DISAGREE=0; see [decide-rate-measured-2026-06-29](docs/plan/decide-rate-measured-2026-06-29.md)):**
   QF_S is already at z3 parity on accessible data (so the string `max_len` lever
   has no verifiable headroom there); **QF_UF 37→39/48** (equisatisfiable
   uninterpreted-sort `ite`-elimination + a no-hard-error robustness fix);
   **QF_ABV 173→176/177** (write-index array extensionality for shared-base
   `store-chain = store-chain` over wide indices, + robustness). Remaining leads:
   the UF+theory-combination keystone (`issue5836-2`/`issue5396`); and a confirmed
   **deadline-robustness defect** — QF_AUFLIA `bug330` runs 25 s under a 2 s
   `config.timeout` (the UFLIA combination solve on its array-abstracted
   relaxation doesn't check the deadline; QF_LIA and the lazy-row CEGAR are clean).
2. **Reduction certificates → Lean (Track 3)** — drive the trusted-reduction
   ledger to zero (Alethe emitter → Carcara-checked → per-reduction proofs →
   kernel), and build the Lean tactic backend (P3.7, **fail not `sorry`**).
3. **Keystones** — incremental e-graph + CDCL(T) loop (Track 1) and the Alethe
   term/proof IR + emitter (Track 3): build-once, unlock-many.
4. **Theory depth (Track 2)** and **consumer/frontend demand-pull (Track 4 +
   consumer track)** — the latter is mature and fuzz-hardened but does **not**
   move the core decide-rate; its job is to surface real gaps (it has filed
   U6/U7/U8) and ship user-facing, certifying value, not to claim parity.
5. **The verified-systems trajectory (Track 5, ADR-0056, 2026-07-06)** — the
   application-level, seL4-inspired destination the capabilities are *for*:
   reflect compiled Rust (**rustc MIR + LLVM IR**) into `axeyum-ir` and
   discharge panic-freedom / memory-safety / constant-time / cross-IR
   translation-validation / protocol-refinement obligations **push-button, with
   replayed or certified evidence** — "Hyperkernel-style guarantees where
   *proved* is independently checkable." Prototyped green (rounds Q–U,
   2026-07-02/03: both reflectors + CFG executors, 16 cross-IR equivalence
   proofs, a 5-shape refutation corpus, exact panic specs for
   overflow/division/bounds with witnesses replayed against the real compiled
   functions, a checksum module end-to-end; millisecond proofs). Plan:
   [`docs/plan/track-5-verified-systems/`](docs/plan/track-5-verified-systems/README.md);
   definition of done in the
   [north star](docs/plan/00-north-star.md#definition-of-done--the-verified-systems-trajectory-track-5).
   Not keystone-blocked (eager pipeline suffices for v1); the standing
   measured-not-seeded rule applies doubly (P5.5 is an *external* target).

**Immediate next focus (2026-07-07 — the arithmetic arc executed + 4 soundness
bugs closed; strings breadth is now the dominant measured gap).** Since the
2026-07-06 rotation, the arithmetic levers were HARVESTED and the plan
re-ranked twice (9th + 10th reviews):
- **Arithmetic (measured, DISAGREE=0):** QF_NIA-cvc5 **21→33/39 (85%)** — congruent
  Ackermann div/mod-by-zero (#40, recovered the structural div-0 unsats), `int.pow2`
  first-class op + value-table axioms (#41, cvc5 neg-exp=0 verified from source).
  QF_NRA-cvc5 **27→32/38 (84%)** — equality-anchored decision + bignum CAD-entry
  coefficients + parser slices (#43, slices 4+7). The bounded arithmetic levers
  (div/mod-0, iand, pow2, √2) are now **harvested**; the genuine-engine NRA residue
  (~6/12: Boolean-CAD multivar, MetiTarski transcendental, degree-8/10) is the
  ADR-0058 Phase C/D arc — **DE-PRIORITIZED below strings** (10th review: Phase B
  was OBE — the DPLL→CAD edge already existed at `5ede57f4`, #43 used it).
- **Soundness (4 wrong-verdict bugs closed this arc):** the div/mod-by-const-0
  convention fold (P0, `52f3b1d1`), a pre-existing const-0 wrong-sat (caught by the
  new const-0 fuzz), `str.from_code` over 128..=0x2FFFF (#46), and FP
  `isNegative`/`isPositive` on signed zeros (#50, wrong-UNSAT). **The partial-operator
  Hard Rule is now an ENFORCED per-op fuzz-coverage checklist** (#42,
  `docs/research/01-foundations/underspecified-operator-fuzz-coverage.md`); every
  bug was surfaced the instant a differential fuzz could see the degenerate shape.
- **Lean-parity:** #44 landed the **regex derivative-emptiness → kernel-checked Lean
  `False`** reconstruction (`cd6783b9`, full multi-state closure, no new kernel
  axioms; a kernel-checked narrowing). Tracker correction 2026-07-09: the live
  evidence path is already wired through `Evidence::UnsatRegexEmptiness` and the
  string unsat evidence dispatcher; the remaining Lean work is broader ledger
  coverage, not this wiring.
**The rotation NOW (post-keystone correction, 2026-07-11):** (1) **strings
breadth remains a measured gap** (QF_SLIA 18/50=36%, QF_S 87/134=65%). A scout
PROVED the
"str.++ bound-cap" census was a mis-diagnosis (raising the cap gains ~0 rows — the
cap message masks extended-function rejections). Real levers: **(1a)
membership-over-concatenation** — ✅ **#49 LANDED** (`7197da29`, QF_S 78→82: 5 rows
issue2060/5510/5520/7677/4608 unsupported→sat, sat-side slice, DISAGREE=0 z3+cvc5);
✅ **the concat-UNSAT + joint-product-automaton SAT + trivial-length-atom follow-up
LANDED** (`93c5b829`, task #55, QF_S 82→87, DISAGREE=0); **(1b) the LenAbs
length/LIA SAT bridge LANDED** (`3ac4f429`, task #53, replay-gated and
differentially clean); **(1c) quadratic word-equation certified unsat** remains
the Nielsen-arrangement keystone (ADR-0063), deliberately deferred until a
completeness-of-splits witness exists. **Fast-follow closed
2026-07-11:** the derivative-closure deadline edge now polls inside both
similarity canonicalization (`canon_within`) and derivative expansion
(`derivative_within`), including combined-regex canonicalization before the
membership solver starts. Pathological `Σ*`-enlarged intersection regressions
pin timely `Unknown` for solve/refute paths. Remaining string increments are the
measured unsupported extended-function/sequence residue plus the research-gated
Nielsen class, not the already-landed #53/#55 work.
(2) **#44/#52 regex-emptiness evidence wiring is already live** (verified in code:
`string_unsat_evidence` produces `Evidence::UnsatRegexEmptiness`, whose checker
re-runs the Lean-module reconstruction; the stale "wiring pending" note is
corrected). (3) ✅ **the #42 fuzz GAPs are CLOSED**
(FP+RealDiv-0 #47, seq.nth #51 — only low-risk GAP-BV1 remains). (4) ✅ **CdclT
arithmetic migration LANDED** (ADR-0055/0060; LIA/LRA TheorySolver adapters and
default dispatch). The active post-keystone depth target is P2.6 quantified
model/counterexample instantiation, with proof integration in the same increment.
**Euclidean-residue UNSAT evidence is LANDED (ADR-0095):** `clock-3`/`clock-10`
carry a separate original-IR structural certificate with zero trust steps.
**Restricted infinite-domain SAT replay is now LANDED (ADR-0096):** `Model`
carries deterministic typed Skolem certificates, and canonical `check_model`
independently re-matches/substitutes the exact `forall* exists` assertion and
proves only affine/reflexive tautologies. This recovers `issue4849-nqe` by
`b:=a` without pretending the ground evaluator can enumerate `Int`. Fresh
quantified-LIA measurement is **5/12** (sat 1, unsat 4), DISAGREE=0, errors and
replay failures 0. The five-decision audit is evidence-certified 3/5 and
rechecked 5/5; the SAT row has zero trust holes, but Lean UNSAT remains 0/4 and
two UNSAT rows are bare, so no division-level dominance claim is made.
**Positive-slope affine-growth CEGQI is now LANDED (ADR-0097):** two consecutive
instances above `div(else+threshold, coefficient)` refute the exact piecewise
universal, while a separate original-IR checker carries zero-trust evidence.
The measured slice is now **6/12** (sat 1, unsat 5), DISAGREE=0, with 4/6
certified and 6/6 rechecked; Lean UNSAT remains 0/5 and the two older bare UNSAT
rows still block division dominance. A satisfiable near-miss sweep also exposed
and closed a legacy trigger-instantiation termination defect: duplicate
cartesian instances from unused binders are deduplicated and folded as a
balanced conjunction instead of an exponential repeated tree. The same
aggregate validation repaired one post-keystone AUFBV invariant: nested
`!ext_eq_*` flags are now registered in stable order before e-graph explanations
can guard dynamic interface clauses. Final static/resource gates are green; the
serialized CI-mode aggregate passed through the hardware-relative frontier and
the two longest differential fuzzers, then was stopped when the pre-existing
`sturm_overflow_declines_gracefully` test failed to terminate after 30 minutes
(recorded precisely in STATUS, not claimed as a full pass). Six quantified-LIA
rows remained at that checkpoint.
**Guarded unit-gap Skolem SAT is now LANDED (ADR-0098):** untrusted search may
pull one direct positive `or`-nested existential, while a separate checker
re-matches the untouched original theorem
`upper <= lower+1 or exists z. lower<z<upper` over `Int`/`Real` and checks the
global `z:=lower+1` witness. The certificate now owns an arena-stable affine
recipe over original-arena atoms, closing the clone-local `TermId` replay defect
found by the benchmark lifecycle. Target/Real/tamper/margin/polarity and
untouched-arena tests pass; a 64-seed static-Z3 sweep plus 32 integer negatives
has DISAGREE=0. Fresh release measurement is **7/12** (sat 2, unsat 5, unknown
1, unsupported 4), DISAGREE=0, errors/replay failures 0. The seven-decision
audit checks 7/7, certifies 5/7, and marks both SAT rows dominant candidates;
Lean UNSAT remains 0/5 and two bare UNSAT rows still block division dominance.
At that checkpoint five rows remained: four large/nested Boolean universals
were unsupported and nested-QE UNSAT `issue4433-nqe` was incomplete.
**Checked nested-XOR hierarchical instantiation is now LANDED (ADR-0099):** at
the two outer selector pivots, the first XOR is false and exposes the positive
nested universal; one off-pivot inner instance then equates distinct integer
constants. Search proposes that genuine consequence and requires an ordinary
QF refutation, while a separate original-IR checker independently re-matches
the exact two-outer/one-inner theorem. Target/tamper/signed-constant/order/
structure/polarity tests and a 64-UNSAT + 64-SAT static-Z3 sweep pass. Fresh
release measurement is **8/12** (sat 2, unsat 6, unknown 0, unsupported 4),
DISAGREE=0, errors/replay failures 0. The eight-decision audit checks 8/8 and
certifies 6/8; `issue4433-nqe` carries zero-trust
`int-nested-xor-unsat` evidence. Lean UNSAT remains 0/6. No rows remain
incomplete. Next, work directly on the Pareto evidence debt: certify the two
older bare UNSAT rows `ARI176e1` and `issue5279-nqe`, then return to the four
unsupported Boolean-heavy universals. Decide-rate ~74% and climbing.
**Evaluator-replayed closed-universal evidence is now LANDED (ADR-0100):**
untrusted QF search may discover a concrete falsifying assignment for a closed
quantifier-free scalar universal, but the certificate carries only original
binder IDs and typed values. A separate checker rejects open/nested/UF forms and
evaluates the untouched original body, accepting only `Bool(false)`. This
upgrades `ARI176e1` and `issue5279-nqe`; the fresh eight-decision audit is now
checked **8/8** and certified **8/8**, with empty trust ledgers, DISAGREE=0, and
no errors/timeouts. Lean UNSAT remains 0/6, so no division-level Pareto claim is
made. Next, return to the four unsupported Boolean-heavy universals while
keeping Lean reconstruction as the proof-parity lane.
**Next-action census:** `cbqi-sdlx-fixpoint-3-dd` is the bounded first target:
its nested quantified integers occur only in equality-to-constant predicates,
so a checked finite partition (each mentioned constant plus one deterministic
other representative) is exact. The other three rows are 299–422-line affine
`ite` networks with 40–50 mixed binders; two are SAT and require general model
construction, while the UNSAT row requires scalable CEGQI. Do not claim the
finite-partition slice addresses that broader engine gap.
**Checked finite equality-partition quantifiers are now LANDED (ADR-0101):**
for a closed nested Bool/Int formula, every Int binder occurrence must be a
direct equality against an explicit constant. Those constants plus one
deterministic other value form an exact behavioral quotient. Search expands the
quotient in a clone; a separate checker recursively evaluates the untouched
original formula and enforces a 2^20 representative-case cap. This decides
`cbqi-sdlx-fixpoint-3-dd`: fresh release measurement is **9/12** (sat 2,
unsat 7, unsupported 3), DISAGREE=0, errors/replay failures 0; audit is checked
and certified **9/9** with zero trust holes. At that checkpoint Lean UNSAT was
0/7. The engine frontier is general quantified model construction for the two
large SAT affine-ITE rows and scalable CEGQI for the remaining large UNSAT row;
do not extrapolate the finite quotient beyond its checked occurrence discipline.
**Closed-universal counterexamples now reconstruct to Lean (ADR-0102):** the
ADR-0100 certificate is rechecked, the untouched universal is encoded as nested
dependent products over the existing Int/Bool preludes, and the carried
witnesses are applied before kernel-checked integer normalization closes
`False`. `ARI176e1` and `issue5279-nqe` therefore move the nine-decision audit
from Lean UNSAT 0/7 and 2 dominant candidates to **Lean UNSAT 2/7 and 4/9
dominant candidates**, with evidence still checked/certified 9/9 and no
mismatch, timeout, audit error, or trust hole. This route adds no
certificate-specific refuter axiom. The other five UNSAT certificate families
remain honestly uncredited; their composed instantiation/arithmetic proofs are
the next proof-parity lane alongside the three-row engine frontier.
Focused all-feature tests pass 3/3 (the optional real-Lean subprocess check
skipped because no `lean` binary is installed); solver lib 829/829, evidence
69/69, bench 7/7, capability/support goldens, workspace Clippy,
warning-denied rustdoc, links, formatting/diff, and foundational resources are
green. The pre-existing Sturm nontermination still prevents a whole-workspace
aggregate claim.
**Nested-XOR quantifiers now reconstruct to Lean (ADR-0103):** the ADR-0099
certificate is regenerated against the untouched assertion, the two outer
pivots and one adjacent nested witness are applied as genuine universal
instantiations, and kernel-checked `Iff`/XOR reasoning plus integer normalization
closes `False`. The route covers signed constants and either checked child/
equality orientation, and adds no theorem-specific refuter or arithmetic axiom.
The fresh audit moves to **Lean UNSAT 3/7 and 5/9 dominant candidates**, while
evidence remains checked/certified 9/9 with no mismatch, timeout, audit error,
or trust hole. Remaining proof debt is four rows: two Euclidean-residue,
affine-growth, and finite equality-partition certificates.
Focused all-feature 3/3, solver lib 829/829, evidence 69/69, bench 7/7,
capability/support goldens, workspace Clippy, warning-denied rustdoc, links,
formatting/diff, and foundational resources are green. The known pre-existing
Sturm nontermination still prevents a whole-workspace aggregate claim.
**Euclidean-residue quantifiers now reconstruct to Lean (ADR-0104):** the
trusted integer prelude explicitly gains one standard theorem stating
existence of quotient/remainder decomposition for a positive modulus, without
adding div/mod operations. The canonical `clock-3`/`clock-10` hypotheses are
instantiated with those existential witnesses; recomposition and both bounds
refute their three disjuncts through kernel-checked equality/order reasoning.
Certificate regeneration, exact theorem-type inference, both real rows,
tampered modulus, and a satisfiable weakened-bound control pass. The fresh
release audit moves to **Lean UNSAT 5/7 and 7/9 dominant candidates**; evidence
remains checked/certified 9/9 with no mismatch, timeout, audit error, or trust
hole. This is a documented trusted-base expansion, not a query-specific
refuter axiom. Remaining proof debt is `repair-const-nterm` affine growth and
`cbqi-sdlx-fixpoint-3-dd` finite equality partition. Next, test whether the same
Euclidean theorem closes the affine-growth certificate before designing the
more general finite-partition proof. Focused all-feature reconstruction 3/3,
integer prelude 6/6, solver lib 829/829, evidence 69/69, bench 7/7,
capability/support goldens 2/2 and 12/12, workspace Clippy, warning-denied
rustdoc, links, formatting/diff, and 137-concept/174-pack foundational resources
are green. No whole-workspace aggregate is claimed because of the known
pre-existing Sturm nontermination.
**Affine-growth quantifiers now reconstruct to Lean (ADR-0105):** the complete
checked ADR-0097 class is encoded with every original Int binder and exact
guarded proposition semantics for its integer `ite`. ADR-0104 decomposition of
`b+t`, `r<c`, and positive-slope monotonicity prove the comparison at two
consecutive candidates. Each guarded instance yields a double-negated pivot
equality; strict consecutiveness closes them constructively, with no classical
axiom or additional arithmetic theorem. The real ten-binder
`repair-const-nterm`, signed/swapped multi-binder class member, tampered
certificate, and binder-dependent near miss pass. Fresh audit is evidence
checked/certified **9/9**, Lean UNSAT **6/7**, and **8/9 dominant candidates**,
with no mismatch, timeout, audit error, or trust hole. Finite equality partition
(`cbqi-sdlx-fixpoint-3-dd`) is now the sole current UNSAT proof gap. Next, derive
the smallest general equality-partition theorem/proof scheme needed to close it
without turning ADR-0101's executable evaluator into an opaque refuter. Focused
all-feature reconstruction 4/4, solver lib 829/829, evidence 69/69, bench 7/7,
capability/support goldens 2/2 and 12/12, workspace Clippy, warning-denied
rustdoc, links, formatting/diff, and 137-concept/174-pack foundational resources
are green. No whole-workspace aggregate is claimed because of the known
pre-existing Sturm nontermination.
**Single-pivot equality partitions now reconstruct to Lean (ADR-0106):** the
ADR-0101 certificate is rechecked against untouched IR, then a recursive proof
engine retains every genuine Bool/Int quantifier and exact guarded `ite`
proposition. Arbitrary Bool witnesses split through `Bool.rec`; arbitrary Int
witnesses split on one explicit standard `IntPrelude::eq_em` theorem. The finite
quotient evaluator only guides proof search and is never admitted. The real
`cbqi-sdlx-fixpoint-3-dd` target, quantifier/polarity/connective controls,
tampered case count, multi-constant boundary, and arithmetic declines pass.
Fresh audit is evidence checked/certified **9/9**, Lean UNSAT **7/7**, and
**9/9 dominant candidates**, with no mismatch, timeout, audit error, or trust
hole. This gives complete Pareto proof credit to every decided row, not
division-wide dominance: decide-rate remains **9/12**, and the three large
affine-ITE rows still require scalable CEGQI and general quantified model
construction. Multi-constant equality partitions remain a separate proof
extension. At that checkpoint, the next depth-first engine target was
symbolic/lazy treatment of those three rows; the rejected concrete-tuple
prototype below was not to be repeated.
Focused all-feature reconstruction 5/5, integer prelude 7/7, solver lib 829/829,
evidence 69/69, bench 7/7, capability/support goldens 2/2 and 12/12, workspace
Clippy, warning-denied rustdoc, links, formatting/diff, and
137-concept/174-pack foundational resources are green. No external Lean binary
is installed, and no whole-workspace aggregate is claimed because of the known
pre-existing Sturm nontermination.
**Checked Boolean-guard quantified models are now LANDED (ADR-0107):** a
quantifier-erased QF skeleton proposes only a free-Boolean candidate. Replay
keeps the untouched original assertion, exhaustively checks bounded Boolean
structure or drops only positive universal binders, exactly lifts integer
`ite`, and requires a source-bound LIA-DPLL refutation of the negated closure.
Theory cores are rechecked; large propositional closures carry source-matched
DIMACS/DRAT. Concrete counterexamples generalize sufficient Boolean blocking
cubes but never grant SAT. This recovers `015-psyco-pp` and `psyco-196`: fresh
release measurement is **11/12** (sat 4, unsat 7, unsupported 1), with
DISAGREE=0 and no replay failure. The audit is checked/certified **11/11**, Lean
UNSAT **7/7**, and **11/11 dominant candidates**, with no mismatch, timeout,
audit error, or trust hole. The sole remaining row is UNSAT `006-cbqi-ite`;
the next depth-first target is symbolic tuple synthesis or clause-level/lazy
quantifier evaluation for that row, not SAT model construction and not another
concrete 40--50-component tuple loop.
Focused default/all-feature integration 6/6, solver lib 830/830, evidence
69/69, bench 7/7, capability/support goldens 2/2 and 12/12, workspace
all-target/all-feature Clippy, warning-denied rustdoc, links, formatting/diff,
and 137-concept/174-pack foundational resources are green. No external Lean
binary is installed, and no whole-workspace aggregate is claimed because of the
known pre-existing Sturm nontermination.
**Rejected next prototype:** exact top-level conjunction flattening plus
model-fixed multi-binder QF counterexample tuples made `006-cbqi-ite` engage the
CEGQI loop, but 8 rounds still returned unknown in 8.2 s and 32 rounds exhausted
a shared 30 s deadline. The code was reverted. One concrete 40--50-component
tuple per round is not the Pareto lever; pursue symbolic tuple synthesis,
clause-level/lazy quantifier evaluation, or the SAT-side model program instead.
**Checked quantified counterexample covers are now LANDED (ADR-0108):** search
weakens positive universals only for candidate generation, obtains concrete
falsifying Bool/Int binder models, and retains sufficient cubes of original
free-Boolean values. The independent checker regenerates every exact source
instance, source-bound-refutes cube plus instance through LIA-DPLL/DRAT, and
separately refutes the weakened original skeleton plus every cube block. The
final `006-cbqi-ite` row carries 119 cases (maximum cube width 6), solves in
about 1.2 s, and has empty trust steps. Its first Lean slice applies the one
original universal leaf to each carried tuple and closes a deterministic,
100,000-node-capped excluded-middle tree with signed Boolean and normalized
integer proofs. Fresh audit is **12/12 decided, certified, checked, and
dominant**, Lean UNSAT **8/8**, with DISAGREE=0 and no mismatch, replay failure,
audit error, timeout, or trust hole. The initial target kernel reconstruction
took about 17.7 s and rendered about 152 MB; this baseline motivated ADR-0109.
Focused default/all-feature
tests pass 5 normal + 1 explicit release validation, solver lib 830/830,
evidence 69/69, bench 7/7, capability/support goldens 2/2 and 12/12, workspace
all-target/all-feature Clippy, warning-denied rustdoc, links, formatting/diff,
and 137-concept/174-pack foundational resources are green. No external Lean
binary or whole-workspace aggregate is claimed.
**Closed proof-DAG sharing is now LANDED (ADR-0109):** the legacy Lean renderer
remains unchanged, while an opt-in compact module path counts occurrences over
the hash-consed proof DAG and names only repeated compound expressions with no
loose de Bruijn variables or free locals. Definitions are emitted
child-before-parent with deterministic names and a 16,384-share cap.
ADR-0108 additionally exports computational `Bool` as a real Lean inductive so
its recursor computes in the destination kernel. The `006-cbqi-ite` module
shrinks **151,845,067→2,682,977 bytes (98.23%)** and release reconstruction
**17.74→10.75 s (39.43%)**, while the fresh audit remains 12/12
checked/certified/dominant and 8/8 Lean UNSAT with zero mismatch, timeout,
error, replay failure, or trust hole. The release regression enforces a <3 MB,
real-`Bool`, shared, `sorryAx`-free artifact; renderer tests reject open-term
hoisting. Lean kernel 154/154, solver lib 830/830, evidence 69/69, bench 7/7,
capability/support goldens 2/2 and 12/12, workspace all-target/all-feature
Clippy, warning-denied rustdoc, links, formatting/diff, and
137-concept/174-pack foundational resources are green. No external Lean binary
is installed and no whole-workspace aggregate is claimed because of the known
Sturm nontermination. Next P2.6 depth work is the
general lazy clause-evaluation/MAM path, followed by alternation and
quantified-UF model/evidence boundaries; open-context lambda lifting is
measurement-gated rather than the next blocker.
**Justified lazy quantifier-clause scheduling is now LANDED (ADR-0110):** the
e-matching loop reuses its congruence-closed bridge to three-value
equality/disequality clauses from recorded ground units. Any-true instances are
suppressed; all-false and one-undetermined complete source instances run before
unresolved/non-clausal fallback. It never asserts a detached literal without
its false-sibling justifications, and the public witness/evidence APIs remain
complete. A 256-match target schedules one instance and improves five-run
release median batch-plus-QF time **4.237→2.524 ms (40.4%)**. The 54-row
quantified-BV division is decision-identical to baseline, quantified LIA remains
12/12, and direct quantified-BV Z3 fuzz has zero disagreement. Solver lib
833/833, the 900-seed soundness sweep, focused evidence/MBQI, workspace Clippy,
warning-denied rustdoc, links, formatting/diff, generated matrices, and
foundational-resource gates pass. The 2,000-case quantified-UFLIA debug fuzz
was stopped CPU-active after 15 minutes/1.3 GB, so no pass is claimed. ADR-0111
subsequently lands T2.6.1's shared matching-state slice.
**Shared incremental e-matching state is now LANDED (ADR-0111):** one quantified
refutation attempt infers triggers once, interns identical recursive patterns,
extends one ground e-graph only with appended source instances/equalities, and
executes all unique patterns against one batched class/application index per
round. Public one-shot witness APIs and complete-source evidence are unchanged.
On 32 quantifiers over 256 ground applications, the shared session returns the
same 8,192 ordered tuples while five-run release median matching improves
**17.477→0.974 ms (94.4%, 17.9x)**. The retained two-round chain replays UNSAT;
the 54-row quantified-BV division is decision-identical with PAR-2 within
0.03%, and isolated quantified-LIA median is within 0.34% while remaining
12/12. E-graph 27/27, solver lib 834/834, evidence 69/69, bench 7/7, the
900-seed soundness sweep, direct Z3 fuzz, workspace Clippy, warning-denied
rustdoc, links, formatting/diff, generated matrices, and foundational resources
pass.
**Revision-checked indexes and add-only candidate queues are now LANDED
(ADR-0112):** retained e-match indexes extend class/application maps from new
node suffixes, and root-symbol queues rematch only patterns that can gain an
application match. Real e-class merges and scope rollback revision-invalidate
root-keyed data; merge rounds conservatively rebuild and rematch all patterns.
On 64 unrelated roots over 4,096 retained applications, appending one
application preserves every complete tuple while executing 1 instead of 64
patterns; five-run release median is **2.555→0.311 ms (87.8%, 8.2x)** including
index refresh and tuple joins. The 54-row cvc5 quantified-BV slice remains
decision-identical with PAR-2 7.46905 s, quantified LIA remains 12/12 across
three runs, and 1,000 direct-Z3 quantified-BV cases have zero disagreement.
E-graph 30/30, e-matching 31/31, solver lib 835/835, evidence 69/69, MBQI 13/13,
bench 7/7, and the 900-seed soundness sweep pass.
**Inverted-parent selective merge queues are now LANDED (ADR-0113):** every real
union, including congruence cascades, enters a deterministic journal consumed by
retained match indexes without a graph rebuild. Changed equality endpoints walk
transitive e-class parents to queue only reachable trigger roots; cached and
multi-pattern substitutions compare current roots. Raw application retention
also fixes the existing completeness edge where explicitly equal `f(a)` and
`f(b)` still require both bindings when `a` and `b` are unequal. Direct,
repeated-variable, nested, ground-subpattern, add-plus-merge, application-class,
cycle, rollback, and full-rematch parity gates pass. On 64 roots over 4,096
applications, a one-root merge executes 1 instead of 64 patterns and improves
five-run optimized complete-round median **2.231→0.151 ms (93.2%, 14.8x)**.
The cvc5 quantified-BV slice is decision-identical at PAR-2 7.46912 s;
quantified LIA remains 12/12 with three-run median 0.11713 s; 1,000 direct-Z3
and 900 bounded-instance cases have zero disagreement. E-graph 33/33,
e-matching 37/37, solver lib 841/841, evidence 69/69, MBQI 13/13, and bench 7/7
pass.
**Compiled exact parent-path tries are now LANDED (ADR-0114):** every interned
pattern occurrence contributes child-to-root `(declaration, argument-index)`
steps to one shared flat trie. Merge lookup pairs current e-class roots with
trie states and follows only compatible parent arguments; visited state pairs
make recursive equalities cycle-safe, and terminals are sorted/deduplicated.
The operator add queue and current-root cached joins are unchanged. Direct,
nested, repeated, ground, add-plus-merge, equal-application, duplicate path,
shared-prefix, divergent declaration/argument, multiple-start, cycle, and
full/declaration-rematch parity gates pass. On 64 patterns sharing one outer
root over 4,096 applications, one nested path executes 1 instead of 64 patterns
and improves five-run optimized complete-round median **12.777→0.386 ms (97.0%,
33.1x)**. cvc5 quantified BV is unchanged at PAR-2 7.46935 s; quantified LIA
remains 12/12 with three-run median 0.11791 s; 1,000 direct-Z3 and 900 bounded
cases agree. E-graph 33/33, e-matching 40/40, solver lib 844/844, evidence 69/69,
MBQI 13/13, and bench 7/7 pass. **Next actions:** measure class-label and
ground-argument filters, then relevance/generation controls; bytecode remains
gated on beating the recursive compiled matcher. Then add replayable
false-sibling justifications for detached-literal propagation. Alternation/QSAT
and quantified-UF function-model/evidence boundaries follow.
**Exact class-label and nullary ground-argument filters are now LANDED
(ADR-0115):** e-class roots retain sorted declaration sets through direct and
congruence unions and rollback. Exact-path terminals require the changed start
class to contain a nested occurrence's top declaration, and transitions may
require one direct nullary ground sibling; compound ground siblings remain
unfiltered. A matrix with 64 same-shape patterns and 4,096 applications reaches
64/8/8/1 terminals in unfiltered/class-only/ground-only/combined modes while
returning identical tuples. Five-run optimized medians are
**13.453/2.314/1.991/0.404 ms**; combined filtering reduces complete-round time
97.0% (**33.3x**). cvc5 quantified BV remains 29 SAT / 9 UNSAT / 5 unknown / 11
unsupported with zero mismatches/errors/replay failures and PAR-2 7.46935 s;
quantified LIA remains 12/12 with three-run median 0.11882 s. All 1,000
direct-Z3 and 900 bounded-instance cases agree; the known Bitwuzla SAT replay
rejection remains beside four expected UNSAT rows. E-graph 34/34, e-matching
41/41, solver lib 845/845, evidence 69/69, MBQI 13/13, and bench 7/7 pass.
**Next actions:** add and independently measure relevance/generation controls;
bytecode remains gated on beating the recursive compiled matcher. Then add
replayable false-sibling justifications for detached-literal propagation.
Alternation/QSAT and quantified-UF function-model/evidence boundaries follow.
**Generation-delta top-application queues are now LANDED (ADR-0116):** the
initial pattern scan remains complete, then add rounds queue newly created root
applications and merge rounds queue ADR-0115-filtered path terminals. Candidate
matching uses the same recursive class matcher and appends to monotonic caches;
joins and witness lifting canonicalize current roots. The current bridge contains
only active asserted terms and their subterms, so a separate relevance bit would
filter nothing. On one affected pattern over 4,096 outer applications, full and
delta routes scan 4,096 versus 1 top application and return identical tuples;
five-run optimized complete-round median improves **0.370→0.122 ms (67.0%,
3.03x)**. cvc5 quantified BV remains 29 SAT / 9 UNSAT / 5 unknown / 11
unsupported with zero mismatches/errors/replay failures and PAR-2 7.46919 s;
quantified LIA remains 12/12 with three-run median 0.11828 s. All 1,000
direct-Z3 and 900 bounded-instance cases agree; the known Bitwuzla SAT replay
rejection remains beside four expected UNSAT rows. E-graph 35/35, e-matching
42/42, solver lib 846/846, evidence 69/69, MBQI 13/13, and bench 7/7 pass.
**Next actions:** add replayable false-sibling justifications for detached-literal
propagation. Generation-cost scheduling and bytecode remain separately
measurement-gated; alternation/QSAT and quantified-UF function-model/evidence
boundaries follow.
**Source-bound checked detached quantifier literals are now LANDED (ADR-0117):**
a public arena-bound certificate carries the untouched universal, ordered
binding tuple, exact complete instance, detached equality/disequality literal,
and every false sibling's sorted original-ground reasons. A batch checker builds
one fresh source context, reconstructs every instance, and independently replays
each reason subset before a detached term enters QF search. Generated-premise
reasons decline to complete source instances. On 128 matches with six false
siblings, reachable DAG nodes fall **4,230→2,438 (42.4%)** and tree nodes
**10,121→4,745 (53.1%)**; five-run optimized QF median improves
**8.250→3.226 ms (60.9%, 2.56x)** and checked end-to-end median
**11.301→9.886 ms (12.5%, 1.14x)**. cvc5 quantified BV remains 29 SAT / 9
UNSAT / 5 unknown / 11 unsupported with zero mismatches/errors/replay failures
and PAR-2 7.46892 s; quantified LIA remains 12/12 with three-run median 0.11825
s. All 1,000 direct-Z3 and 900 bounded-instance cases agree; the known Bitwuzla
SAT replay rejection remains beside four expected UNSAT rows. E-graph 35/35,
e-matching/propagation 47/47, solver lib 851/851, evidence 69/69, MBQI 13/13,
and bench 7/7 pass. **Next actions:** add recursive source-instance provenance
for generated false-sibling reasons, then reuse the checked implication in the
online CDCL(T) clause path. Non-equality theory literals and proof-format
serialization follow; generation-cost scheduling/bytecode remain measured
separate work.
**Bounded recursive quantifier ground provenance is now LANDED (ADR-0118):**
every admitted generated equality/disequality retains either its exact
universal-instance certificate or the prior checked detached propagation that
concluded it. The public checker reconstructs every substitution, requires the
exact sorted derivation table for non-source named reasons, recursively replays
prior implications under depth-16/node-4,096 caps, and rejects missing,
duplicate, unused, reordered, wrong-variant/conclusion, and nested-tampered
artifacts to complete-instance fallback. A six-stage target preserves UNSAT
while reachable DAG nodes fall **54→17 (68.5%)** and tree nodes **117→33
(71.8%)**. cvc5 quantified BV remains 29 SAT / 9 UNSAT / 5 unknown / 11
unsupported with zero mismatches/errors/replay failures and PAR-2 7.46909 s;
quantified LIA remains 12/12 with three-run median 0.11756 s. All 1,000
direct-Z3 and 900 bounded-instance cases agree; the known Bitwuzla SAT replay
rejection remains beside four expected UNSAT rows. E-graph 35/35,
e-matching/propagation 52/52, solver lib 856/856, evidence 69/69, MBQI 13/13,
and bench 7/7 pass. Workspace Clippy/rustdoc, links, foundational resources,
formatting/diff, generated matrices, and all 26 reference checkouts pass.
**Next action:** reuse this checked implication in the
online CDCL(T) quantifier-clause path. Non-equality antecedents and proof-format
serialization follow; generation-cost scheduling/bytecode remain separate
measured work.
**Checked quantifier clauses in retained CDCL(T) are now LANDED (ADR-0119):**
the original ground Boolean/equality skeleton is encoded once; every generated
batch backtracks SAT/theory state to level zero, independently rechecks its
exact-instance or recursive derivation, appends new equality atoms in root
scope, and adds the clause permanently while retaining learned clauses, VSIDS,
and phases. Online SAT only resumes matching, and online UNSAT returns a product
verdict only after ordinary QF replay refutes the exact admitted ground set.
Unsupported, tampered, mismapped, and over-budget sessions fall back. A
six-stage target cuts complete QF rebuilds **7→2** and five-run optimized median
time **0.560→0.351 ms (37.3%, 1.60x)**. cvc5 quantified BV remains 29 SAT / 9
UNSAT / 5 unknown / 11 unsupported with zero disagreement/error/replay failure
and PAR-2 7.47183 s; quantified LIA remains 12/12 with three-run median 0.11770
s. All 1,000 direct-Z3 and 900 bounded-instance cases agree; Bitwuzla retains
four expected UNSAT rows plus its known SAT replay alarm. Solver 861/861,
evidence 69/69, MBQI 13/13, and bench 7/7 pass. **Next action:** measure and
design SAT-trail-driven matching callbacks so newly assigned equality literals
can queue only affected quantifier work. Non-equality antecedents and online
proof serialization remain separate trust-boundary increments;
generation-cost scheduling/bytecode remain measurement-gated.
**Scoped SAT-candidate equality e-matching is now LANDED (ADR-0120):** at an
ordinary source-matching fixpoint, true equality atoms from the retained SAT
candidate are merged only in one temporary matching-e-graph scope. Exact merge
paths execute affected patterns, a reverse index joins only their quantifiers,
and concrete tuples are materialized before pop. Candidate equalities never
become reasons/evidence; only complete exact source instances enter ADR-0119,
and product UNSAT still requires ordinary QF replay. A nested-trigger target
moves **Unknown→UNSAT** and improves five-run optimized median
**0.573→0.148 ms (74.2%, 3.87x)**. A 64-pattern target executes/scans 1
pattern/application versus 64, returns the same tuple, and improves median
**5.478→4.329 ms (21.0%, 1.27x)**. cvc5 quantified BV remains 29 SAT / 9
UNSAT / 5 unknown / 11 unsupported with zero disagreement/error/replay failure
and PAR-2 7.47178 s; quantified LIA remains 12/12 with median 0.11852 s. All
1,064 direct-Z3 and 900 bounded-instance cases agree; Bitwuzla retains four
expected UNSAT rows and its known SAT replay alarm. Solver 863/863, e-matching
57/57, evidence 69/69, MBQI 13/13, and bench 7/7 pass. **Next action:** attack
the measured nested/alternating BV frontier, starting with `issue4328-nqe`:
extend the checked quantified-SAT Skolem contract to the exact
`forall a:BV32. exists b:BV32. bvsle a b` theorem with reflexive `b:=a`
replay. All 16 remaining public BV blockers are nested/existential; non-equality
online antecedents and high-frequency callbacks do not currently move that
decide-rate frontier. Online proof serialization remains the parallel trust
lane.
**Checked reflexive bit-vector Skolem witnesses are now LANDED (ADR-0121):**
`AffineSkolemWitness` has exactly one BV interpretation: a same-width universal
variable with coefficient one and zero offset. A separate original-assertion
checker substitutes that identity and accepts only reflexive `bvsle`/`bvule`
(plus equality); modular affine, composite, offset, foreign, width-mismatched,
and tampered recipes decline. Certificate replay precedes finite enumeration,
closing a width-16 combinatorial replay defect exposed by the new matrix.
`issue4328-nqe` moves **Unknown→SAT** with five-run optimized median 0.008736
ms. The cvc5 quantified-BV slice moves **29/9/5/11→30 SAT / 9 UNSAT / 4
unknown / 11 unsupported**, DISAGREE=0, no errors/replay failures, and five-run
PAR-2 median 7.00692 s. The audit checks/certifies 39/39; the target has empty
trust and is dominant (division 38/39 dominant, Lean UNSAT 8/9). All 1,128
direct-Z3 and 900 bounded-instance cases agree. Quantified LIA remains 12/12;
Bitwuzla is 5/5 with no replay failure. Solver 863/863, witness 14/14,
certificate 12/12, evidence 69/69, MBQI 13/13, bench 7/7, and all static,
documentation, resource, matrix, and 26-reference gates pass. **Next action:**
attack `issue5365-nqe` through a checked free-BV guard model: choose the outer
existential `a != 0` and independently prove that the untouched deeply nested
implication is vacuous. General BV QE remains a later frontier, not the first
implementation choice for this measured row.
**Checked vacuous bit-vector guard models are now LANDED (ADR-0122):** a
dedicated certificate carries one exact-width outer BV existential witness. Its
independent original-IR checker requires a nonempty direct unique Bool/BV
quantifier prefix, a root implication, and an antecedent equating that exact
binder with one same-width constant; the witness must differ from the constant,
so the consequent is irrelevant. `issue5365-nqe` moves **Unknown→SAT** with
five-run optimized median 0.004147 ms. The cvc5 quantified-BV slice moves to
**31 SAT / 9 UNSAT / 3 unknown / 11 unsupported**, DISAGREE=0, no errors or
replay failures, and five-run PAR-2 median 6.54204 s. The audit certifies/checks
40/40, with 39/40 dominant; the target has empty trust. All 1,192 direct-Z3
cases/controls agree. Quantified LIA remains 12/12 and Bitwuzla remains 5/5.
ADR-specific suites and all static/documentation/resource gates pass. The full
workspace run retains one independent open performance ratchet:
`frontier_bv_reduction` measures 28 against committed baseline 30 even in
isolation; do not lower that baseline without understanding the regression.
**Next action:** attack `model_6_1_bv` by extending checked free-Boolean model
replay to the exact Boolean branch that makes its untouched quantified-BV body
globally true. General free-BV models and QE/QSAT were later frontiers at this
checkpoint; ADR-0130 subsequently closes the affine-LSB/direct-witness slice.
**Checked Boolean discharge of quantified BV closures is now LANDED
(ADR-0123):** ADR-0107's independent three-valued checker now admits
Bool/Int/BV syntax while keeping non-reflexive BV predicates opaque. A complete
free-Boolean assignment must prove the untouched closure true independently of
every BV value; unresolved BV closures decline before LIA fallback.
`model_6_1_bv` moves **Unknown→SAT** with five-run optimized median 0.064489 ms.
The cvc5 quantified-BV slice moves to **32 SAT / 9 UNSAT / 2 unknown / 11
unsupported**, DISAGREE=0, no errors/replay failures, and five-run PAR-2 median
6.07677 s. The audit certifies/checks 41/41, with 40/41 dominant; the target is
`quantified-bool-model-sat` with empty trust. All 1,256 direct-Z3 cases and
controls agree. Quantified LIA remains 12/12 and Bitwuzla remains 5/5. **Next
action:** attack `small-pipeline-fixpoint-3`, the smaller remaining UNSAT unknown
(235 DAG nodes versus `bug802`'s 3,317), through a checked finite-state
fixpoint/transition refutation rather than full 32-bit binder enumeration.
**Source-bound BV alternation counterexamples are now LANDED (ADR-0124):** a
closed unique Bool/BV `forall+ exists+` implication with an outer-only
antecedent may carry concrete outer values plus a DRAT/LRAT refutation of the
exact source-instantiated residual QF_BV matrix. Search is untrusted and uses
deterministic one-binder perturbations; replay repeats prefix checks,
substitution, existential freshening, CNF regeneration, and proof checking.
`small-pipeline-fixpoint-3` moves **Unknown→UNSAT** with five-run optimized
median 63.692 ms. The cvc5 quantified-BV slice is now **32 SAT / 10 UNSAT / 1
unknown / 11 unsupported**, 42 agreements, DISAGREE=0, no errors/replay
failures, and five-run PAR-2 median 5.613350 s. The audit certifies/checks 42/42
with 40/42 dominant, Lean 8/10 UNSAT, target taxonomy
`bv-alternation-counterexample-unsat`, and empty trust. All 1,320 direct-Z3
cases/controls agree. Solver 863/863, evidence 69/69, focused alternation 4/4,
workspace Clippy/rustdoc, generated matrices, foundational resources,
rules-as-code, and links pass. The full workspace run independently fails both
`bounded_string_replace_membership_deadline` wall caps, including in an isolated
serial rerun; `just` is unavailable. The older `frontier_bv_reduction` 28/30
ratchet remains unchanged. **Next action:** characterize `bug802`, the sole
remaining cvc5 quantified-BV unknown (3,317 DAG / 5,760 tree nodes), and choose
between extending source-bound alternation search, a checked transition
invariant, or a bounded proof-producing QSAT decomposition. Keep general QSAT
and ADR-0124 Lean reconstruction explicit separate boundaries.
**ADR-0124 Lean reconstruction remains a WIP checkpoint (2026-07-13):** the
source proposition now preserves the exact outer/inner implication, the
residual Alethe tail consumes an evaluator-checked antecedent and introduces
bounded local lets, and compact export releases transient kernel lookup tables
behind a one-way read-only guard. Consecutive Lean lets are checked as one
dependent telescope to avoid quadratic zeta expansion. Kernel 167/167 and the
seven non-stress alternation tests pass, but the two public release stress tests
remain ignored and the latest 4 GiB run still allocation-failed. Therefore this
does **not** raise Lean coverage or close ADR-0124 reconstruction. Next: attribute
and reduce the remaining public export peak, then restore the full direct/router
stress equality gate before acceptance.
**ADR-0124/0125 bounded-memory Lean reconstruction is now LANDED
(2026-07-14):** compact Lean output now
streams through an `io::Write` sink before final inference, so the proof arena
and the 89 MiB source module no longer require a second in-memory copy. Free
variables associated with nested eliminator lambdas are closed in one
scope-aware shared-DAG traversal, while ordinary abstraction skips subgraphs
that do not contain a requested local. The trusted kernel now checks the open
skeleton with each marked local available only inside its owning lambda, rejects
scope escape as unbound, and returns the mechanically closed proof; complete
application spines and expected lambda types are checked without materializing
quadratic intermediate telescopes. Exact direct/router module equality is
stream-compared so the test does not retain both large strings. The public
`small-pipeline-fixpoint-3` gate passes in **81.57 s at 3,756,104 KiB peak**;
the 530-binder `bug802` gate passes in **45.28 s at 2,186,192 KiB peak**, both
under the guarded 4 GiB release envelope and with no `sorryAx`. Quantified-BV
Lean UNSAT coverage first rose **14→16/18**. ADR-0129 source
elimination/introduction is implemented and kernel-checked for identity and
generic bounded QF transfers; its public 32-bit row exposes an 86-literal,
411-premise resolution step. A
continuation-coded clause boundary and direct
unit-propagation proof now avoid materializing intermediate resolvents, cache
normalized clauses once, and pass wide-chain positive plus corrupted-conflict
kernel gates. On the public row this cuts open-proof construction from the
prior guarded OOM to about 30 seconds. A minimized public-shaped 4-bit case then
localized the final scoped `TypeMismatch`: whole-body AIG lowering was being
projected as if it were definitionally the `And` of independently lowered
leaves. The paired route now carries one structural conjunction proposition
from the untouched source axiom through elimination and reintroduction, and the
scoped close passes. With the 64/256 cap removed experimentally, the public
release proof reaches module streaming in 211.18 s at 2,062,692 KiB peak under
4 GiB, but expanded open gate propositions exceed the 14 GiB temporary
filesystem. Scope-preserving gate proposition aliases now close as explicit
dependent `let`s inside the witness scope. The trusted kernel retains each
let-bound value for zeta equality without substituting it through the full proof,
so application/type checks preserve the open DAG. The 64/256 cap is removed.
The public row exports a **106,809,049-byte** self-contained module and passes in
**19.69 s at 2,078,224 KiB peak** under 4 GiB, with genuine
`Exists.rec`/`Exists.intro` and no `sorryAx`. Quantified-BV Lean UNSAT coverage
rises **16→17/18**. Next: reuse the compact reflected-RUP and scoped-alias
boundary for ADR-0127.
**ADR-0127 Lean reconstruction is now LANDED:** the dispatcher owns one strict
conjunctive universal instance as a distinct proof fragment, rechecks its exact
source-bound certificate, projects the untouched conjunction, applies every
typed universal witness, and closes the regenerated residual with the compact
CPS Alethe boundary. Conflict-graph LRAT trimming, checked closed-clause
declarations, deferred clause aliases, and explicit logical-AIG gate `let`s keep
the proof DAG linear without turning learned clauses into axioms. The trusted
kernel's exact expression interner is compact, sharded, collision-checked, and
segmented so large proofs avoid monolithic arena reallocations. The public
`cond-var-elim-binary` release gate passes in **196.98 s** (**3:17.54 command**) at
**1,039,568 KiB peak** under the 4 GiB cap, emits a self-contained module below
the 128 MiB regression bound, contains no `sorryAx`, and matches the direct
route. Quantified-BV Lean UNSAT coverage rises **17→18/18**. The same logical
AIG sharing reduces ADR-0129's module to **18,576,938 bytes**, with its release
gate passing in **4.10--4.21 s** (the measured no-rebuild peak is **419,460
KiB**); a scoped 64 MiB reconstruction
worker also makes its full debug file pass 9/9 without relying on the harness
stack. **Next:** take the measured Glaurung CNF gate/root-emission and
duplicate-filtering slice under artifact v27's corrected production boundary;
in the depth lane, broaden nested/alternating QSAT and quantified-UF models.
**Exact source-term BV Skolems are now LANDED (ADR-0141):** the existing
`forall+ exists` certificate may carry one exact source-reachable, same-width,
quantifier-free BV term over the leading universals with coefficient one and
zero rational offset. Search proposes only the opposite source operand of
equality or non-strict BV order; the independent checker revalidates arena
membership, source reachability, sort, scope, and the untouched prefix before
substitution must make the complete body reflexive. This admits modular and
bitwise expressions plus total UF applications such as `b := f(a)` without
inventing a function table or assigning modular meaning to the affine fields.
Focused witness/certificate suites pass 17/17 and 14/14; a 64-case BV matrix
certifies all 48 intended SAT cases with no Z3 disagreement, and a 12-case
wide-BV quantified-UF matrix is jointly SAT/replayed through width 257. Strict,
detached, free-symbol, nested, and non-reflexive shapes still decline. **Next:**
broaden beyond one direct source-term existential (piecewise/multiple-dependent
Skolems or a separately checked function model) while GQ1/GQ10 still wait for
the real capture; SAT-side Lean theorem/model export remains separate.
**Scaled source-bound BV alternation is now LANDED (ADR-0125):** only the
ADR-0124 total-binder cap rises 128→1,024; the 4,096-node matrix cap and exact
source/proof replay contract are unchanged. `bug802` has 318 universal plus 212
existential Bool/BV binders; its first antecedent model yields a checked
residual refutation. It moves **Unknown→UNSAT** with optimized median 19.804 ms.
The cvc5 quantified-BV slice is now **32 SAT / 11 UNSAT / 0 unknown / 11
unsupported**, 43 agreements, DISAGREE=0, no errors/replay failures, and
five-run PAR-2 median 5.148639 s. The audit certifies/checks 43/43 with 40/43
dominant, Lean 8/11 UNSAT, target taxonomy
`bv-alternation-counterexample-unsat`, and empty trust. All 1,336 direct-Z3
cases/controls agree; focused alternation tests are 6/6 and include explicit
over-cap rejection. Solver 863/863, evidence 69/69, workspace Clippy/rustdoc,
generated matrices, links, foundational 137/174, formatting, and diff checks
pass. The independent full-workspace blocker remains the two
`bounded_string_replace_membership_deadline` wall caps reproduced during
ADR-0124; the unrelated `frontier_bv_reduction` 28/30 ratchet remains unchanged.
**Next action:** add a checked negated-existential witness
certificate for `NUM878`, `ari-syqi`, and `ari118-bv-2occ-x` (5/6/7 DAG nodes).
Each is `not (exists binders. body)` and is UNSAT when one concrete Bool/BV
witness makes the untouched body true. Search may propose the witness, but the
checker must validate the exact source shape, binding order/sorts/closure, and
evaluate the original body directly. This should convert three unsupported rows
without QSAT or full 32-bit enumeration. The remaining unsupported rows then
split into four SAT and four UNSAT broader nested/polarity classes.
**Evaluator-replayed negated-existential witnesses are now LANDED
(ADR-0126):** one exact top-level `not (exists+ body)` over at most 128 unique
Bool/BV binders and a 4,096-node closed quantifier-free body may carry complete
typed values. The checker performs no substitution, rewrite, or solver call; it
evaluates the untouched original body and accepts only `Bool(true)`. Untrusted
search freshens binders and solves the positive QF body, then must pass that
checker. `NUM878`, `ari-syqi`, and `ari118-bv-2occ-x` move
**Unsupported→UNSAT** with target medians 3/0/3 ms. The cvc5 quantified-BV slice
is now **32 SAT / 14 UNSAT / 0 unknown / 8 unsupported**, 46 agreements,
DISAGREE=0, no errors/replay failures, and five-run PAR-2 median 3.508581 s. The
audit certifies/checks 46/46 with 40/46 dominant and Lean 8/14 UNSAT; all three
targets use `negated-existential-witness-unsat` with empty trust. All 1,400
direct-Z3 cases/controls agree; focused tests are 6/6. Solver library 863/863 and
evidence 69/69, capability/support golden matrices, default pure-Rust check,
workspace Clippy/rustdoc, foundational 137/174, links, formatting, and diff
checks pass. The independent full-workspace blocker remains exactly the two
`bounded_string_replace_membership_deadline` wall caps; the unrelated
`frontier_bv_reduction` 28/30 ratchet remains unchanged. **Next action:** attack
`cond-var-elim-binary`, the smallest remaining unsupported UNSAT row (19 DAG).
Its ground premise `k_332 < k_42` falsifies the universal instance at `x=1`:
the `x != 1` branch and `not (k_332 < x*k_42)` branch are both false. Add a
source-bound open-universal counterexample certificate that checks the ground
premise plus exact instance contradiction; do not generalize this to QSAT.
**Source-bound conjunctive BV universal instances are now LANDED (ADR-0127):**
one unique `forall+` reached only through a top-level Bool conjunction may be
replaced by a complete concrete Bool/BV instance. The checker revalidates the
source path, unique prefix, binding IDs/order/sorts, 128-binder/4,096-node caps,
exact substitution, complete weakened assertion, and its regenerated QF_BV
DRAT/LRAT proof. Search is untrusted and tries defaults plus deterministic
same-sort source constants. `cond-var-elim-binary` moves
**Unsupported→UNSAT** with `x=1,y=0`. The recovered cvc5 quantified-BV slice is
**32 SAT / 15 UNSAT / 0 unknown / 7 unsupported**, 47 agreements, DISAGREE=0,
no errors/replay failures, and five-run PAR-2 median 3.008609 s. The audit
certifies/checks 47/47 with 40/47 dominant and Lean 8/15 UNSAT; the target uses
`bv-conjunctive-universal-instance-unsat` with empty trust. All 1,464 direct-Z3
cases/controls agree; focused certificate and differential tests pass. Recovery
also removed quantified preprocessing and search heuristics that lacked checked
contracts. A memoized quantified fast-path gate plus binder-context memoization
restore the bounded `str.replace`-membership deadline regressions to 0.67 s
instead of exceeding both 30 s wall caps. The unrelated
`frontier_bv_reduction` 28/30 hardware-relative ratchet remains unchanged.
**Checked vacuous-existential-prefix counterexamples are now LANDED
(ADR-0128):** one exact nonempty `exists+ forall+` Bool/BV assertion may carry a
complete universal counterexample only when a separate checker proves all
leading existential binders absent from the closed QF body. It validates unique
typed binder IDs/order, 128-binder/4,096-source-node caps, and evaluates the
untouched body directly to `Bool(false)`. Untrusted search freshens only the
universal block and must pass that checker. `issue2031-bv-var-elim` moves
**Unsupported→UNSAT** with five-run target median 0.129 ms. The fresh cvc5
quantified-BV slice is **32 SAT / 16 UNSAT / 0 unknown / 6 unsupported**, 48
agreements, DISAGREE=0, no errors/replay failures, and five-run PAR-2 median
2.529213 s. The audit certifies/checks 48/48 with empty target trust, while
dominance remains 40/48 and Lean remains 8/16 UNSAT because this new evidence
correctly has no Lean route. The cumulative direct-Z3 suite covers 1,592 cases
and controls. **Next action:** attack `nested9_true-unreach-call`, now the
smallest unsupported row at 32 DAG nodes. **That action is now LANDED
(ADR-0129):** exact shared ground premises and equal typed existential prefixes
are alpha-aligned, then every target-body conjunct is replayed by identity, a
source-bound `QF_BV` implication proof, or an exact signed-add lemma with the
no-wrap margin checked over signed constants. `nested9_true-unreach-call` moves
**Unsupported→UNSAT** with five-run solve median 0.075 ms and evidence median
0.039 ms. The fresh cvc5 quantified-BV slice is **32 SAT / 17 UNSAT / 0 unknown
/ 5 unsupported**, 49 agreements, DISAGREE=0, no errors/replay failures, and
five-run PAR-2 median 2.065744 s. The audit certifies/checks 49/49 with empty
target trust; dominance remains 40/49 and Lean remains 8/17 UNSAT. Eight
focused tests include 64 direct-Z3 safe transfers and 64 genuine signed-wrap
SAT controls; cumulative quantified-BV direct-Z3 coverage is 1,720 cases and
controls. The negative sweep also exposed and repaired two linear-depth term
builders: exact finite expansion and AC canonicalization now preserve
logarithmic-depth balanced trees through the maximum admitted 1,024-way fold.
**That action is now LANDED (ADR-0130):** each quantified source assertion
carries exact sorted values for all free BV symbols. Direct positive universals
are proved by a small affine GF(2) LSB interpreter; directly negated universals
carry complete typed binder values evaluated against the untouched body.
`smtcomp-qbv-053118` moves **Unsupported→SAT** with five-run target solve median
0.195489 ms and evidence median 3.287 ms. The fresh cvc5 quantified-BV slice is
**33 SAT / 17 UNSAT / 0 unknown / 4 unsupported**, 50 agreements, DISAGREE=0,
no errors/replay failures, and five-run PAR-2 median 1.623998 s. The audit
certifies/checks 50/50 with empty target trust; dominance is 41/50 and Lean
remains 8/17 UNSAT. Five focused tests include 32 direct-Z3 certified SAT models
and 32 UNSAT controls; cumulative quantified-BV direct-Z3 coverage is 1,784
cases and controls. Strict all-target solver Clippy and all adjacent quantified
certificate/differential suites pass; the complete workspace `just check`
(format, strict Clippy, tests, warning-denied rustdoc, foundational resources,
generated-document consistency, and links) also passes. **That action is now
LANDED (ADR-0131):** one directly negated existential implication may carry a
complete free-BV model only when the checker re-extracts exactly one
binder-dependent signed interval implication, evaluator-replays every ground
antecedent to true and the untouched division-bearing outer conclusion to
false, rejects empty intervals, and proves signed `lower <= upper <= cap`.
QF_BV generates candidates only. `intersection-example-onelane` moves
**Unsupported→SAT** with five-run corpus solve median 37.681117 ms and evidence
median 33.267 ms. The fresh cvc5 quantified-BV slice is **34 SAT / 17 UNSAT / 0
unknown / 3 unsupported**, 51 agreements, DISAGREE=0, no errors/replay failures,
and five-run PAR-2 median 1.200617 s. The audit certifies/checks 51/51 with 42/51
dominant, Lean 8/17 UNSAT, and empty target trust. Nine focused tests include 16
new certified SAT cases and 16 direct-Z3 UNSAT controls; cumulative
quantified-BV direct-Z3 coverage is 1,816. The complete workspace `just check`
(format, strict Clippy, tests, warning-denied rustdoc, foundational resources,
generated-document consistency, and links) passes. **Next action:** characterize
`gn-wrong-091018`, now the smallest unsupported row at 88 DAG nodes. **That
action is now LANDED (ADR-0132):** a separate directly negated existential
model checker requires exactly one binder-dependent inner implication whose
conclusion is signed nonnegativity of a binary product. One direct binder-free
`bvsdiv` factor must evaluator-replay to zero, the other factor must contain the
unique binder, and the comparison bound must be a same-width literal zero. The
nonlinear factor is never interpreted; every other ground fact replays and
QF_BV remains candidate-only. `gn-wrong-091018` moves **Unsupported→SAT** with
five-run corpus solve median 88.677335 ms and evidence median 70.981 ms. The
fresh cvc5 quantified-BV slice is **35 SAT / 17 UNSAT / 0 unknown / 2
unsupported**, 52 agreements, DISAGREE=0, no errors/replay failures, and
five-run PAR-2 median 0.794198 s. The audit certifies/checks 52/52 with 43/52
dominant, Lean 8/17 UNSAT, and empty target trust. Thirteen focused tests include
16 new certified SAT cases and 16 direct-Z3 nonzero-factor UNSAT controls;
cumulative quantified-BV direct-Z3 coverage is 1,848. The complete workspace
`just check` (format, strict Clippy, tests, warning-denied rustdoc,
foundational resources, generated-document consistency, and links) passes.
**Next action:**
characterize `psyco-001-bv`, now the smallest unsupported row at 147 DAG nodes.
It is a positive universal over mixed Bool/BV binders below free-Boolean facts;
work backwards from cvc5/Z3 quantified model checking and Boolean-discharge
machinery to isolate the exact guarded ITE/equality implication that a complete
free-Boolean model makes universal. Do not enumerate the 32-bit binders, trust
candidate Boolean simplification as evidence, or broaden ADR-0132's unrelated
zero-product matcher. **That action is now LANDED (ADR-0133):** bounded CEGIS
may refine complete free-Boolean candidates with concrete source instances,
but a separate checker accepts only positive Bool/BV universals with binder IDs
disjoint from free symbols and rebuilds the exact negated `QF_BV` residual
under the complete model before rechecking its DRAT/LRAT proof. Quantifier
erasure and instances remain search-only.
`psyco-001-bv` moves **Unsupported→SAT** with five-run corpus solve median
339.928031 ms and evidence median 761.351 ms. The fresh cvc5 quantified-BV
slice is **36 SAT / 17 UNSAT / 0 unknown / 1 unsupported**, 53 agreements,
DISAGREE=0, no errors/replay failures, and five-run PAR-2 median 0.408282 s. The
audit certifies/checks 53/53 with 44/53 dominant, Lean 8/17 UNSAT, and empty
target trust. Sixteen focused tests include 16 new certified SAT cases, 16
direct-Z3 UNSAT controls, and binder/free capture rejection; cumulative
quantified-BV direct-Z3 coverage is 1,880. The complete workspace `just check`
gate passes, including strict
Clippy, all tests, warning-denied rustdoc, foundational resources, generated
documentation checks, and link validation. **Next action:** characterize
`psyco-107-bv`, the sole remaining row, from its source shape and cvc5/Z3
quantifier/model-checking machinery. Preserve
the residual-proof contract: do not broaden positive-universal opening to
negative contexts, existentials, free BVs, functions, or mixed arithmetic.
**That action is now LANDED (ADR-0134):** bounded CEGIS may select complete
positive-universal Bool/BV source instances, while a separate checker binds the
exact ordered query, revalidates the source fragment, regenerates 1 through 256
unique complete typed instances, and rechecks DRAT/LRAT for exactly the ground
weakening plus those instances. Heuristic candidate blocks cannot enter the
artifact. `psyco-107-bv` moves **Unsupported→UNSAT** with five-run corpus solve
median 108.817031 ms and evidence median 103.525 ms. The public slice is now
**36 SAT / 18 UNSAT / 0 unknown / 0 unsupported**, 54 agreements,
DISAGREE=0, no errors/replay failures, and five-run PAR-2 median 0.0330305167
seconds. The audit certifies/checks 54/54 with 44/54 dominant, Lean 8/18 UNSAT,
and empty target trust. Seven focused tests include a two-instance necessity gate,
adversarial source/binding/proof/capture checks, unsupported-sibling decline,
and 32 direct-Z3 comparisons;
cumulative quantified-BV direct-Z3 coverage is 1,912. **Next action:** preserve
this full public-slice ratchet while moving from corpus completion to depth:
characterize Lean reconstruction for the ADR-0134 source-instance theorem and
its residual QF_BV proof, then use that boundary to rank the remaining checked
quantified-BV UNSAT certificates before broadening nested/alternating QSAT or
quantified-UF models.
**That action is now LANDED (ADR-0135):** the admitted source shape reconstructs
as genuine typed Bool/BV universal theorems; each carried tuple is introduced
only by applying its untouched source axiom to exact constructor witnesses; and
an independently AIG-lowered, compact named-gate Alethe tail closes the derived
ground assumptions. Classical double-negation normalization now carries an
explicit kernel-checked proof instead of reusing a proof at a non-definitionally
equal type. The two-instance theorem is registered in the real-Lean
representative harness (this host has no `lean` binary), while
the duplicate `psyco-107-bv` Lean stress route remains outside the default gate
after debug measurements exceeded three minutes at roughly 2.3 GiB RSS; the
public Lean count therefore remains 8/18. **Next action:** compact or serialize
the corpus-scale resolution proof so the ADR-0134 target completes under a
bounded Lean gate, then rank ADR-0124/0126/0127/0128/0129 source-bound UNSAT
families for reconstruction before broadening nested/alternating QSAT or
quantified-UF models.
**That action is now LANDED (ADR-0137):** declaration dependency discovery
visits the kernel expression DAG once, compact export no longer caps repeated
closed shares, single-use closed regions receive deterministic 512-node chunks,
and declaration types/values retain those chunks through capture-safe scoped
`let` aliases. A timed one-pass `psyco-107-bv` release stress gate completes in
102.19 seconds at 2,697,384 KiB max RSS under a 3 GiB test-process cap; the final
cold-build `just test-quant-bv-lean-stress` rerun passes in 106.51 seconds inside
4 GiB. Refreshed public
measurement is 54/54 decided and evidence-certified/rechecked, 45/54 dominant,
Lean UNSAT 9/18, DISAGREE=0, with no error/replay failure/audit error/timeout.
**Next action:** rank ADR-0124/0126/0127/0128/0129/0130/0131/0132/0133 by
source-proof reuse and measured reconstruction cost, implement the smallest
genuine Lean proof family next, and continue reducing the guarded 2.7 GiB export
peak before broadening nested/alternating QSAT or quantified-UF models.
**That action is now LANDED (ADR-0138):** ADR-0126's concrete Bool/BV witnesses
become genuine typed nested `Exists.intro` proofs against the sole untouched
negated source axiom. Small bodies carry explicit logical AIG gate proofs; large
bodies use shared reducible computational-Bool operators and local gate `let`s,
with kernel reduction checking the concrete root. Kernel abstraction,
instantiation, universe substitution, open inference, definitional equality,
and weak-head normalization now preserve expression-DAG sharing with
context-valid caches. The three public rows pass in 12.43 seconds under the 4
GiB gate; the refreshed exact audit is 54/54 evidence-certified/rechecked,
48/54 dominant, Lean UNSAT 12/18, DISAGREE=0, and has no audit error or timeout.
**Next action:** rank ADR-0124/0127/0128/0129 by source-proof reuse and guarded
reconstruction cost, implement the smallest remaining genuine Lean proof
family, and continue reducing large-proof memory before broader
nested/alternating QSAT or quantified-UF models.
**That ranking is now LANDED (ADR-0139):** the adjacent ADR-0127 experiment
exposed 15,705 proof commands with repeated 4,700--5,000-premise RUP chains and
failed safely at a 2.18 GiB allocation inside the 4 GiB guard, so it is now
explicitly gated on compact reflected-RUP checking. The smaller evaluator-proof
reuse slice closes `qbv-simp`: typed constructor values instantiate its
untouched universal, and an explicit evaluated AIG proof refutes the body in
0.08 seconds. Exact audit is 49/54 dominant and Lean UNSAT 13/18, with all 54
decisions checked/certified and zero mismatch/error/timeout. **Next action:**
implement ADR-0128's vacuous-existential elimination over the same evaluated-AIG
counterexample spine, then return to ADR-0124/0129 and the ADR-0127 RUP reflector.
**That action is now LANDED (ADR-0140):** the untouched `exists+ forall+`
source is encoded directly, every checker-proved-vacuous existential is
eliminated by genuine `Exists.rec`, and exact typed values instantiate the
surviving universal before computational AIG reduction closes `False`. The
explicit gate proof failed safely at a 1.42 GiB allocation; the accepted compact
route owns a scoped 64 MiB proof-worker stack and passes the public optimized
stress gate twice in 16.54 seconds (38.04 seconds cold, 1,975,764 KiB peak under
4 GiB). Exact audit is 50/54 dominant and Lean UNSAT 14/18, with 54/54 checked
and certified and zero mismatch/error/timeout. **Next action:** characterize
ADR-0129's paired-existential transfer for genuine source elimination and
introduction, then rank it against ADR-0124 before returning to ADR-0127's
compact reflected-RUP requirement.
**Process state:** first green CI in 200+ runs held into a green cadence;
the pre-push hook gates the pushed SHA incl. the ~6s `:status` corpus
sweep (a wrong verdict must not leave the machine); STATUS truncated
22,349→~600 lines with full archives (task #27); Track 5 (Verified
Systems, ADR-0056) adopted by the concurrent lane. **P4.2/P5.1 symexec
overlap — DECIDED (was flagged twice; now resolved):** Track 4's
`explore_cfg`/`SymbolicExecutor` is the single owner of the CFG
symbolic-execution engine; Track 5's P5.1 IR reflectors CONSUME it (feed it
reflected `axeyum-ir` CFG states) rather than build a parallel executor.
Track 5 is sequenced behind the Track 1/3 keystones it consumes (the driver,
the Lean ladder) — it advances where integration-independent (reflection,
panic-spec extraction) but its solver-facing obligations ride the shared
engine.
**Standing from 2026-07-03:** the first committed PAR-2 head-to-head
exists (`582ecba8`; the QF_BV parity lever is reduction depth, not CEGAR);
the budget-excused-cap audit found two healthy sites; the quiet-box
frontier ratchet (lia_cuts 20→26) remains queued.

**Grounding correction (important).** Reading the code + ADRs showed the NRA
engine is *far more built* than the first plan draft assumed: the bignum algebraic
core (polynomials, Sturm, resultants, real algebraic numbers, field arithmetic)
already lives in **`axeyum-ir`** (ADR-0044/0045/0046) and a **largely-complete
CAD** (2-variable complete, N-variable decision-complete, fuzz-gated) lives in
`axeyum-solver`. So there is **no new `axeyum-poly` crate** (ADR-0044 keeps the
primitives in `axeyum-ir`) and "Phase A" is mostly done — see the corrected
[P2.5 current-state](docs/plan/track-2-theories/P2.5-nra/00-current-state.md).
**Next-arc decomposition (2026-07-06, `fcbde209`) — EXECUTED 2026-07-07:**
[09-next-arithmetic-lever-decomposition](docs/plan/track-2-theories/P2.5-nra/09-next-arithmetic-lever-decomposition.md).
The ROI verdict (QF_NIA's bounded levers first) played out: all landed —
div/mod Euclidean linearization + congruent div-0 recovery (#40), `iand` blast,
`int.pow2` (#41), and the NRA cheap pickups incl algebraic-√2 (#43). QF_NIA-cvc5
21→33, QF_NRA-cvc5 27→32, DISAGREE=0. The bounded arithmetic levers are now
**harvested**; §3's "the DPLL→CAD edge is missing" premise was CORRECTED (it
existed at `5ede57f4`; #43 used it — see the doc's 10th-review note). The residue
is the ADR-0058 Phase C/D engine arc, de-prioritized below strings.

**Measured (2026-07-01/02, `check_auto` vs z3 4.13.3, curated corpus,
DISAGREE=0): QF_NRA 21→26/38 (`5cc63a15`; was 9/38 at `124e18aa`), QF_NIA
20/28.** The 2026-06-30 route-trace
finding (the CAD declines Boolean structure) was resolved by the landed
case-split (`5ede57f4` — the earlier fuzz "failure" was a benign i128
eval-overflow, not a wrong verdict), then sign/zero refutation (`f9e06baf`) and
**coprime-split CAD projection** (`98719094` — the dominant decline was a
shared-factor `Res ≡ 0`, not a cap). Strings re-measured under the ADR-0052
gate: QF_S 48/134, QF_SEQ 26/33, QF_SLIA 11/50 — **23 previously-claimed
`unsat`s are now honest `unknown`s, two of which were on declared-`sat`
instances** (real wrong verdicts the oracle path never compared;
[SCOREBOARD](bench-results/SCOREBOARD.md)).

**Live status (2026-07-02).** The **whole-repo health debt was paid**: main's CI
had been red for 198 consecutive runs (MSRV/let-chains, rustdoc, fmt,
cargo-deny, ~100 stable-clippy sites — repaired in `0d10aeba`/`f4734abf`); two
**exponential per-path DAG walks** were found and memoized
(`set_cardinality`'s BV collector `0bc133c2` — evidence binaries had been
grinding 8+ hours, stalling every full sweep since 2026-06-26; the `bv2nat`
blast's skeleton scan `f403991b` — a 9-hour QF_S scoreboard hang); and five
stale evidence reds that rotted behind the hang were un-rotted (`459ffc41`,
`4ca37cee` — the zero-trust Alethe emitters again outrank the structural
pre-solve certs, size-gated). `fifo_bc04` was root-caused (an O(dag·ite²)
contextual-`ite` saturation from `f4575ea5`) and un-ignored (`e67f218f`,
>600 s → 3.2 s); **one honest `#[ignore]` remains** (the uninterpreted-sort
`ite` SAT row → the P1.4/P1.5 e-graph keystone). All landings keep DISAGREE=0,
`unknown`-first, and the measured-scoreboard discipline.

The per-track detail, exit criteria, and current frontier levers are in the
sections below and under [`docs/plan/`](docs/plan/README.md). **Treat any
"phase complete" note as an increment, never as the goal.**

When multiple agents or humans are active, use separate topic-branch worktrees
and one `main` integration owner. The standing protocol lives in
[`docs/contributor-guide/multi-agent-worktrees.md`](docs/contributor-guide/multi-agent-worktrees.md).
Potential sibling/incubator projects around education, ontology artifacts,
rules/law reasoning, and downstream verification apps are tracked in
[`docs/sibling-projects.md`](docs/sibling-projects.md). The first detailed
incubator roadmaps live in [`docs/atlas/`](docs/atlas/),
[`docs/proof-cookbook/`](docs/proof-cookbook/), and
[`docs/rules-as-code/`](docs/rules-as-code/); their first validated artifacts
live under [`artifacts/ontology/`](artifacts/ontology/) and the corresponding
incubator subfolders. The broader foundational-resource expansion lives in
[`docs/foundational-resources/`](docs/foundational-resources/), including the
university-style math field spine in
[`docs/foundational-resources/MATH-FIELDS.md`](docs/foundational-resources/MATH-FIELDS.md)
and the top-down curriculum-wide resource master plan in
[`docs/foundational-resources/MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md`](docs/foundational-resources/MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md)
with the owner-facing all-resource plan in
[`docs/foundational-resources/MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md`](docs/foundational-resources/MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md)
and the curriculum-to-resource buildout plan in
[`docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md`](docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md);
the practical staged build sequence for educational content, ontology rows,
example packs, proof artifacts, solver feedback, rules/law transfer, and future
library boundaries is
[`docs/foundational-resources/MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md`](docs/foundational-resources/MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md);
the forward execution plan for turning validated packs into learner paths,
proof upgrades, solver feedback, and consumer boundaries is
[`docs/foundational-resources/CURRICULUM-RESOURCE-EXECUTION-PLAN.md`](docs/foundational-resources/CURRICULUM-RESOURCE-EXECUTION-PLAN.md).
The commit-sized curriculum/resource work matrix is
[`docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md`](docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md).
The current execution ledger for stabilizing the 173 current math packs,
resolving unclassified solver-reuse rows, completing learner paths, and
deepening proof routes field by field is
[`docs/foundational-resources/MATH-CURRICULUM-DETAILED-BUILD-PLAN.md`](docs/foundational-resources/MATH-CURRICULUM-DETAILED-BUILD-PLAN.md).
The current learner-spine audit over all non-template math packs is
[`docs/foundational-resources/LEARNER-COVERAGE-AUDIT.md`](docs/foundational-resources/LEARNER-COVERAGE-AUDIT.md);
it records all 173 current non-template packs as focused-lesson linked, with no
path-only, index-only, or missing learner buckets.
The detailed operating roadmap for building the math-curriculum resource system
across ontology rows, example packs, learner pages, proof routes, solver reuse,
rules/law transfer, consumer boundaries, and eventual library splits is
[`docs/foundational-resources/RESOURCE-BUILDOUT-ROADMAP.md`](docs/foundational-resources/RESOURCE-BUILDOUT-ROADMAP.md).
The compact all-field consumer readiness table is
[`docs/foundational-resources/FIELD-READINESS-QUERY-MATRIX.md`](docs/foundational-resources/FIELD-READINESS-QUERY-MATRIX.md);
it records the smoke-checked route, bridge lookup, checked-row drilldown, and
theorem boundary for all 18 math fields.
The proof-route query matrix is
[`docs/foundational-resources/PROOF-ROUTE-QUERY-MATRIX.md`](docs/foundational-resources/PROOF-ROUTE-QUERY-MATRIX.md);
it records route-level summary queries and boundaries for finite replay,
Boolean CNF/LRAT, QF_BV, QF_LIA/Diophantine, QF_LRA/Farkas, QF_UF/Alethe, and
Lean-horizon resources.
The theorem-horizon query guide is
[`docs/foundational-resources/THEOREM-HORIZON-QUERIES.md`](docs/foundational-resources/THEOREM-HORIZON-QUERIES.md);
it records route, pack, field, and text queries for `lean-horizon` rows so
consumers can find theorem boundaries without treating them as checked SMT
evidence; the public query script also exposes
`horizon-frontier` for theorem-boundary rows with finite-shadow contrast,
including finite/infinite cardinality, algebra homomorphism/quotient structure,
vector-space/duality/module/tensor structure, group-action/orbit-stabilizer
and Burnside theorem boundaries, monoid/permutation-group theorem boundaries,
finite random-variable and conditional-expectation theorem boundaries,
recurrence/asymptotic, stochastic-kernel, and
martingale/stopping theory, finite integration/Lebesgue theorem boundaries,
finite product-measure/Fubini-Tonelli theorem boundaries,
root-finding convergence/stability, and
calculus differentiability/integrability/FTC/multivariable theory,
complex-analysis/factorization theory, convexity/Jensen theorem boundaries,
hyperplane-separation/duality, KKT sufficiency, active-set method theory, SDP
duality/Slater-condition theory, and gradient-descent convergence/rate
theory, line-search termination/convergence theory, Wolfe-line-search
existence/convergence theory, and projected-gradient projection/convergence
theory, proximal-gradient proximal-map/convergence theory, max-flow/min-cut
theorem boundaries, shortest-path theorem boundaries, topological-sort theorem
boundaries, finite topology/compactness/connectedness/quotient/specialization
theorem boundaries, affine-geometry affine-combination/incidence,
incidence-geometry projective/configuration, orientation/area
affine-volume/change-of-variables, circle-geometry tangent/chord,
rigid-configuration graph-rigidity/classification, inversion-geometry
circle-line, and cyclic-geometry Ptolemy theorem boundaries.
The theorem-horizon lane now also has a focused finite chain-complex torsion
boundary that keeps one-entry Smith replay and checked `2*k = 1`
QF_LIA/Diophantine evidence separate from general Smith normal form,
universal coefficient, Ext/Tor, exact-sequence, chain-homotopy, and
topological-invariance theorem coverage.
The solver-reuse query guide is
[`docs/foundational-resources/SOLVER-REUSE-QUERIES.md`](docs/foundational-resources/SOLVER-REUSE-QUERIES.md);
it records promoted-pack, proof-route, field, and checked-row queries for
solver/proof contributors mining the resource corpus without turning
educational rows into benchmark or parity claims.
The proof-upgrade query guide is
[`docs/foundational-resources/PROOF-UPGRADE-QUERIES.md`](docs/foundational-resources/PROOF-UPGRADE-QUERIES.md);
it records route-summary, replay-only row, route-relevant pack, checked-row,
curriculum-node, solver-reuse, and horizon queries for choosing certificate
upgrades without over-promoting finite replay rows.
The trust-boundary query guide is
[`docs/foundational-resources/TRUST-BOUNDARY-QUERIES.md`](docs/foundational-resources/TRUST-BOUNDARY-QUERIES.md);
it records proof-status and result-status drilldowns for checked evidence,
replay-only finite rows, and Lean-horizon boundaries before consumers display
or promote resource claims.
The fragment-demand query guide is
[`docs/foundational-resources/FRAGMENT-DEMAND-QUERIES.md`](docs/foundational-resources/FRAGMENT-DEMAND-QUERIES.md);
it records fragment-scoped pack and row queries for Bool, QF_BV, QF_LIA,
QF_LRA, QF_UF, finite replay, and Lean-horizon resources so solver and proof
contributors can mine curriculum pressure without turning it into parity
evidence.
The rejection-case query guide is
[`docs/foundational-resources/REJECTION-CASE-QUERIES.md`](docs/foundational-resources/REJECTION-CASE-QUERIES.md);
it records malformed-claim and route-scoped rejection queries while keeping
public resource rows separate from proof-cookbook tamper tests.
The checker-tamper matrix is
[`docs/foundational-resources/CHECKER-TAMPER-MATRIX.md`](docs/foundational-resources/CHECKER-TAMPER-MATRIX.md);
it maps each active proof route from malformed source-row discovery to the
focused corrupted-evidence command, and records routes that still need a tamper
regression before they can be called tamper-covered.
The claim-label matrix is
[`docs/foundational-resources/CLAIM-LABEL-MATRIX.md`](docs/foundational-resources/CLAIM-LABEL-MATRIX.md);
it maps `expected_result` plus `proof_status` pairs to allowed downstream
display labels so consumers do not turn checked evidence, finite replay,
Lean-horizon rows, or promoted solver-reuse packs into theorem, benchmark, or
parity claims; the public consumer query script exposes the same mapping through
`python3 scripts/query-foundational-resources.py labels`.
The public data contract is
[`docs/foundational-resources/PUBLIC-DATA-CONTRACT.md`](docs/foundational-resources/PUBLIC-DATA-CONTRACT.md);
it defines the JSON files, stable fields, schema/version expectations,
compatibility rules, smoke commands, coverage summaries, and display-label
counts that make the R6 consumer boundary usable without importing Axeyum
internals.
The coverage-frontier query guide is
[`docs/foundational-resources/COVERAGE-FRONTIER-QUERIES.md`](docs/foundational-resources/COVERAGE-FRONTIER-QUERIES.md);
it ranks field, fragment, curriculum-node, and decidability groups by checked
evidence, replay-only refutations, and Lean-horizon pressure, with
action-filtered worklists for proof-review/proof-upgrade/theorem-horizon
routing, so builders can choose the next pack, proof-upgrade, proof-review, or
learner-page increment from the public JSON contract.
The pack-frontier query guide is
[`docs/foundational-resources/PACK-FRONTIER-QUERIES.md`](docs/foundational-resources/PACK-FRONTIER-QUERIES.md);
it drills from those group-level rankings to concrete pack worklists with
checked-density, proof-review, theorem-horizon, route-promotion, and
finite-shadow filters.
The curriculum-node query guide is
[`docs/foundational-resources/CURRICULUM-NODE-QUERIES.md`](docs/foundational-resources/CURRICULUM-NODE-QUERIES.md);
it records concept, pack, field, route, checked-row, and horizon drilldowns for
consumers that start from the formal curriculum DAG rather than a field or
proof route.
The proof-route family selector is
[`docs/foundational-resources/PROOF-ROUTE-FAMILY-SELECTION.md`](docs/foundational-resources/PROOF-ROUTE-FAMILY-SELECTION.md);
it picks one representative replay-heavy family per active proof route and
states when another compact negative row is worth promoting to checked
evidence.
The proof-route learner snippets guide is
[`docs/learn/math/proof-route-learner-snippets.md`](docs/learn/math/proof-route-learner-snippets.md);
it gives reusable trust-boundary wording for Boolean CNF/LRAT, QF_LRA/Farkas,
QF_UF/Alethe, QF_LIA/Diophantine, and QF_BV/DRAT rows.
The matrix computation consumer query guide is
[`docs/foundational-resources/MATRIX-COMPUTATION-QUERIES.md`](docs/foundational-resources/MATRIX-COMPUTATION-QUERIES.md);
it records exact concept-plus-route queries for LU/nullspace, residual,
Schur complements, rank/nullity, eigenpair, singular-value, random-matrix,
chain/cochain/UCT, tensor/module, operator, and Chebyshev resources.
The probability/statistics consumer query guide is
[`docs/foundational-resources/PROBABILITY-STATISTICS-QUERIES.md`](docs/foundational-resources/PROBABILITY-STATISTICS-QUERIES.md);
it records exact concept-plus-route queries for finite probability tables,
finite measure, product/integration, pushforwards, conditional expectation,
stochastic kernels, tail counts, exact tests, and finite random-matrix
moments, including Schur conditional-variance shadows.
The measure-theory consumer query guide is
[`docs/foundational-resources/MEASURE-THEORY-QUERIES.md`](docs/foundational-resources/MEASURE-THEORY-QUERIES.md);
it records exact concept-plus-route queries for finite measure additivity,
product/integration, pushforwards, conditional expectation, martingales,
kernels, hitting times, and concentration resources.
The topology/homology consumer query guide is
[`docs/foundational-resources/TOPOLOGY-HOMOLOGY-QUERIES.md`](docs/foundational-resources/TOPOLOGY-HOMOLOGY-QUERIES.md);
it records exact concept-plus-route queries for metric balls, finite topology,
compactness, connectedness, quotient/specialization rows, finite homology,
cohomology, UCT shadows, and cup-product resources.
The algebra structure consumer query guide is
[`docs/foundational-resources/ALGEBRA-STRUCTURE-QUERIES.md`](docs/foundational-resources/ALGEBRA-STRUCTURE-QUERIES.md);
it records exact concept-plus-route queries for finite groups/actions,
homomorphisms, ideals, quotient rows, modules, tensor rows, and fixed-width
residue/field resources.
The number and arithmetic consumer query guide is
[`docs/foundational-resources/NUMBER-ARITHMETIC-QUERIES.md`](docs/foundational-resources/NUMBER-ARITHMETIC-QUERIES.md);
it records exact concept-plus-route queries for gcd/divisibility, CRT,
nonunit inverse, fixed-width residue, totality, quotient/ideal, and
exact-vs-floating resources.
The geometry resource consumer query guide is
[`docs/foundational-resources/GEOMETRY-RESOURCE-QUERIES.md`](docs/foundational-resources/GEOMETRY-RESOURCE-QUERIES.md);
it records exact concept-plus-route queries for finite coordinate/incidence/
rigid/affine/orientation geometry and finite circle/inversion/cyclic geometry
resources.
The graph/discrete consumer query guide is
[`docs/foundational-resources/GRAPH-DISCRETE-QUERIES.md`](docs/foundational-resources/GRAPH-DISCRETE-QUERIES.md);
it records exact concept-plus-route queries for finite graph coloring,
reachability, matching, cuts, d-separation, fixed-width coloring, and BFS/DFS
runtime resources.
The optimization/convexity consumer query guide is
[`docs/foundational-resources/OPTIMIZATION-CONVEXITY-QUERIES.md`](docs/foundational-resources/OPTIMIZATION-CONVEXITY-QUERIES.md);
it records exact concept-plus-route queries for LP objectives, convexity
shadows, KKT/QP/SDP rows, first-order method steps, projections, residuals,
Schur-complement shadows, and exact-vs-floating boundary resources.
The functional-analysis/operator consumer query guide is
[`docs/foundational-resources/FUNCTIONAL-OPERATOR-QUERIES.md`](docs/foundational-resources/FUNCTIONAL-OPERATOR-QUERIES.md);
it records exact concept-plus-route queries for finite operators, Chebyshev
rows, inner-product/projection rows, spectral and singular-value rows, and
dual/tensor equality resources.
The analysis/numerical consumer query guide is
[`docs/foundational-resources/ANALYSIS-NUMERICAL-QUERIES.md`](docs/foundational-resources/ANALYSIS-NUMERICAL-QUERIES.md);
it records exact concept-plus-route queries for bounded real-analysis rows,
numerical-method rows, residuals, singular-value shadows, dynamics/Euler,
Runge-Kutta midpoint, Heun rows, Backward Euler rows, Crank-Nicolson rows,
Adams-Bashforth rows, BDF2 rows, Simpson-rule quadrature rows, Romberg
extrapolation rows, Schur complements, real-Schur rows, and complex real-pair
resources.
The dynamics consumer query guide is
[`docs/foundational-resources/DYNAMICS-QUERIES.md`](docs/foundational-resources/DYNAMICS-QUERIES.md);
it records exact concept-plus-route queries for finite recurrences,
transition/invariant rows, Euler, Backward Euler, and Crank-Nicolson rows,
Adams-Bashforth rows, BDF2 rows, stochastic kernels, Markov chains, and
hitting-time resources.
The foundations/discrete consumer query guide is
[`docs/foundational-resources/FOUNDATIONS-DISCRETE-QUERIES.md`](docs/foundational-resources/FOUNDATIONS-DISCRETE-QUERIES.md);
it records exact concept-plus-route queries for Boolean proof rows, finite
proof patterns, bounded induction, finite quantifiers, cardinality, counting,
Boolean algebra, partition, and relation/function resources.
The finite countermodel replay consumer query guide is
[`docs/foundational-resources/COUNTERMODEL-REPLAY-QUERIES.md`](docs/foundational-resources/COUNTERMODEL-REPLAY-QUERIES.md);
it records pack-scoped concept queries for Boolean assignments, finite
predicate tables, proof-pattern counterexamples, function-table conflicts, and
finite order/lattice countermodels while keeping proof-route claims separate.
The rules/law transfer crosswalk that maps finite predicates, arithmetic
thresholds, graph reachability, precedence, category equivalence, and proof
routes into concrete policy/rule checks is
[`docs/foundational-resources/RULES-LAW-CROSSWALK.md`](docs/foundational-resources/RULES-LAW-CROSSWALK.md).
The rules/law query guide is
[`docs/foundational-resources/RULES-LAW-QUERIES.md`](docs/foundational-resources/RULES-LAW-QUERIES.md);
it records copyable `scripts/query-rules-as-code.py` commands for pack
discovery, coverage summaries, checked-obligation lookup, generated
query-family lookup, and bounded generated-row inspection.
The rules/law pattern matrix is
[`docs/foundational-resources/RULES-LAW-PATTERN-MATRIX.md`](docs/foundational-resources/RULES-LAW-PATTERN-MATRIX.md);
it maps finite predicates, role/tenant relations, thresholds, monotonicity,
version transitions, precedence, category equivalence, workflow reachability,
and bounded implementation-equivalence patterns back to math concept rows,
proof routes, current packs, and copyable queries.
The learner-facing rules/law trust-boundary page is
[`docs/learn/rules-law-trust-boundary.md`](docs/learn/rules-law-trust-boundary.md);
it walks from human-authored source rules through formal models, replayed
witnesses, checked obligations, and explicit legal/theorem horizons.
Curriculum coverage status (2026-07-06): all 19 non-Lean-horizon nodes of the
23-node formal-mathematics-tour DAG are `covered` — the last five `planned`
nodes (proof-methods, induction, relations-and-functions, rationals, reals)
gained self-checking `axeyum-scenarios` families (ProofMethods, Induction,
Relation, Rational, RealAlgebra), the mathtour covered-implies-realized
invariant enforces them, and the curriculum-status audit's review queue is
empty; the remaining 4 nodes (cardinality, complex, sequences-and-limits,
calculus) are Lean-horizon proof-reconstruction targets by design.
Current resource-buildout status (2026-07-06): the public JSON layer reports
137 concept rows, 173 non-template packs, 1131 expected checks (581 `sat`,
414 `unsat`, 136 `not-run`), 399 checked rows, 596 replay-only rows, 136
Lean-horizon rows, and 173 promoted solver-reuse packs. The latest math pack
adds finite policy-iteration replay with exact zero-residual
policy-evaluation linear solves on the shared discounted MDP, greedy
improvement rounds, termination by policy stability, monotone value
improvement to the same exact optimum as value iteration, a checked bad
policy-value QF_LRA/Farkas row, and explicit policy-improvement-theorem,
termination/optimality, average-reward, stochastic-approximation, and
floating-point-dynamic-programming horizons.
The rules/law JSON
layer now reports 7 packs, 1,037
bounded sample rows, 1,942 generated query rows, 27 checked obligations, and
9 replayed witness rows. The learner
coverage audit records all 167 non-template packs as focused-lesson linked,
with no path-only, index-only, or missing learner buckets. The first QF_UF/Alethe
proof upgrade wave now includes equivalence classes, relations/functions, finite
groups, function composition, finite algebra homomorphisms, finite monoids, and
finite group actions, with finite continuous-map preimage membership,
finite module scalar-closure membership, finite vector-space additive-closure
membership, finite dual-space covector additivity, finite tensor-product
left-additivity, finite order-lattice antisymmetry, finite ideal
additive-closure membership, finite quotient-topology, finite
specialization-order, finite cohomology, finite universal-coefficient shadow,
and finite cup-product extensions. The
finite countermodel lane now also makes explicit finite universes, Boolean
assignments, predicate extensions, relation tables, function tables, and finite
order/lattice counterexamples queryable as one checked bridge concept with a
learner-facing replay guide and a consumer query guide, without changing pack
or check totals. The theorem-horizon lane now also has a consumer query guide
for finding `lean-horizon` rows by route, field, pack, and topic while keeping
them out of checked-evidence claims, and focused boundary pages for real
completeness, monotone convergence, finite hitting-time theory,
Chebyshev/operator theory, finite concentration, and finite Euler/ODE theory
now keep finite checked shadows separate from general theorem targets. The solver-reuse
lane now also has a consumer query guide for finding promoted packs by proof
route, field, and checked row while keeping educational resources separate from
benchmark and parity claims. The proof-upgrade lane now also has a consumer
query guide for finding replay-only rows, route-relevant packs, checked
evidence contrasts, curriculum-node/R5 slices, and Lean horizons before
promoting another certificate row. The curriculum-node
lane now also has a consumer query guide for starting from nodes such as
`sets`, `linear-algebra`, `modular-arithmetic`, and `calculus`, then drilling
into concepts, packs, checked rows, and theorem horizons. The
finite algebra-homomorphism lane now also promotes the
concrete bad group-homomorphism row through QF_UF/Alethe after exact table
replay isolates `phi(1+1)=1` versus `phi(1)+phi(1)=0`. The finite
linear-algebra lane now also promotes the explicit
`qf-lra-bad-lu-product-entry` row after exact LU replay computes
`(L*U)[1,1] = 3` while the malformed row claims `4`, and the bad
nullspace-component row through QF_LRA/Farkas after exact matrix replay
computes `A*v = 0` for `v = [2, -1]` while the bad row claims the first
component is `1`. The finite
metric-continuity lane now also promotes the bad open-ball preimage row through
QF_LRA/Farkas after exact finite replay computes the output-ball preimage as
`{p0, p1}` while the bad row claims `p2` is inside even though
`|f(p2)-0| = 1`. The sequence-limit lane now also promotes the bad
reciprocal-tail bound row through QF_LRA/Farkas after exact replay computes
`a_2 = 1/3` while the bad row claims the distance is strictly below `1/4`.
The analysis bridge lane now also makes rational interval replay, sequence-tail
shadows, Cauchy-tail shadows, squeeze shadows, derivative-identity shadows, and
integration horizons first-class atlas concepts. The bounded-family/asymptotic
boundary lane now also makes finite BFS/DFS runtime counters, finite recurrence
prefixes, fixed coefficient windows, bounded dynamics traces, and finite Euler
error rows queryable as one bridge concept while keeping asymptotic runtime,
closed-form recurrence, convergence-rate, and limiting theorem claims in the
Lean-horizon lane. The polynomial bridge lane now also makes fixed coefficient
tuples, division/factor witnesses, coefficient windows, root-finding steps,
derivative shadows, and polynomial geometry obligations queryable by one
concept while keeping general factorization, algebraic closure, root
distribution, and generating-function convergence as proof horizons. The algebra
equality-certificate lane now makes the table-replay-versus-QF_UF/Alethe
promotion rule queryable by one bridge concept, so finite algebra rows graduate
only when the table checker and congruence certificate tell different useful
stories. The finite
order/lattice lane now also promotes the false Boolean-lattice top-element row
through Bool/CNF DRAT/LRAT after exact relation replay isolates `B !<= A`
while the bad claim that `A` is top requires `B <= A`. The modular-arithmetic
QF_LIA/Diophantine lane now also includes the incompatible non-coprime CRT row:
`x == 1 mod 4` and `x == 2 mod 6` reduce to `4*a - 6*b = 1`, where
`gcd(4,6)=2` does not divide `1`, and the fixed-width QF_BV lane now includes
the composite nonunit inverse search and the modulo-5 Fermat-unit counterexample
search: no 3-bit residue `b < 6` satisfies `(2*b) mod 6 = 1`, and no 3-bit
residue `0 < a < 5` satisfies `a^4 mod 5 != 1`, both with checked
DIMACS/DRAT evidence. The topology
QF_LIA/Diophantine lane now also includes finite chain-complex torsion via
one-entry Smith diagonal replay and checked rejection of `2*k = 1`, plus
finite simplicial homology boundary-square cancellation via checked rejection
of the false coefficient row `coeff_b = 1` when `boundary(boundary([a,b,c]))`
forces `coeff_b = 0`. The
measure/probability QF_LRA/Farkas lane now also promotes finite
product-measure's bad product-probability and bad marginal rows through
source-linked exact linear contradictions after replay computes the product
mass and row marginal, plus finite random-variables' bad pushforward row after
replay computes the outcome mass and bad expectation-through-pushforward row
after replay computes `E[X] = 20`, with separate `qf-lra-*` proof rows for the
final exact-linear contradictions, finite-integration's bad expectation row
after replay computes the integral, finite-conditional-expectation's bad
total-expectation row after replay computes `E[X] = E[E[X|G]] = 7/2` while the
bad row claims `4`, and its bad tower-property row after nested-partition
replay computes `7/2` rather than `4`, plus its bad variance-decomposition row
after finite replay computes `Var(X)=35/4`, `E[Var(X|G)]=5/2`, and
`Var(E[X|G])=25/4` while the bad row claims total variance `9`,
finite-measure's explicit `qf-lra-bad-complement-measure` row
after finite replay computes the event
and total measures, finite-measure-monotonicity's bad subset-measure and
union-subadditivity rows after finite replay computes the subset/superset
measures and the union bound `mu(A)+mu(B)=4/3`, finite-martingales'
bad stopped-expectation and conditional-expectation rows after bounded stopping
replay computes `E[M_tau] = 0` and finite filtration replay computes the
up-block expectation, finite Markov-chain's bad stochastic-row and false
stationary-distribution rows now kept as exact replay while
`qf-lra-bad-stochastic-row` and `qf-lra-bad-stationary-distribution` own the
checked Farkas proof-object regressions in solver-reuse metadata,
finite concentration's bad tail-bound and bad union-bound rows after exact
finite replay computes `P(X >= 2) = 1/4` and `P(A union B) = 3/4`, and finite
hitting-times' bad survival-mass and bad expected-time rows after replay
computes `P(T > 4) = 5/16` and the start equation reduces to
`2*h_start = 2 + h_start + h_middle`, plus finite-probability's bad
total-variation row after replay computes absolute differences `1/6, 0, 1/6`,
`l1 = 1/3`, and `TV = 1/6` while the bad row claims `1/4`.
The statistics
QF_LRA/Farkas lane now also promotes exact-statistical-tests' bad Fisher
left-tail and probability-ordered two-sided rows after fixed-margin replay
computes `17/70` rather than `1/4` and `17/35` rather than `1/2`,
and exact-statistical-tests' bad multinomial row after finite enumeration
computes `1/9` rather than `1/6`,
alongside descriptive-statistics' explicit `qf-lra-bad-variance` row after
exact finite-sample replay computes `Var(X) = 5/4` rather than `3/2`.
The numerical-analysis QF_LRA/Farkas lane now also promotes
numerical-linear-algebra's bad solution-box upper-bound row after exact
linear-system replay computes `x0 = 6/5` rather than satisfying the claimed
`x0 <= 1` bound, alongside its bad Jacobi first-step error-bound row where
iteration replay computes `||x1 - x*||_inf = 7/44` rather than satisfying the
claimed `1/8` bound.
The foundational concept atlas now also includes 65 generated R1 bridge
rows: finite model replay, counterexample proof, bounded theorem shadows,
refutation-as-query, finite proof-pattern replay, finite quantifier expansion,
bounded induction obligations, Boolean CNF DRAT/LRAT anatomy, QF_LRA Farkas
certificate anatomy, exact-vs-floating arithmetic, LP objective-threshold
replay, rational convexity/gradient shadows, QF_UF Alethe certificate
anatomy, QF_BV bit-blast certificate anatomy, gcd/divisibility witnesses,
modular CRT/inverse witnesses, finite counting replay, finite graph replay/
obstruction, finite dynamics/Euler replay, finite Boolean algebra, finite
partition/relation roundtrips, finite image/preimage/inverse tables, finite
bijection/cardinality,
cardinality theorem horizons, metric balls, bounded epsilon-delta shadows,
compactness shadows, connectedness shadows, continuity-by-preimage, finite
topology closure/interior and homeomorphism replay,
finite quotient-topology replay,
finite specialization-order replay, finite boundary-operator replay, finite
chain-complex/homology replay, finite torsion-homology replay, finite
cohomology replay, finite universal-coefficient shadow replay, finite
cup-product replay, LU factorization and nullspace
replay with checked bad product-entry and bad nullspace-component evidence,
rank-nullity replay, residual bounds, eigenpair witnesses, characteristic polynomial replay, finite
trace-invariant checks, finite random-matrix moments, finite measure additivity, finite probability mass
tables and finite distribution-distance rows, finite pushforward distributions, finite stochastic kernels, finite
conditional expectations, finite product-measure/integration replay, finite
tail/count obstructions, homomorphism preservation, kernel/image replay,
quotient maps,
ideal closure, module actions, tensor bilinearity, finite group actions,
totality conventions, and Lean horizons, plus coordinate/incidence/rigid/
oriented geometry replay, finite circle/inversion/cyclic geometry replay,
complex real-pair transform replay, finite inner-product/projection replay,
and finite operator/Chebyshev replay, so resource packs can point at shared
evidence and boundary vocabulary instead of repeating it locally.
The measure-theory bridge rows now make finite event-algebra/additivity,
complement, monotonicity, subadditivity, product-table, marginal, finite
Fubini-style sum, and simple-function integral replay queryable while keeping
Lebesgue measure, general product-measure existence, convergence theorems, and
almost-everywhere reasoning in the Lean-horizon lane.
The public foundational-resource consumer query layer now also exercises the
topology lane: Boolean, Alethe, Diophantine, and QF_BV field readiness,
metric/compactness/preimage/closure/homeomorphism/quotient/specialization/boundary/homology/
torsion/cohomology/universal/cup
bridge lookups, concept-scoped metric-ball, bounded epsilon-delta,
finite topology-operator/homeomorphism, finite quotient-topology, finite
specialization-order, finite boundary-operator, chain-complex/homology, and
finite torsion-homology/cohomology/universal-coefficient/cup-product
queries, and checked
Boolean/Alethe/Diophantine/QF_BV rows for finite topology, compactness, connectedness,
continuous maps, homeomorphism replay, finite quotient topology, finite specialization order, boundary
replay, homology, torsion homology, cohomology, finite universal-coefficient
shadow, finite cup products, metric balls, and bounded epsilon-delta shadows are
smoke-checked through the committed JSON contract, while arbitrary compactness,
connectedness, quotient topology universal properties, quotient-map theorem schemas,
specialization-order theorems, homeomorphism invariance,
homology/cohomology invariance, exact sequences, universal coefficient theorems,
cohomology-operation laws, and
general algebraic-topology theorems stay in the theorem-horizon lane.
The public foundational-resource consumer query layer now also exercises the
statistics lane: Farkas field readiness, finite-table/tail-count bridge
lookups, random-matrix bridge lookups, concept-scoped
`bridge_random_matrix_finite_moment` Farkas pack and checked-row queries, and
checked Farkas/Diophantine rows for exact finite tests, contingency tables,
regression, random matrices, probability/process tables, concentration, and
stochastic kernels are smoke-checked through the committed JSON contract,
while floating-point inference, asymptotic sampling, MCMC, VI,
model-calibration claims, random-matrix asymptotics, universality, simulation
quality, and high-dimensional limit laws stay in numerical-honesty or
theorem-horizon lanes.
The public foundational-resource consumer query layer now also exercises the
linear-algebra lane: Farkas/Alethe field readiness, rank/projection bridge
lookups, and checked rows for exact rational matrices, residual/eigen
witnesses, finite vector spaces, dual spaces, modules, tensors, geometry
dot-products, finite SDP/KKT/active-set rows, and matrix process equations are
smoke-checked through the committed JSON contract, while spectral theorems,
conditioning/stability, and general vector-space/module/tensor theorem claims
stay in the horizon lanes; the focused
[`linear-algebra-structure-theorem-boundary.md`](docs/learn/math/linear-algebra-structure-theorem-boundary.md)
page now records that split for finite vector, dual, module, and tensor packs.
The public foundational-resource consumer query layer now also exercises the
core algebra/number/graph lanes: abstract-algebra Alethe readiness,
homomorphism/ideal bridge lookups, concept-scoped homomorphism-preservation
Alethe checked-row queries, checked Alethe and fixed-width QF_BV rows;
number-theory Diophantine readiness, finite-family lookups, and checked
integer-arithmetic plus fixed-width residue rows; and graph-theory Boolean plus
LIA readiness,
graph-family/runtime lookups, checked finite
coloring/reachability/matching/cut/d-separation rows, and checked finite
BFS/DFS cost-counter rows. These are smoke-checked through the committed JSON contract without
promoting arbitrary algebraic-structure theorems, unbounded number-theory
claims, asymptotic graph algorithms, or general graph theorems. The focused
[`algebra-homomorphism-quotient-theorem-boundary.md`](docs/learn/math/algebra-homomorphism-quotient-theorem-boundary.md)
page now records the finite map/kernel/image/ideal/quotient split from general
isomorphism and ideal-theory theorem claims.
The public foundational-resource consumer query layer now also exercises the
analysis/numerical/complex lanes: real-analysis Farkas readiness,
epsilon/gradient bridge lookups, and checked bounded-analysis rows;
numerical-analysis Farkas readiness, residual/operator bridge lookups, and
checked exact residual, Euler, operator, recurrence, and optimization-step
rows; and complex-analysis Farkas readiness, real-pair bridge lookup, and
checked algebraic complex rows. These are smoke-checked through the committed
JSON contract without promoting completeness, convergence, floating-point
stability, holomorphic, analytic-continuation, or theorem-level calculus
claims.
The public foundational-resource consumer query layer now also exercises the
foundations/discrete/probability lanes: logic/proof Boolean readiness,
proof-vocabulary lookups, and checked proof-pattern/CNF rows; set-theory and
foundations Alethe/Boolean readiness, partition and finite-Boolean-algebra
lookups, and checked finite relation/function/quotient/equality and set-family
contradiction rows; discrete-math Diophantine/Boolean readiness,
finite-family lookups, and checked counting/coefficient/tail-count and finite
Boolean-algebra rows; and
probability-theory Farkas readiness, probability-table lookups, and checked
finite probability/process rows. These are smoke-checked through the committed
JSON contract without promoting proof automation, ZFC/infinite set theory,
asymptotic combinatorics, continuous probability, stochastic-process limits,
or theorem-level probability claims.
The sequence/real-analysis lane now also splits bounded monotone sequence and
finite recurrence-prefix, separation/root-finding, KKT, active-set QP, SDP, and gradient-descent checks into focused packs: finite monotone-prefix
replay, finite prefix supremum, finite tail-gap replay, Fibonacci prefix
replay, affine recurrence replay, companion-matrix state replay, exact
bisection/Newton replay, finite convex-combination/separator replay,
finite constrained-quadratic KKT replay, finite active-set QP face/slack
replay plus inactive-slack evidence, finite two-by-two SDP replay, exact gradient-descent step replay, exact
Armijo line-search replay, exact Wolfe line-search replay, exact
projected-gradient interval/decrease replay, and exact L1 proximal-gradient
soft-threshold plus box-constrained replay, and checked
QF_LRA/Farkas rejection of bad upper-bound, bad finite-value, bad Newton-step,
bad bisection-width, bad convex-combination,
bad separator, bad stationarity, bad free-gradient, bad inactive-slack,
bad degenerate active-set multiplier, bad objective, bad duality-gap, bad slack-entry, bad decrease,
bad step-coordinate, bad descent-bound, bad Armijo, bad descent-direction, bad accepted-candidate, bad Wolfe-minimizer,
bad Wolfe-sufficient-decrease, bad Wolfe-curvature, bad
projection, bad projected-decrease, bad proximal-point, and bad
composite-decrease, and bad box-proximal-point rows, while
monotone convergence, closed-form recurrence solving, asymptotics, and
separation/KKT/active-set/SDP/descent/Wolfe/line-search/projected-gradient/proximal-gradient/stability/convergence theorems remain Lean-horizon.
The optimization/convexity bridge rows now make exact LP feasibility,
objective-threshold Farkas replay, finite midpoint/Jensen shadows, affine
monotonicity, gradient replay, Hessian-minor witnesses, least-squares
normal-equation replay, finite root-finding steps, and finite hyperplane
separation plus finite KKT stationarity/complementarity, finite active-set QP
face/slack replay, and finite SDP objective/slack/gap replay plus finite
gradient-descent step/decrease replay and finite line-search
rejection/acceptance replay plus finite Wolfe line-search replay plus finite
projected-gradient interval/decrease replay plus finite proximal-gradient
soft-threshold, composite-decrease, and box-plus-L1 replay queryable while keeping duality, KKT
sufficiency, active-set method theory, SDP strong duality, general separation, and
algorithm-convergence claims in the Lean-horizon lane.
The public foundational-resource consumer query layer now also exercises the
functional-analysis/operator lane: field readiness over
`functional_analysis_and_operator_theory`, the shared operator/Chebyshev
bridge lookup, concept-scoped `bridge_finite_operator_chebyshev` Farkas pack
and checked-row queries, and checked Farkas rows for finite operators, inner
products, Chebyshev grids, interpolation/residual rows,
alternation-magnitude refutations, spectral examples, and
characteristic-polynomial arithmetic are smoke-checked through the committed JSON contract,
while Banach/Hilbert/compact-operator/Haar-space/minimax/alternation-theorem
and infinite-dimensional claims stay in the theorem-horizon lane.
The first route-note pass has also landed on the high-use learner cluster
pages for logic/proof, graph/discrete reasoning, linear algebra/optimization,
probability/statistics, and algebra/number theory.
The first proof-object anatomy learner page now follows
`proof-methods-refutation-v0` from the PHP(3,2) source claim through committed
CNF, emitted DRAT/LRAT proof objects, and same-artifact corrupted-proof
rejection.
The first Farkas certificate anatomy learner page now follows
`linear-optimization-v0` from an exact LP threshold conflict through source
SMT-LIB, emitted `UnsatFarkas` evidence, and same-artifact multiplier tamper
rejection.
The first Alethe certificate anatomy learner page now follows
`equivalence-classes-v0` from a quotient-map congruence conflict through source
SMT-LIB, emitted zero-trust `UnsatAletheProof` evidence, and same-artifact
truncated-proof rejection.
The first Diophantine certificate anatomy learner page now follows
`modular-arithmetic-v0` from a nonunit modular-inverse obstruction through
source SMT-LIB, emitted `UnsatDiophantine` evidence, and same-artifact
contradiction-row tamper rejection.
The first QF_BV bit-blast certificate anatomy learner page now follows
`finite-fields-v0` from fixed-width finite-field BV rows through source
SMT-LIB, generated DIMACS/DRAT evidence, and same-artifact truncated-DRAT
rejection.
The matrix-computation learner index now groups LU/nullspace, rank/nullity, residual,
projection, eigenpair, characteristic-polynomial, finite random-matrix,
chain-complex, operator, module, and tensor rows by replay, QF_LRA/Farkas,
QF_UF/Alethe, QF_LIA/Diophantine, Lean-horizon, and numerical-honesty
boundaries.
The matrix corpus/benchmark boundary note now separates educational matrix
examples from solver regressions, benchmark-corpus rows, and theorem-horizon
claims, so matrix resources can be reused without implying performance,
parity, numerical-stability, or general-theorem coverage.
The analysis/calculus theorem-horizon map now groups real completeness,
IVT/MVT/FTC, compactness/connectedness, sequence and recurrence convergence,
root-finding convergence, optimization convergence/duality,
measure/probability convergence, functional-analysis/operator theory, and
dynamics by finite shadow, checked evidence route, missing Lean/theorem
dependency, and next build artifact.
The real-completeness theorem-boundary page now expands that first horizon row
into a concrete dependency ledger, linking existing rational interval,
sequence-tail, monotone-prefix, metric-continuity, RCF-shadow, and finite
compactness packs to least-upper-bound, Cauchy-completeness, monotone-
convergence, compactness, and uniform-continuity proof obligations without
turning finite shadows into theorem claims.
The algebra equality-certificate boundary page now makes the finite-algebra
promotion rule explicit: table replay owns concrete structure evaluation, while
QF_UF/Alethe rows are added only for isolated equality, congruence, closure,
representative, preservation, identity-action, action-compatibility, or
bilinearity certificates.
Those four certificate anatomy stories now also have first-class bridge rows in
the foundational concept atlas, making the active proof-object routes queryable
through shared R1 vocabulary.
The set/foundations bridge rows now make powerset/Boolean algebra,
partition/equivalence roundtrips, image/preimage/inverse tables,
finite bijection/cardinality checks, and infinite-cardinality theorem horizons
queryable through the same R1 vocabulary.
The geometry and complex-analysis bridge rows now make finite coordinate,
incidence, rigid-configuration, affine, oriented-area, circle-geometry, inversion-geometry, and complex real-pair transform replay
queryable without overstating synthetic, differential, global, or analytic
theorem coverage.
The learner spine now also splits the finite topology and finite measure
first-principles stories into standalone end-to-end pages, leaving the combined
topology/measure page as a cross-field bridge rather than the only entry point.
`linear-optimization-v0` now also has a standalone LP/Farkas end-to-end page
for feasible-point replay, objective-threshold replay, checked
QF_LRA/Farkas evidence, and tampered-certificate rejection, leaving the
combined linear-system/LP page as the matrix-to-optimization bridge.
`finite-probability-v0` now also has a standalone finite probability
mass-table page for exact PMF normalization, conditional probability, Bayes
posterior replay, checked QF_LRA/Farkas bad normalization, checked bad
conditional-probability rejection, checked bad posterior rejection, finite
independence replay, checked bad-independence rejection, total variation replay,
and checked bad-total-variation rejection, leaving the broader finite-probability
page as the stochastic-process bridge.
`bounded-dynamics-v0` now also has a standalone bounded recurrence dynamics
page for exact trace replay, finite invariant checking, threshold reachability,
and checked QF_LRA/Farkas bad transition-step, bad threshold-step, and bad invariant-bound
evidence, leaving the combined finite-dynamics/Euler page as the numerical-step
bridge.
`finite-euler-method-v0` now also has a standalone finite Euler method page
for exact explicit-Euler transition replay, finite polynomial-solution error
tables, monotone invariant checks, replay-only bad max-error,
bad terminal-error, and bad-step rejection, separate checked QF_LRA/Farkas
proof rows, and the ODE/numerical-analysis Lean horizon.
`finite-operator-v0` now also has a standalone finite-dimensional operator
page for exact `l1` norm replay, row-sum operator-bound replay, finite
Chebyshev recurrence replay, replay-only malformed norm/bound/Chebyshev rows,
and separate checked QF_LRA/Farkas `qf-lra-*` evidence rows, leaving the
broader bounded-dynamics/operator page as the cross-resource bridge.
The six active proof-cookbook routes for CNF/LRAT, QF_BV, QF_LIA, QF_LRA,
QF_UF/Alethe, and Lean horizons now each name concrete math example packs that
use the route.
The first example-family row now groups the recurring finite-algebra
QF_UF/Alethe congruence conflicts under `family_finite_algebra_alethe`,
backed by the shared `math_resource_uf_routes` regression.
The second example-family row now groups recurring exact-rational
QF_LRA/Farkas infeasibility rows under `family_exact_rational_farkas`,
backed by the shared `math_resource_lra_routes` regression and scoped to
the optimization/Farkas proof-route lane.
The third example-family row now groups recurring finite Boolean CNF/LRAT
refutations under `family_boolean_cnf_lrat`, backed by the shared
`math_resource_boolean_routes` regression across logic, counting, graph,
finite-set, and finite-topology packs.
The fourth example-family row now groups recurring integer/count QF_LIA
Diophantine and checked arithmetic-evidence obstructions under
`family_integer_diophantine`, backed by the shared `math_resource_lia_routes`
regression across number-theory, induction, counting, statistics, graph-search,
polynomial, and homology packs.
The fifth example-family row now groups fixed-width QF_BV/DRAT obligations
under `family_fixed_width_bv_drat`, backed by `math_resource_bv_routes` across
finite fields, finite rings, graph coloring, and bounded number-theory residue
search/bad-witness packs.
The generated coverage, field, proof-gap, learner/proof-upgrade, and
curriculum-pressure dashboards now expose conservative R0-R6 gate/next-gate
columns and overlapping fragment-pressure buckets, making R4-to-R5 solver-reuse
candidates and Bool/CNF, QF_BV, QF_LIA, QF_LRA, QF_UF, finite-replay, and
Lean-horizon demand visible without hand-maintained scans.
The generated solver-reuse disposition audit now reports 156 promoted math
packs, 0 non-benchmark-horizon packs, and 0 unclassified rows, so future
unclassified packs and deliberate non-benchmark rows surface in a
freshness-checked queue.
The generated curriculum-status audit now separates source `curriculum_status`
from generated `resource_status`, making source `planned` rows with validated
resource packs visible as explicit `covered` versus `lean-horizon` review
items.
The first structured solver-reuse batch is now fully promoted from R4 candidate
rows into source-linked regression artifacts with pack back-links.
`logic-basics-v0`, `finite-cardinality-v0`, `graph-matching-v0`,
`graph-reachability-v0`, `graph-cut-v0`, `graph-d-separation-v0`,
`finite-compactness-v0`, `finite-connectedness-v0`,
`graph-search-runtime-v0`, `integer-lia-v0`, `natural-arithmetic-v0`, and
`number-theory-v0` are the first promoted packs from that batch:
`tiny-cnf-refutation`,
`no-injection-four-to-three`, `triangle-no-perfect-matching`,
`disconnected-no-path`, `one-edge-cut-rejected`, and
`chain-conditioned-blocks` plus `collider-unconditioned-blocks` now have
source-linked DIMACS artifacts; topology's
`bad-open-cover-rejected` and `bad-connected-claim-rejected` now do too. The
Boolean `math_resource_boolean_routes` regression checks emitted DRAT and LRAT
proof objects, while
the learner/resource map now exposes a focused d-separation causal trust
boundary that keeps those finite DAG path-blocking rows separate from causal
identification, do-calculus, probabilistic graphical-model semantics,
adjustment-set correctness, and statistical consistency.
It also exposes a focused graph-cut trust boundary that keeps finite edge and
vertex cut replay plus the one-edge CNF non-cut row separate from Menger-style
cut theorems, max-flow/min-cut, scalable algorithms, spectral cuts,
graph-partitioning guarantees, and asymptotic claims.
The graph learner map now likewise exposes a focused matching trust boundary
that keeps finite matching replay, augmenting-path replay, and the `K3`
perfect-matching CNF refutation separate from Hall/Tutte theorem coverage,
matching algorithms, weighted matching, flow reductions, graph minors, and
asymptotic claims.
It also exposes a focused reachability trust boundary that keeps finite
BFS/DFS/no-path/cut replay and the disconnected no-path CNF refutation separate
from BFS/DFS correctness, all-pairs/dynamic reachability, graph-family,
graph-minor, and asymptotic claims.
It also exposes a focused coloring trust boundary that keeps replay-only finite
coloring witnesses, checked same-color rejection, Boolean CNF/LRAT evidence,
and QF_BV/DRAT evidence separate from chromatic-number, planar-coloring,
algorithm, graph-minor, and asymptotic claims.
It also exposes a focused graph-search runtime theorem boundary that keeps
finite BFS/DFS visited-counter replay and QF_LIA bad-bound evidence separate
from asymptotic runtime, graph-family lower-bound, average-case, heuristic,
parallel-search, and benchmark claims.
`bad-dfs-cost-bound-rejected` now has a source-linked
QF_LIA artifact checked by the `math_resource_lia_routes` arithmetic-evidence
regression and `diophantine-gcd-obstruction` now has a source-linked QF_LIA
artifact checked by the `math_resource_lia_routes` Diophantine regression,
`diophantine-gcd-obstruction-qf-lia` now adds the same checked route for
`number-theory-v0`, and
`bounded-natural-negative-rejected` now has a source-linked QF_LIA artifact
checked by the `math_resource_lia_routes` arithmetic-evidence regression, while
`quadratic-nonresidue-qf-bv-drat` and `bad-square-witness-qf-bv-drat` now have
source-linked QF_BV artifacts checked by the `math_resource_bv_routes` DRAT
regression.
The first consumer-facing query layer over the committed foundational-resource
JSON contract has landed in `scripts/query-foundational-resources.py` and
`docs/foundational-resources/CONSUMER-QUERIES.md`, covering summary counts,
pack discovery, field-plus-proof-route discovery, checked-row mining,
solver-reuse rows, atlas concept lookup, and curriculum field-readiness
summaries without importing validators or generators. The latest boundary
review keeps the foundational resources
JSON-first and in-repo: promoted solver-reuse rows are consumer-readable through
the query helper, and the field-readiness smoke set now spans all 18 math
fields: logic/proof, set foundations, discrete math, graph theory, number
theory, algebra, linear algebra, analysis, topology, measure/probability,
statistics, optimization, numerical analysis, dynamics, geometry, complex
analysis, and functional/operator theory. The smoke layer also exercises
representative bridge lookups and checked-row drilldowns for the active
Boolean, Alethe, Diophantine, Farkas, and QF_BV routes; there is still no
external consumer or repeated typed API need that would justify a crate or repo
split.
The compact
[`FIELD-READINESS-QUERY-MATRIX.md`](docs/foundational-resources/FIELD-READINESS-QUERY-MATRIX.md)
now turns that full-field smoke layer into a single consumer-facing table:
one row per math field with pack/check counts, the primary readiness route,
bridge lookup terms, checked-row drilldown, and the theorem claims that remain
out of scope.
The matrix computation lane now has
[`MATRIX-COMPUTATION-QUERIES.md`](docs/foundational-resources/MATRIX-COMPUTATION-QUERIES.md),
and the query helper accepts exact `--concept` filters on `packs` and `checks`,
so consumers can discover matrix rows by bridge concept plus proof route without
parsing generated Markdown or adding a typed API.
The probability/statistics lane now has
[`PROBABILITY-STATISTICS-QUERIES.md`](docs/foundational-resources/PROBABILITY-STATISTICS-QUERIES.md),
and the foundational smoke checks concept-scoped Farkas rows for probability
mass tables, finite measure, product/integration, pushforwards, conditional
expectation, stochastic kernels, tail counts, and random-matrix moments, so
downstream consumers can discover exact finite-table resources without
promoting continuous probability, asymptotic statistics, stochastic-process
limit, simulation-quality, or floating-point inference claims.
The measure-theory lane now has
[`MEASURE-THEORY-QUERIES.md`](docs/foundational-resources/MEASURE-THEORY-QUERIES.md),
and the foundational smoke checks finite measure additivity, complement,
monotonicity, subadditivity, product measure, marginals, integration,
pushforward, conditional expectation, martingale/stopped expectation,
stochastic-kernel, hitting-time, and concentration rows through Farkas queries,
so downstream consumers can discover finite measure resources without
promoting countable additivity, Lebesgue construction, convergence theorems,
almost-everywhere reasoning, stochastic-process limits, simulation quality, or
floating-point claims.
The topology/homology lane now has
[`TOPOLOGY-HOMOLOGY-QUERIES.md`](docs/foundational-resources/TOPOLOGY-HOMOLOGY-QUERIES.md),
and the foundational smoke checks concept-scoped Boolean, Farkas, Alethe,
Diophantine, and QF_BV rows for metric shadows, compactness, connectedness,
continuity, quotient topology, specialization order, boundary/homology,
torsion, cohomology, UCT, and cup-product resources, so downstream consumers
can discover finite topology resources without promoting general topology or
algebraic-topology theorem claims.
The algebra structure lane now has
[`ALGEBRA-STRUCTURE-QUERIES.md`](docs/foundational-resources/ALGEBRA-STRUCTURE-QUERIES.md),
and the foundational smoke checks concept-scoped Alethe/QF_BV rows for
homomorphisms, group actions, module actions, ideals, and modular residue
witnesses, so downstream consumers can discover finite algebra resources
without promoting arbitrary algebraic structure theorems.
The number/arithmetic lane now has
[`NUMBER-ARITHMETIC-QUERIES.md`](docs/foundational-resources/NUMBER-ARITHMETIC-QUERIES.md),
and the foundational smoke checks concept-scoped Diophantine, QF_BV, totality,
and exact-vs-floating rows for gcd/divisibility, CRT, nonunit inverse,
fixed-width residue, quotient/ideal, and semantic-boundary resources, so
downstream consumers can discover finite arithmetic rows without promoting
analytic number theory, algebraic number theory, unbounded induction, or
floating-point guarantee claims.
The geometry resource lane now has
[`GEOMETRY-RESOURCE-QUERIES.md`](docs/foundational-resources/GEOMETRY-RESOURCE-QUERIES.md),
and the foundational smoke checks concept-scoped Farkas pack/check queries for
`bridge_coordinate_orientation_geometry` and
`bridge_finite_circle_inversion_cyclic_replay`, so downstream consumers can
discover finite geometry resources without promoting synthetic, projective,
differential, global, or higher-degree geometry theorem claims.
The graph/discrete lane now has
[`GRAPH-DISCRETE-QUERIES.md`](docs/foundational-resources/GRAPH-DISCRETE-QUERIES.md),
and the foundational smoke checks concept-scoped Boolean, QF_BV, and LIA
pack/check queries for `bridge_finite_graph_replay_obstruction`, so downstream
consumers can discover finite coloring, reachability, matching, cut,
d-separation, fixed-width coloring, and BFS/DFS runtime rows without promoting
general graph-theory or asymptotic algorithm claims.
The optimization/convexity lane now has
[`OPTIMIZATION-CONVEXITY-QUERIES.md`](docs/foundational-resources/OPTIMIZATION-CONVEXITY-QUERIES.md),
and the foundational smoke checks LP objective/Farkas rows, rational convexity
shadows, projection/residual rows, exact-vs-floating boundary rows, and
pack-specific KKT, active-set QP, SDP, gradient-descent, Armijo/Wolfe
line-search, projected-gradient, and soft-threshold/composite-decrease/box-plus-L1
proximal-gradient rows, so downstream
consumers can discover finite optimization resources without promoting
duality, KKT sufficiency, SDP strong duality, Slater conditions,
gradient-descent convergence/rates, line-search termination/convergence,
Wolfe-line-search existence/convergence, method convergence, stability, or
benchmark claims.
The functional-analysis/operator lane now has
[`FUNCTIONAL-OPERATOR-QUERIES.md`](docs/foundational-resources/FUNCTIONAL-OPERATOR-QUERIES.md),
and the foundational smoke checks finite operator/Chebyshev, eigenpair,
Rayleigh, inner-product/projection, and finite dual/tensor rows through
Farkas/Alethe queries, so downstream consumers can discover finite
functional/operator resources without promoting Banach/Hilbert-space,
compact-operator, topological-dual, minimax, alternation-theorem, stability, or
infinite-dimensional approximation claims.
The analysis/numerical/complex lane now has
[`ANALYSIS-NUMERICAL-QUERIES.md`](docs/foundational-resources/ANALYSIS-NUMERICAL-QUERIES.md),
and the foundational smoke checks bounded epsilon-delta, metric-ball,
algebraic derivative/integral, Newton/root-finding, finite dynamics/Euler,
Adams-Bashforth and BDF2 multistep, residual, exact-vs-floating, and complex
real-pair rows through Farkas queries,
so downstream consumers can discover finite analysis resources without
promoting completeness, IVT/MVT/FTC, convergence, numerical stability,
floating-point error, holomorphicity, contour-integration,
analytic-continuation, or algebraic-closure claims.
The dynamics lane now has
[`DYNAMICS-QUERIES.md`](docs/foundational-resources/DYNAMICS-QUERIES.md),
and the foundational smoke checks finite recurrence, transition, invariant,
Euler, stochastic-kernel, Markov-chain, hitting-time, and calculus-shadow rows
through Farkas queries, including Adams-Bashforth and BDF2 multistep rows, so
downstream consumers can discover finite dynamics
resources without promoting continuous ODE/PDE theory, flow/stability/
bifurcation theorems, chaos/ergodic theory, Euler convergence,
stochastic-process limits, continuous-time Markov processes, numerical
stability, or floating-point claims.
The foundations/discrete lane now has
[`FOUNDATIONS-DISCRETE-QUERIES.md`](docs/foundational-resources/FOUNDATIONS-DISCRETE-QUERIES.md),
and the foundational smoke checks Boolean proof/CNF, refutation-as-query,
finite proof-pattern, bounded induction, finite quantifier, finite
cardinality/bijection, finite Boolean algebra, finite counting,
partition/equivalence, and finite relation/function/image/preimage rows through
Boolean, Alethe, Diophantine, and LIA queries, so downstream consumers can
discover finite foundations resources without promoting proof automation, ZFC,
infinite sets/cardinality, unbounded induction, asymptotic enumeration, or
broad combinatorial theorem claims.
The proof-route lane now has
[`PROOF-ROUTE-QUERY-MATRIX.md`](docs/foundational-resources/PROOF-ROUTE-QUERY-MATRIX.md),
and the query helper accepts `routes` summaries with route aliases and optional
field scoping, so consumers can inspect route coverage before drilling into
packs or checked rows.
The foundational example-pack validator now also has committed negative
fixtures for unknown fields, metadata/check drift, and missing witness
references, and `check-foundational-resources.sh` requires those invalid packs
to fail with the expected diagnostics.
The rules/law transfer lane now has a crosswalk from math resources to concrete
policy/rule checks, with `benefit-eligibility-v0` mapped to finite predicates,
Bool/QF_LIA thresholds, temporal versioning, replayed witnesses, and proof-route
upgrade targets; source-linked Bool/QF_LIA fixtures now check its consistency,
coverage, fixed no-exception monotonicity, and active-threshold implementation
equivalence obligations through the `rules_as_code_examples` solver regression.
`authorization-policy-v0` now adds the second rules/law pack: finite
tenant/resource relations, explicit deny precedence, admin tenant guarding,
intended version-delta witnesses, and checked Bool/QF_LIA fixtures for tenant
isolation, deny precedence, admin tenant boundaries, and bounded implementation
equivalence.
`tax-benefit-arithmetic-v0` now adds the third rules/law pack: integer
thresholds, household-size adjustments, caps, active phase-out monotonicity,
effective-date witnesses, and checked Bool/QF_LIA fixtures for non-negative
benefit, cap, active phase-out monotonicity, and bounded implementation
equivalence, with the validator replaying the full piecewise finite sample.
`procurement-scoring-v0` now adds the fourth rules/law pack: finite predicate
exclusions, bid caps, encoded submission deadlines, small-business
bonus-threshold witnesses, score monotonicity, and checked Bool/QF_LIA fixtures
for debarment, late submission, bid-cap, monotonicity, and bounded
implementation-equivalence obligations.
`grant-allocation-v0` now adds the fifth rules/law pack: exact rational
allocation shares, budget balance, shelter/clinic minimum floors,
administrative caps, finite allocation witnesses, and checked QF_LRA/Farkas
fixtures for total-budget, minimum-share, cap, and bounded
implementation-equivalence obligations.
The rules/law lane now also has a generated query dashboard that reads the
five committed rule-pack JSON files, exposes 1,007 bounded sample rows, and
links deterministic generated query-row JSON for 1,766 coverage, equivalence,
threshold, cap, deadline, version-delta, monotonicity, and rational-allocation
rows without promoting the packs to legal or solver benchmarks.
`RULES-LAW-QUERIES.md` and `scripts/query-rules-as-code.py` now make that
rules/law boundary queryable by pack, proof status, generated family, and
bounded row; `just rules-as-code` smoke-checks the procurement pack, checked
obligations, quality-score query family, and late-submission generated rows.
`RULES-LAW-PATTERN-MATRIX.md` now maps that same boundary back to math-resource
concepts and proof routes, and the rules-as-code smoke gate also checks
monotonicity checks, adjacent generated families, and quality-monotonicity
rows.
`docs/learn/rules-law-trust-boundary.md` now gives learners the corresponding
source-rule -> model -> replay/check -> horizon walkthrough for the five
current rule packs.
Finite order lattices, finite permutation groups, finite vector spaces, finite
dual spaces, finite modules, finite ideals, finite tensor products, and finite
group actions now add secondary equality-heavy promotions for bad antisymmetry,
bad nonbijection, bad subspace-closure, covector-additivity, submodule
scalar-closure, ideal additive-closure plus quotient-ring representative
congruence, bilinear left-additivity, bad identity-action, and bad
action-compatibility rows.
Continue the
math-resource proof upgrades from
[`docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md`](docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md),
where modular arithmetic now promotes both the nonunit inverse obstruction and
incompatible non-coprime CRT obstruction through checked QF_LIA/Diophantine
evidence, exact statistical tests promote the bad binomial tail-count row and
the bad Fisher and multinomial p-value rows,
finite simplicial homology promotes its bad boundary coefficient, and induction
patterns promote a finite even-product parity obstruction. The
QF_LIA/Diophantine first-target set is now covered;
the first secondary statistics margin/count row is now promoted in
descriptive statistics, integer LIA is now promoted for its gcd divisibility
obstruction, bounded induction obligations are now promoted for a bounded
bad-step count checked arithmetic-evidence row, bounded natural arithmetic is now promoted
for its bad negative domain row, and the finite-probability
bad-normalization row now has a checked
QF_LRA/Farkas regression, with finite Markov chains now split so the bad
stochastic-row and false stationary-distribution replay rows feed explicit
`qf-lra-*` Farkas rows, and finite concentration now promoted for the bad
tail-bound and bad union-bound obstructions, with finite hitting times now source-linked and
promoted for the bad survival-mass and bad expected-time equations; least-squares regression is now
promoted for the bad coefficient and bad RSS-improvement rows, and bounded rational real analysis for
the bad linear-delta row, with finite conditional expectation now promoted for
the bad high-block, total-expectation, tower-property, and
variance-decomposition tables, finite Euler method now source-linked and promoted
for its bad max-error, bad terminal-error, and bad fixed-step rows, bounded dynamics now promoted
for its bad invariant-bound conflict, and finite probability now promoted for
bad conditional-probability, bad Bayes-posterior, and bad independence
conflicts, with orientation/area geometry now promoted
for its bad affine-area-scaling and bad fixed-orientation claims and numerical
linear algebra now promoted for its bad residual-bound, solution-box
upper-bound, and Jacobi error-bound rows, and random matrix finite now promoted for its bad
trace-square moment and bad expected-rank rows, with affine geometry now promoted for its bad
midpoint-coordinate, collinearity-determinant, and distance-preservation rows and inner-product spaces now
promoted for its bad negative-norm and projection-orthogonality rows, and
spectral linear algebra now promoted for its bad eigenpair and bad
Rayleigh-quotient rows, with matrix
invariants now promoted for its bad characteristic
polynomial row. The matrix-corpus regression pass now source-links the
least-squares bad-coefficients, numerical residual-bound, finite random-matrix
trace-square, spectral bad-eigenpair, and matrix-invariant bad-characteristic
SMT-LIB artifacts to the shared QF_LRA/Farkas route tests, while leaving the
strict-inequality inner-product negative-norm row on its existing inline
Farkas route until the SMT-LIB parser/evidence path accepts that artifact
shape. Polynomial factorization now promoted for its fixed
irreducible-quadratic discriminant conflict, and finite Chebyshev systems now
promoted for the duplicate-node determinant and bad interpolation-sample
conflicts, with metric continuity now promoted for the finite
bad-delta output-bound conflict, finite stochastic kernels now promoted for
the bad kernel-row normalization and bad composition-entry conflicts, and finite product measure now
promoted for the bad product-probability and bad marginal conflicts, with
finite random variables now promoted for separate bad pushforward-distribution
and bad expectation-through-pushforward QF_LRA conflicts and finite integration now
promoted for the bad expectation conflict, and finite
martingales now promoted for the bad stopped-expectation and
conditional-expectation conflicts, with
finite Markov chains carrying explicit promoted solver-reuse metadata for the
separate `qf-lra-bad-stochastic-row` and
`qf-lra-bad-stationary-distribution` conflicts after replay isolates the bad
source rows, and finite concentration carrying
source-linked promoted bad tail-bound and bad union-bound conflicts, while sequence-limit shadows
now promote a bounded Cauchy-tail max-distance threshold conflict, and
multivariable calculus now promotes a bad exact gradient-component conflict,
with calculus algebraic shadows now promoting a bad exact derivative-value
conflict, and complex-plane transforms now promoting bad conjugation-product
imaginary-part and bad unit-square real-part conflicts.
The first
secondary QF_LRA/Farkas
target set is now covered, the initial equality-heavy QF_UF/Alethe
secondary set is now covered including the finite-ideals quotient
representative row, and finite group actions now promote a bad identity-action
conflict and a bad action-compatibility conflict through checked QF_UF/Alethe
regressions, while finite continuous maps now promote a bad preimage-membership
conflict through the same checked route.
The first
QF_BV bit-blast/DRAT resource promotion now covers the
finite-rings bad distributivity and bad multiplicative-identity rows, the
finite-fields composite no-inverse and bad inverse-candidate rows, and the
graph-coloring one-bit triangle two-coloring obstruction, with bounded number
theory now promoted for the modulo-7 quadratic nonresidue row and the bad
square-root witness row; finite
compactness now contributes checked DRAT/LRAT evidence for a bad open-cover row,
finite connectedness now contributes checked DRAT/LRAT evidence for a bad
connectedness row, finite topology now contributes checked DRAT/LRAT evidence
for a missing-empty-set axiom row, induction obligations and natural arithmetic
now contribute checked arithmetic-evidence regressions for bounded bad step
counts and bounded-natural negativity, and graph search runtime contributes checked
QF_LIA arithmetic evidence for a bad finite DFS cost bound, while
cardinality principles now contributes a checked QF_LIA/Diophantine regression
for the overlapping-set false-additivity count conflict. The five active resource proof-certificate routes
now each have a route-specific tamper/rejection regression: Boolean CNF/LRAT,
QF_BV DRAT, QF_LRA/Farkas, QF_LIA/Diophantine, and QF_UF/Alethe all mutate an
emitted resource certificate and require the independent checker to reject it;
the foundational resource dashboards now report **173 promoted solver-reuse
packs**, **0 non-benchmark-horizon packs**, and **0 unclassified packs** after
the latest finite policy-iteration bad policy-value QF_LRA/Farkas promotion,
the latest finite value-iteration bad Bellman-backup QF_LRA/Farkas promotion,
the latest finite hard-margin SVM bad-bias QF_LRA/Farkas promotion,
the latest finite perceptron bad weight-update QF_LRA/Farkas promotion,
the latest finite nearest-neighbor bad squared-distance QF_LRA/Farkas promotion,
the latest finite dyadic weighted-entropy QF_LRA/Farkas promotion,
the latest finite decision-tree bad weighted-Gini QF_LRA/Farkas promotion,
the latest finite calibration/Brier bad-Brier-score QF_LRA/Farkas promotion,
the latest finite precision-recall bad-average-precision QF_LRA/Farkas promotion,
the latest finite ROC/AUC bad-AUC QF_LRA/Farkas promotion,
the latest finite confusion-matrix bad-precision QF_LRA/Farkas promotion,
the latest finite Naive Bayes bad-posterior QF_LRA/Farkas promotion,
the latest finite PCA bad-eigenvalue QF_LRA/Farkas promotion,
the latest finite linear-discriminant bad-direction QF_LRA/Farkas promotion,
the latest finite Steffensen accelerated-value QF_LRA/Farkas promotion,
the latest finite Aitken accelerated-value QF_LRA/Farkas promotion,
the latest finite secant-method bad step QF_LRA/Farkas promotion,
the latest finite Romberg extrapolated-value QF_LRA/Farkas promotion,
the latest finite cubic spline interpolation bad value QF_LRA/Farkas promotion,
the latest finite cubic Hermite interpolation bad value QF_LRA/Farkas promotion,
the latest finite Taylor polynomial bad value QF_LRA/Farkas promotion,
the latest finite-difference derivative bad value QF_LRA/Farkas promotion,
the latest finite barycentric interpolation bad value QF_LRA/Farkas promotion,
the latest finite divided-differences bad interpolation-value QF_LRA/Farkas
promotion,
the latest finite Simpson-rule bad quadrature-value QF_LRA/Farkas promotion,
the latest finite BDF2 bad implicit-multistep QF_LRA/Farkas promotion,
the latest finite Adams-Bashforth bad multistep QF_LRA/Farkas promotion,
the latest finite Crank-Nicolson bad implicit-trapezoid-step QF_LRA/Farkas
promotion,
the latest finite Backward Euler bad implicit-step QF_LRA/Farkas promotion,
the latest finite Heun bad first-step QF_LRA/Farkas promotion,
the latest finite Runge-Kutta midpoint bad first-step QF_LRA/Farkas promotion,
the latest finite GMRES bad one-step alpha QF_LRA/Farkas promotion,
the latest finite Cauchy-Riemann bad derivative real-part QF_LRA/Farkas
promotion,
the latest finite interval-arithmetic bad product-upper-bound QF_LRA/Farkas
promotion,
the latest finite rounding-shadow bad exact-vs-rounded equality QF_LRA/Farkas
promotion,
the latest finite shifted-QR bad next-step entry QF_LRA/Farkas promotion,
the latest finite QR-iteration-step bad next-step entry QF_LRA/Farkas promotion,
the latest finite polar-decomposition bad diagonal QF_LRA/Farkas promotion,
the latest finite real-Schur bad superdiagonal QF_LRA/Farkas promotion,
the latest finite orthogonal-diagonalization bad eigenvalue QF_LRA/Farkas promotion,
the latest finite LDLT bad diagonal-entry QF_LRA/Farkas promotion,
the latest finite pivoted-LU bad pivot-sign QF_LRA/Farkas promotion,
the latest finite LU bad-multiplier QF_LRA/Farkas promotion,
the latest finite Gram-Schmidt bad-projection-coefficient QF_LRA/Farkas promotion,
the latest finite Householder bad-reflection-entry QF_LRA/Farkas promotion,
the latest finite Givens bad-sine-coefficient QF_LRA/Farkas promotion,
the latest finite power-iteration bad coordinate QF_LRA/Farkas promotion,
the latest finite Gaussian-elimination bad eliminated-RHS QF_LRA/Farkas
promotion,
the latest finite Schur-complement bad scalar QF_LRA/Farkas promotion,
the latest finite Jordan-chain bad-component QF_LRA/Farkas promotion,
the latest finite Arnoldi bad-Hessenberg-coefficient QF_LRA/Farkas promotion,
the latest finite Lanczos bad-tridiagonal-coefficient QF_LRA/Farkas promotion,
the latest finite singular-value bad-bound QF_LRA/Farkas promotion,
the latest finite Cholesky bad product-entry QF_LRA/Farkas promotion,
the latest finite QR bad product-entry QF_LRA/Farkas promotion,
the latest finite Walsh-Hadamard bad transform-coefficient QF_LRA/Farkas promotion,
the latest finite-DAG topological bad edge-order QF_LIA promotion,
the latest finite-shortest-path bad potential-bound QF_LRA/Farkas promotion,
the latest finite-flow-cut bad cut-bound QF_LRA/Farkas promotion,
the latest finite-specialization-order bad `T0` QF_UF/Alethe promotion,
the latest finite-Chebyshev split into replay rows plus explicit `qf-lra-*`
Farkas rows,
the latest finite-circle-geometry bad line-intersection QF_LRA/Farkas promotion,
the latest finite-cyclic-geometry bad Ptolemy QF_LRA/Farkas promotion,
the latest finite-inversion-geometry bad inverse-distance-product QF_LRA/Farkas promotion,
the latest finite-inversion-geometry bad inverse-coordinate QF_LRA/Farkas promotion,
the latest finite-active-set-QP bad degenerate-multiplier QF_LRA/Farkas promotion,
the latest finite-active-set-QP bad inactive-slack QF_LRA/Farkas promotion,
the latest finite-active-set-QP bad free-gradient QF_LRA/Farkas promotion,
the latest finite-wolfe-line-search bad minimizer QF_LRA/Farkas promotion,
the latest finite-wolfe-line-search bad sufficient-decrease QF_LRA/Farkas promotion,
the latest finite-wolfe-line-search bad curvature QF_LRA/Farkas promotion,
the latest finite-proximal-gradient bad composite-decrease QF_LRA/Farkas promotion,
the latest finite-proximal-gradient bad box-proximal-point QF_LRA/Farkas promotion,
the latest finite-proximal-gradient bad proximal-point QF_LRA/Farkas promotion,
the latest finite-projected-gradient bad projection and bad decrease QF_LRA/Farkas promotions,
the latest inner-product bad projection-orthogonality QF_LRA/Farkas promotion,
the latest spectral bad Rayleigh-quotient QF_LRA/Farkas promotion,
the latest finite-line-search bad descent-direction and bad accepted-candidate QF_LRA/Farkas promotions,
the latest finite-line-search bad Armijo QF_LRA/Farkas promotion,
the latest finite-gradient-descent bad descent-bound, bad step-coordinate, and bad decrease
QF_LRA/Farkas promotions,
the latest finite-SDP bad objective, bad duality-gap, and bad slack-entry
QF_LRA/Farkas promotion,
the latest finite-KKT bad stationarity and bad complementarity QF_LRA/Farkas
promotion,
the latest finite-separation split into replay-only bad convex-combination and
bad separator rows plus separate `qf-lra-*` QF_LRA/Farkas proof rows,
the latest finite-root-finding split into replay-only bad Newton-step and
bad bisection-width rows plus separate `qf-lra-*` QF_LRA/Farkas proof rows,
the latest finite-condition-number bad upper-bound QF_LRA/Farkas promotion,
the latest bounded-dynamics split into replay-only bad transition-step,
bad threshold-step, and invariant-bound rows plus separate `qf-lra-*`
QF_LRA/Farkas proof rows,
complex-algebraic bad product-coordinate and bad norm-squared QF_LRA/Farkas
promotion,
finite-operator bad `l1` sum-norm QF_LRA/Farkas promotion,
finite-operator bad operator-bound QF_LRA/Farkas promotion,
coordinate-geometry bad midpoint-coordinate and squared-distance QF_LRA/Farkas
promotion,
incidence-geometry bad intersection-coordinate and point-on-line QF_LRA/Farkas
promotion,
rigid-configuration bad translation-image and distance-table QF_LRA/Farkas
promotion,
finite-measure-monotonicity bad subset-measure and bad union-subadditivity
QF_LRA/Farkas promotion,
bounded-monotone-sequence explicit bad upper-bound and bad tail-gap
QF_LRA/Farkas proof rows,
finite-recurrence-prefix bad Fibonacci-value and bad affine-step QF_LRA/Farkas
promotion,
finite-topology missing-empty-set Bool/CNF DRAT/LRAT promotion,
finite-measure bad-complement QF_LRA/Farkas promotion,
real-algebra RCF-shadow negative-discriminant QF_LRA/Farkas
promotion, polynomial-factorization discriminant QF_LRA/Farkas promotion,
cardinality-principles overlap-additivity count QF_LIA/Diophantine
promotion,
induction-obligations bounded bad-step count checked QF_LIA arithmetic promotion,
complex-plane bad conjugation-product imaginary-part and bad unit-square
real-part QF_LRA/Farkas promotions,
calculus-algebraic false-derivative QF_LRA/Farkas promotion,
multivariable-calculus bad-gradient QF_LRA/Farkas promotion,
sequence-limit bounded Cauchy-tail QF_LRA/Farkas promotion,
calculus Riemann-sum false-integral QF_LRA/Farkas promotion,
finite-predicate Bool/CNF quantifier-expansion promotion,
polynomial-identities false-root QF_LIA/Diophantine promotion,
finite generating-functions QF_LIA/Diophantine coefficient-convolution
promotion, PHP(3,2) counting/refutation Bool/CNF promotions, and the replay-only
classification pass for bounded dynamics, plus finite-rings bad
multiplicative-identity, finite-fields bad inverse-candidate, and
number-theory bad square-root QF_BV plus gcd-obstruction QF_LIA promotions,
plus the earlier
rational-order, gcd/Bezout, Bool/CNF finite-set/proof-method, QF_LRA
linear-algebra/optimization/convexity, finite-probability, QF_UF, QF_LIA, and
QF_BV source-metadata promotion batches;
prefer the next
proof-frontier lane or equality-heavy pack that can carry a small checked
certificate and a resource-backed regression.

## ⚠ Course correction (2026-06-23): MEASURE, don't seed

**Diagnosis (evidence-based).** ~150 commits over 24h moved **zero** Z3/cvc5
metrics. Verified causes:
1. **Measurement vacuum.** Only **one** division is corpus-measured (QF_BV p4dfa).
   All the new work — interpolation, CHC/PDR/IMC, abduction, online combination,
   datatypes, the proof certs — is on divisions **nothing measures**. Real
   decide-rate gains happened (fuzz-measured: QF_NRA 109→64, QF_NIA 498→146,
   QF_UFLIA 311→18) but are **invisible** because no committed corpus vs Z3 records
   them. *You cannot show progress you do not measure.*
2. **Ledger-over-corpus.** The cadence became *seed engine → mark Validated/Checked
   → register a ledger row → next engine.* That optimizes **breadth + assurance**
   (the ledger). Parity metrics measure **depth + performance** (the corpus). A
   ledger row is **not** progress toward parity; a measured PAR-2 is.
3. **QF_BV bottleneck untouched.** The one measured metric is gated on
   batsat-path search / word-level reduction. The recent SAT heuristics (VSIDS,
   Luby, LBD, phase-saving) landed in the **generic CDCL(T) Dpll** (`lra_online.rs`,
   the *theory* loop) — a different code path from the QF_BV solver
   (`solve_with_rustsat_batsat`/`native_cdcl`). So they cannot move QF_BV.

**The correction (binding until lifted):**
- **Measurement is the gate, not an afterthought.** No fragment may be called
  "parity"/"competitive" without a **committed measured corpus vs Z3/cvc5**
  ([P4.5](docs/plan/track-4-usecases-frontend/P4.5-benchmarking.md)). Until then its
  status is "seeded/decides," never "parity." (See the
  [maturity ladder](#true-parity-the-maturity-ladder-and-the-measurement-debt-2026-06-23).)
- **Fastest real progress = measure what already improved.** Stand up committed
  per-division corpora (QF_LRA, QF_LIA, QF_UF, then QF_NRA/NIA) vs Z3 *now* — the
  gains already exist (fuzz-measured); measuring them makes them visible **today**.
  The new oracle-free corpus gate (`tests/corpus_regression.rs`) is the credibility
  substrate; the missing piece is the **measured PAR-2** harness across divisions.
- **Seed moratorium.** Do **not** add another new engine seed until ≥2 existing
  divisions are *measured-competitive*. A 12th seeded engine is worth less than
  QF_LRA proven on a real corpus.
- **QF_BV work must hit its real bottleneck** — batsat-path search (kissat-class
  techniques in the native core) or deeper word-level reduction — not the theory
  loop. SAT heuristics in `lra_online.rs` do nothing for QF_BV.
- Proof/certification work still has value (it widens the *Certifying* moat we
  already lead) — but it advances assurance, **not** the parity metric; budget it
  accordingly, behind measurement.

**Progress (2026-06-24): the measurement gate now exists.**
[`axeyum-bench/examples/measure_corpus.rs`](crates/axeyum-bench/examples/measure_corpus.rs)
shells the system `z3` binary against any logic's corpus and times axeyum's
`check_auto` on the same files → decided counts, agreement, DISAGREE, **PAR-2 for
both**. First fair numbers (cvc5 slices, both-parse, 10 s, **DISAGREE=0**):
QF_BV 35/35, QF_ABV 8/8, QF_FP 5/5, QF_LRA 5/5 — **parity**; QF_LIA **8/9 vs 9/9**
(z3 ahead by one and far faster — the first honest measured gap). Artifacts under
`bench-results/measured/`.
- **Methodology lesson (load-bearing):** cvc5's own `test/regress` is
  *solver-flavored* — files carry cvc5-specific `(set-option :bv_solver/:incremental)`
  and non-BV-array logics that **z3 rejects at parse**. Scoring those as z3 misses
  fakes an axeyum win (a permissive parser is not solving power); the harness
  **excludes** them (`z3_rejected_unfair`). For a *fair* parity number, prefer a
  **neutral SMT-LIB corpus** over a competitor's regress suite.
- **These are easy instances** — "parity" here means both trivially solve. The
  easy corpus *hides* the depth gaps; the next step is harder neutral per-division
  corpora (where QF_LIA already hints z3 is ahead). Measurement is no longer the
  blocker — corpus *difficulty/neutrality* is.

**Measurement now DISCHARGED (2026-06-24).** The parallel agent generalized this
into a committed, regenerable **[`bench-results/SCOREBOARD.md`](bench-results/SCOREBOARD.md)**
— **24 logic fragments, DISAGREE = 0 everywhere; decided/compared totals live in the generated scoreboard**
— plus the oracle-free per-lever frontier dashboard. The "MEASURE, don't seed"
correction is answered: the weak rows now *name* the blockers (see
[`docs/PARITY-STATUS-AND-PATH.md`](docs/PARITY-STATUS-AND-PATH.md)). The strategic
question is no longer "are we measured" — it is the next section.

**Verification hygiene (2026-06-27).** The solver crate's full all-targets
clippy gate is clean again:
`CARGO_BUILD_JOBS=2 cargo clippy -p axeyum-solver --all-targets -j1 -- -D warnings`.
Keep this gate green for solver/proof/frontend slices; broad capability work is
only useful if the core crate remains easy to audit and re-run.

## Strategy: work backwards from Pareto dominance (2026-06-24)

**The decide-rate race is the wrong target.** Z3/cvc5 have ~20 years of tuning;
the scoreboard confirms axeyum trails on the hard rows (QF_NRA-cvc5 24%, Int-indexed
arrays ~0%, infinite-domain quantifiers 0%). Chasing "match Z3's decide% everywhere"
is a catch-up race axeyum loses on most rows, indefinitely. **Stop optimizing for
global decide-parity.**

**Instead: define and grow the set of fragments where axeyum *Pareto-dominates* the
alternatives.** A fragment is **Pareto-dominant** when axeyum is, on it,
simultaneously: **(1) decide-competitive** with Z3 (parity on that fragment),
**(2) sound** (DISAGREE = 0 — already true everywhere), **(3) Lean-certified**
(every `unsat` carries a kernel-checkable proof), and **(4) pure-Rust / `unsafe`-free /
WASM / deterministic**. On such a fragment axeyum **strictly beats every alternative**:
- vs **Z3 alone** — Z3 ties on decide but has no Lean-checkable proof and is C++ (no
  WASM, memory-unsafe);
- vs **cvc5 alone** — ties on decide, has Alethe/LFSC but not an *integrated in-tree
  Lean-kernel-checked* artifact in a pure-Rust stack;
- vs **Lean alone** — Lean cannot *auto-decide* the fragment; axeyum does, and hands
  back a proof its kernel accepts.

That is a real, defensible "we win here" — unlike "we almost match Z3's decide-rate."

**The new headline metric: four-constraint Pareto-dominance coverage.** Drive it
up per measured division: decided within budget, DISAGREE = 0, every `unsat`
has a re-checked trust-hole-free Lean certificate, and the route remains
pure-Rust / deterministic / `unsafe`-free. A fragment count is too easy to game
by slicing; coverage on a neutral corpus is the control surface.

**Working backwards — what that implies for priorities:**
1. **The binding axis is certification, not decide-rate.** Soundness (2) and
   pure-Rust (4) are already universal; decide-competitiveness (1) already holds on
   the strong rows (QF_FP/QF_UFBV/QF_UFFF 100%, QF_AUFBV 93%, QF_LIA 91%, QF_ABV 88%,
   QF_BVFP/QF_FF/QF_LRA/QF_SEQ ~80%). The **missing leg is (3) Lean certification** on
   those already-strong fragments. **That is where the structural win is, and it is
   the axis Z3 cannot match at all.** → invest the cert lane (Track 3 / PARITY Tier C)
   on the **strong-decide** fragments first, not the weak ones.
2. **Name the beachhead already won.** QF_BV (DRAT), datatypes (complete axiom-free
   Lean chain), QF_LRA (Farkas), QF_UF (congruence) are at/near all-four **today** —
   the first Pareto-dominant fragments. Make this an explicit, tracked list.
3. **The hard rows (NRA high-degree, Int-arrays, infinite quantifiers) are NOT a
   dominance opportunity near-term** — axeyum can't be decide-competitive there for a
   long time. Treat them as "match Z3's *practical* heuristics where cheap, honest
   `unknown` otherwise" — do **not** sink the dominance budget into a decide-rate
   catch-up race there.
4. **vs Lean is a pure-win axis: ship the tactic backend.** axeyum auto-discharging
   SMT-decidable Lean goals with kernel-checked proofs (the lean-smt-style bridge,
   [P3.7](docs/plan/track-3-proof-lean/P3.7-lean-reconstruction.md)) Pareto-dominates
   manual Lean on the decidable fragment — automation Lean lacks, trust Lean demands.

**The inversion in one line:** *we do not win by deciding as much as Z3; we win by
being the only stack that decides it, proves it to a Lean kernel, and runs anywhere
— so grow the fragment set where all four hold, and stop spending on the decide-race
where we structurally can't lead.*

### Refined by source-grounded review (2026-06-24, two Opus critics vs real Z3/cvc5/lean-smt)

The thesis **survives** adversarial review — but four corrections, each verified
against competitor source, are now binding:

1. **The cert moat is real AND unoccupied — confirmed from source.** cvc5's proofs
   are complete *only in "safe mode"* (which disables CAD/strong engines); **CAD/NRA
   has no checkable proof rule at all**; Alethe omits nonlinear/arrays/datatypes.
   lean-smt is **beta**, needs the **cvc5 C++ binary in the loop**, and has a
   structural **`sorry` fallback** (BV reconstruction is `add`/`eq`-only). So
   axeyum's *integrated, pure-Rust, in-tree, `#print axioms`-clean, trust-hole-free*
   self-checking is a position **no incumbent occupies.** Keep this as a *standing
   guard*: re-verify these claims whenever `references/` is refreshed (a moat that
   could silently rot if cvc5/lean-smt close their holes).
2. **Scope "dominant *today*" honestly: kernel-cert ≠ DRAT-cert.** Only the QF_BV
   **bitwise/comparison sub-fragment** reconstructs to the Lean *kernel*; mul/rem/shift
   carry a **DRAT** proof (strong, but not the kernel artifact the thesis sells).
   Every "Pareto-dominant today" claim must name the sub-fragment that is
   *axiom-clean Lean-kernel-checked*, and distinguish it from the DRAT-certified
   superset. Conflating the two is the ledger-over-substance slip the 06-23
   correction forbade.
3. **The headline metric must not be a fragment *count* (gameable by slicing).**
   Use, per division, a **four-constraint coverage %** on a *neutral, non-trivial*
   corpus: `dominant%(D) = |decided-within-budget ∧ emits a re-checked, trust-hole-free,
   #print-axioms-clean Lean cert| / |non-trivial instances|`, reported with PAR-2 vs
   Z3. An instance that decides but only DRAT-certifies does **not** count toward the
   Lean-dominant fraction.
   **READINESS REPORT LANDED (2026-06-25):**
   [`bench-results/DOMINANCE.md`](bench-results/DOMINANCE.md), regenerated by
   [`scripts/gen-dominance-scoreboard.py`](scripts/gen-dominance-scoreboard.py),
   now combines the measured decide/PAR-2 rows with a conservative proof-route
   audit queue. Rows without a committed audit remain readiness entries because
   the division baseline JSONs do not record per-instance Lean reconstruction
   coverage. Current report: **35 rows**, **DISAGREE = 0** (decided/compared
   totals: see the generated scoreboard), with **23 complete exact audit rows**
   and **0 remaining first-queue rows** marked `audit now` for evidence/Lean
   coverage measurement.
   **QF_UF REMEASURE + SMT-LIB DIV/MOD GUARD LANDED (2026-06-26):**
   remeasuring the QF_UF rows exposed a real soundness hazard: SMT-LIB leaves
   integer/real division by zero and integer modulo by zero underspecified, while
   Axeyum's executable evaluator uses deterministic total conventions for model
   replay. The solver now declines arithmetic routes whose divisor is not a
   syntactically known nonzero constant until an explicit underspecification
   encoding exists. The cvc5 QF_UF bounded rows are now **44/82 decided** with
   **DISAGREE=0**; the overbound row remains **4/6 decided**, **DISAGREE=0**.
   **QF_UF DECLARED-SORT EXACT AUDIT INGESTED (2026-06-26):**
   the refreshed bounded declared-sort QF_UF row now has a complete committed
   dominance audit. Equality-only conflicts over declared uninterpreted carrier
   sorts now route to the EUF Lean fragment even without an `Apply` node, and the
   zero-trust evidence lane tries the pure EUF Alethe congruence emitter directly.
   This closes the `parallel-let` Lean gap. A follow-up SAT evidence pass made
   the arithmetic/Diophantine optional evidence prepasses decline declared-sort
   rows with no Int/Real content, closing the `parser/as` and `ite4` audit
   errors. A follow-up set-cardinality pass added a checked lowered
   `set.card`→BV-popcount certificate, closing both the `sets/card` bit-blast
   trust-hole row and the `sets/card-6` evidence timeout. A follow-up
   Boolean-EUF pass added a checked equality-skeleton refutation bridge for
   pure-UF rows whose contradiction is hidden behind `not =>`, CNF, or Boolean
   `ite`, closing `simple-uf`, `uf/cnf-and-neg`, and `uf/cnf-ite`. A follow-up
   UF+arithmetic congruence pass added a checked Ackermann/congruence residual
   certificate for the mixed `list`/integer `bug303` row: congruence over the
   declared carrier sort derives the needed integer equality, then arithmetic
   DPLL refutes the retained Boolean-structured linear-arithmetic core. A final
   direct-evidence routing pass lets structural certificates run before the
   pure-real LRA/NRA evidence branch, so the nonlinear-extension
   `issue3970-nl-ext-purify` row is now certified as a term-identity
   contradiction from its expanded `distinct` disequality `(not (= t t))`. The
   exact row is now **44/44 dominant (100.0%)**, **Lean unsat 15/15 (100.0%)**,
   with **mismatches=0**, **audit_errors=0**, **timeouts=0**, and no remaining
   evidence gaps.
   **QF_UF OVERBOUND EXACT AUDIT INGESTED (2026-06-26):**
   the refreshed overbound declared-sort QF_UF row now has a complete committed
   dominance audit for its decided slice. The new online Boolean-EUF certificate
   handles the three overbound UNSAT stressors whose equality skeletons exceed
   the exhaustive Boolean-EUF case bound: the checker re-runs the deterministic
   online EUF DPLL(T) refuter on the original assertions, rejects non-pure-EUF
   shapes, and carries no trust steps. This closes `uf/cnf_abc`, `proof00`, and
   `proofs/macro-res-exp-crowding-lit-inside-unit`; the row is now
   **4/4 dominant (100.0%)**, **Lean unsat 3/3 (100.0%)**, with
   **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The underlying
   decide-rate row remains **4/6 decided**; this closes certification for the
   currently decided slice, not the two undecided instances.
   **QF_UFLIA BOUNDED REMEASURE + AUDIT REFRESH LANDED (2026-06-26):**
   the bounded declared-sort QF_UFLIA baseline was stale after the mixed
   UF+arithmetic congruence route landed. Re-running the committed Z3 comparison
   now decides `bug303` as `unsat`, agrees with Z3, and moves the row from
   **5/6** to **6/6 decided (100.0%)** with **DISAGREE=0** and PAR-2 mean
   **0.002 s**. The exact dominance audit is refreshed at **6/6 dominant
   (100.0%)**, **Lean unsat 2/2 (100.0%)**, with **mismatches=0**,
   **audit_errors=0**, and **timeouts=0**.
   **QF_UFLIA PARENT EXACT AUDIT INGESTED (2026-06-26):**
   the parent `qf-uflia-cvc5-regress-clean` row now has a complete committed
   dominance audit for its six decided instances. The row is **6/6 dominant
   (100.0%)**, **Lean unsat 2/2 (100.0%)**, with **mismatches=0**,
   **audit_errors=0**, and **timeouts=0**; the two overbound timeout rows remain
   decide-rate work, not certification gaps for the decided slice.
   **QF_UFLIA PARENT ROW REMEASURE LANDED (2026-06-26):**
   the parent cvc5-regress-clean QF_UFLIA baseline was still a stale bounded
   snapshot. Re-running it over the actual parent corpus now records
   **6/8 decided (75.0%)**, **unsupported=0**, **oracle-compared=6/8**,
   **DISAGREE=0**, and PAR-2 mean **5.001 s**. The two remaining blockers are
   the real overbound `Timeout` rows, not parser/command-surface unsupported
   rows. A narrow paired-bound substitution prototype was tested and deliberately
   not committed: even after avoiding recursive-rewrite stack overflow on the
   generated formulas, it did not certify the overbound rows within the 10 s
   budget. The next useful move there is a deeper arithmetic/UF Boolean-skeleton
   reduction, not another shallow equality-propagation seed.
   **QF_UFLIA OVERBOUND EQUALITY PROPAGATION PROBE RETAINED (2026-06-26):**
   the online LIA theory now soundly propagates integer equality atoms from
   LP-infeasible strict branches (`eq=true`) or an LP-infeasible equality branch
   (`eq=false`), with direct unit coverage. This is a narrow DPLL(T) prune, not a
   row closure: both overbound files still time out in the same 873-atom lazy-LIA
   skeleton with 1433 upfront bound lemmas. A broader static-bound experiment that
   included complement bounds and removed the large-atom implication guard was
   rejected because it inflated upfront lemmas to 5484 without deciding either
   row. Next work should instrument lazy UF+LIA CEGAR iterations and attack SAT
   relevance / Boolean-skeleton reduction, not add more shallow bound seeding.
   **QF_UFLIA OVERBOUND DISPATCH DIAGNOSTICS LANDED (2026-06-26):**
   lazy function-consistency CEGAR `unknown`s now report refinement counters, and
   generic `lia-dpll` budget `unknown`s over UF queries report when UF-aware routes
   were not reached plus the Ackermann pair count. The two overbound rows both
   show the same immediate shape at short budget: `lia-dpll` exhausts the budget
   first, `arithmetic_function=true`, `ackermann_pairs=282`; the UF-aware lazy
   route is not reached by `check_auto`. The next useful move is therefore route
   scheduling / shared-deadline work so admitted arithmetic-UF overbound instances
   get a UF-aware probe before opaque-app LIA DPLL consumes the budget. If that
   probe reports `sat_candidates=0`, then the blocker is the 873-atom function-free
   Boolean arithmetic skeleton itself.
   **BOUNDED PRE-LIA UF+ARITH PROBE LANDED (2026-06-26):**
   small non-array integer UF+arithmetic instances over the eager Ackermann bound
   now get a cloned, capped lazy UF+arithmetic probe before generic opaque-app
   `lia-dpll`; probe errors decline and fall through instead of changing solver
   semantics. The cvc5 generated overbound rows are deliberately outside this
   probe's admission cap (**1248 assertions > 256**, `ackermann_pairs=282`), because
   the cloned probe duplicates the same large function-free arithmetic skeleton
   solve and costs seconds even with a tiny nominal timeout. Their next lever is
   not "try lazy CEGAR earlier" anymore; it is a cheaper relevance/global-deadline
   or first-model strategy for the 873-atom arithmetic Boolean skeleton.
   **ONLINE LIA TIMEOUT STATS LANDED (2026-06-26):**
   online LIA DPLL(T) timeouts now report a stable search-state snapshot
   (variables, theory atoms, clause counts, trail depth, decisions, conflicts,
   restarts, reductions). On both generated QF_UFLIA overbound rows at 1 s the
   generic opaque-app LIA path times out with **vars=3873**, **theory_atoms=485**,
   **clauses=10651**, **trail=1314**, **decisions=1**, **conflicts=0**,
   **learned_live=0**, and **restarts=0**. This rules out conflict-learning churn
   as the immediate short-budget blocker: the route burns its budget during the
   first giant propagation / repeated LIA-feasibility phase before any useful SAT
   skeleton exploration. Next work should add relevance filtering, batched/cheap
   propagation, or a first-model/skeleton precheck before asserting 1k+ literals
   through the incremental LIA theory.
   **DEFERRED LARGE ONLINE LIA FEASIBILITY LANDED (2026-06-26):**
   the online LIA driver now switches large skeletons (>=128 LIA atoms or >=4096
   CNF clauses) to a sound deferred-feasibility mode: Boolean assignments are
   recorded cheaply, one full LIA feasibility check runs at the theory-propagation
   boundary, infeasible live sets are reported as ordinary theory-conflict
   propagations, and expensive LP entailment probes are skipped. Core minimization
   is also skipped in this mode, so the fallback does not reintroduce hundreds of
   LIA checks just to shrink a conflict. On the two generated QF_UFLIA overbound
   rows at 1 s, the timeout now moves past the online first-propagation stall and
   reaches the legacy lazy arithmetic loop: **31-33 rounds**, **873 atoms**,
   **1433 bound lemmas**, **31-33 blocking lemmas**. The rows are still `unknown`;
   the next lever is the legacy 873-atom arithmetic refinement loop / route
   scheduling, not online DPLL(T)'s initial propagation.
   **QF_UFLIA OVERBOUND ROUTE SCHEDULING LANDED (2026-06-26):**
   large non-array integer UF+arithmetic queries whose Ackermann pair count is
   over the eager bound now skip generic `lia-dpll` after the exact linear
   refuters decline, and fall through to the UF-aware lazy CEGAR route. This
   avoids solving the same large function-free arithmetic abstraction twice.
   The generated overbound rows now trace as: pre-LIA cloned probe skipped
   (`1248 > 256` assertions), `lia-simplex` unsupported, `lia-dpll` explicitly
   skipped for overbound UF+arithmetic, then `uf-arith-lazy-overbound` owns the
   single abstraction solve and reports **applications=42**, **function_groups=3**,
   **potential_pairs=282**, **solve_rounds=1**, **sat_candidates=0**, and no
   pair checks / lemmas before the 873-atom arithmetic abstraction times out after
   about **32** lazy-LIA rounds. The rows remain `unknown`; next work is the
   arithmetic abstraction itself (relevance / assumption filtering or a cheaper
   first-model / UNSAT-core-producing skeleton loop), not more route duplication.
   **LIA LP CORE DIAGNOSTICS LANDED (2026-06-26):**
   integer simplex collection now preserves the source assertion for each
   generated constraint, and the arithmetic solver exposes a self-checked
   LP-relaxation unsat-core helper from Farkas multipliers. The lazy arithmetic
   loop tries this relaxation core before the generic minimizer and now reports
   learned theory-core sizes on budget `unknown`. On both generated QF_UFLIA
   overbound rows at 1 s the route remains `unknown`, but the timeout now says
   **873 atoms**, **1433 bound lemmas**, **32 blocking lemmas**, and
   **core_len_last=min=max=avg=2**. That rules out oversized dynamic arithmetic
   cores as the immediate blocker. The next lever is SAT/search relevance over
   many tiny bound conflicts in the generated arithmetic skeleton: assumption
   filtering, a cheaper first-model/core-producing loop, or branch-selector
   pruning.
   **ARITHMETIC ORDER POLARITY SHRINK LANDED (2026-06-26):**
   strict arithmetic orders now abstract as Boolean negations of their non-strict
   reversed-order representative (`a < b` as `¬(b <= a)`, `a > b` as
   `¬(a <= b)`) instead of allocating a second unrelated SAT atom for the
   complement. The skeleton simplifier also folds generated Boolean-definition
   tautologies (`¬(A∧B)∨A`, `¬(A∧B)∨B`, `(A∧B)∨¬A∨¬B`) before CNF encoding. On
   both generated QF_UFLIA overbound rows at 1 s, the abstraction now reports
   **461 atoms**, **372 upfront bound lemmas**, and **61** lazy-LIA rounds
   (previously **873 / 1433 / ~32**). A 10 s diagnostic reaches an actual UF CEGAR
   candidate, checks all **282** possible function-consistency pairs, and learns
   **5** Ackermann lemmas before timing out in the second, **477-atom**
   arithmetic abstraction. This is real search movement but not a row closure;
   next work should target the post-CEGAR arithmetic skeleton, especially
   assumption/core-guided solving or relevance pruning after UF lemmas are added.
   **LAZY UF CONSISTENCY BATCHING LANDED (2026-06-26):**
   the lazy UF CEGAR loop now can pre-seed up to 256 cheap congruence lemmas
   whose argument tuples are syntactically equal or equal under top-level fixed
   integer bounds, and its timeout telemetry reports `preseeded_lemmas`.
   Once a candidate has a real functional-consistency violation, the loop now
   batches every same-candidate equal-argument pair rather than only the
   result-different pair, avoiding a later rediscovery round while still not
   adding gratuitous lemmas for already-consistent SAT candidates. On the two
   generated QF_UFLIA overbound rows, pre-seeding finds **0** lemmas because the
   equal UF arguments depend on branch/model choices such as `fmt1`, so the
   1 s result is intentionally unchanged: **461 atoms**, **372 bound lemmas**,
   **61** rounds, no candidate. At 10 s the first row still reaches one UF CEGAR
   candidate, but now records **equal_arg_pairs=6**, **violated_pairs=5**,
   **lemmas_added=6**, then times out in a **479-atom** post-CEGAR arithmetic
   abstraction. This rules out missed same-candidate UF consistency as the main
   blocker; the practical next lever remains post-CEGAR arithmetic relevance /
   assumption-core solving.
   **MODEL-GUIDED BOUND CONFLICT BATCHING LANDED (2026-06-26):**
   the lazy arithmetic DPLL loop now learns up to 32 independent simple
   integer-bound conflicts from the same SAT candidate before re-solving, instead
   of adding one cheap two-bound core per round. This keeps the same certified
   arithmetic-lemma path while increasing useful conflict density. The two
   generated QF_UFLIA overbound rows remain `unknown`, but the 1 s diagnostics
   now report **461 atoms**, **372 bound lemmas**, **29** lazy-LIA rounds, and
   **238** blocking lemmas (down from **61** one-core rounds). At 10 s the first
   row still reaches one UF candidate and learns **6** UF consistency lemmas, then
   times out in the **479-atom** post-CEGAR arithmetic skeleton after **87**
   lazy-LIA rounds and **296** blocking lemmas. The next practical move is
   relevance / assumption-core solving or branch-selector pruning in that
   post-CEGAR arithmetic skeleton, not more individual core extraction.
   **BOUNDED COMPLEMENT-BOUND IMPLICATIONS LANDED (2026-06-26):**
   the upfront integer-bound implication pass now also seeds adjacent
   monotonicity for complement literals (`not (x <= 1)` as `x >= 2`) while
   retaining the existing 512-atom admission guard and 4096-lemma cap. This is
   the controlled version of complement-bound pruning, not the rejected broad
   experiment that removed the large-query guard. The two generated QF_UFLIA
   overbound rows remain `unknown`, but 1 s diagnostics now report **461 atoms**,
   **642 bound lemmas**, **27** lazy-LIA rounds, and **171** dynamic blocking
   lemmas. At 10 s the first row learns **5** UF consistency lemmas under the
   pruned skeleton, then times out in a **475-atom** post-CEGAR arithmetic
   skeleton after **60** lazy-LIA rounds and **200** dynamic blocking lemmas.
   The remaining blocker is still relevance / assumption-core solving in that
   post-CEGAR arithmetic skeleton.
   **BOOLEAN-SUPPORT ARITHMETIC CHECKS LANDED (2026-06-26):**
   lazy arithmetic DPLL now extracts a deterministic Boolean justification
   support from each SAT skeleton candidate and theory-checks that support before
   checking the solver's full arbitrary Boolean assignment. This stops dead
   branches of generated selector ladders from forcing irrelevant arithmetic
   conflicts first; any supported model is still replay-gated against the
   original assertions, with fallback to the previous full-assignment check if
   replay fails. The two generated QF_UFLIA overbound rows remain `unknown`, but
   1 s diagnostics now report **461 atoms**, **642 bound lemmas**, **21**
   lazy-LIA rounds, and **29** dynamic blocking lemmas. At 10 s the first row
   reaches **4** UF CEGAR solve rounds and **3** SAT candidates, checks **830**
   function-consistency pairs, finds **14** equal-argument pairs and **9**
   violations, learns **14** UF lemmas, then times out in outer
   `lazy UF+arithmetic` convergence. The next blocker is UF CEGAR convergence
   and relevance after several candidate models, not dead-branch arithmetic
   churn.
   **SUPPORT-PATH DIAGNOSTICS LANDED (2026-06-26):**
   lazy arithmetic DPLL budget `unknown` details now report deterministic
   support-path counters (`support_attempts`, support conflict batches,
   support-model replay failures, and full-assignment fallbacks). Two candidate
   pruning experiments were measured and rejected: full raw Ackermann pre-seeding
   inflated the post-CEGAR arithmetic skeleton, and raw pre-abstraction
   Boolean/bound folding slightly shrank the initial skeleton but reduced 10 s
   UF CEGAR progress. The retained diagnostic change preserves the support-first
   baseline: 1 s rows still show **461 atoms**, **642** bound lemmas, **21**
   lazy-LIA rounds, and **29** blocking lemmas, now with
   **support_attempts=21**, **support_conflict_batches=21**, and
   **full_fallbacks=0**. At 10 s the first row remains **4** UF CEGAR rounds,
   **3** SAT candidates, **14** learned UF lemmas, then an outer deadline. Next
   practical lever: incremental/relevance-preserving arithmetic across UF CEGAR
   rounds, or a measured narrow guarded-congruence preseed; broad preseed and
   broad simplification are explicitly rejected for these rows.
   **UF PAIR PROFILE LANDED; GUARDED PRESEED REJECTED (2026-06-26):**
   `axeyum-bench --example uf_pair_profile` now reports deterministic
   same-function application groups, potential Ackermann pair categories, and
   bounded concrete samples for an SMT-LIB file. On the hard overbound row it
   reports **42** applications, **3** function groups, **282** potential pairs,
   and **214** constant-vs-constant pairs. A capped **64** unary-Int
   nonconstant/constant congruence preseed was measured and rejected before
   commit: it grew the arithmetic abstraction to **673 atoms**, spent 10 s in
   **297** support-conflict batches, and reached **0** UF candidates. This
   narrows the next lever further: preserve/reuse arithmetic learning across UF
   CEGAR rounds or make the arithmetic solve incremental under added UF lemmas;
   more upfront congruence seeding is not promising on this row.
   **REUSABLE ARITHMETIC LEMMAS LANDED (2026-06-26):**
   lazy UF+arithmetic CEGAR now carries dynamic arithmetic conflict clauses
   across strengthened UF refinement rounds. The reusable clauses are rebuilt
   over original arithmetic terms rather than prior `!arith_atom_N` symbols, and
   static upfront bound lemmas are not carried because they are regenerated per
   solve. The generated overbound rows remain `unknown`, but the frontier moves:
   both 1 s target rows now reach **42** support-conflict rounds and **56**
   reusable arithmetic lemmas, and the 10 s hard row reaches **6** UF CEGAR
   rounds, **5** SAT candidates, **1359** pair checks, **23** equal-argument
   pairs, **16** violations, and **23** learned UF lemmas before the outer
   deadline, carrying **357** reusable arithmetic lemmas by the final timeout.
   Next practical lever: keep the arithmetic SAT core warm directly or make UF
   lemma addition incremental inside one combined skeleton; the row still needs
   convergence/relevance after several candidate models.
   **WARM ARITHMETIC SKELETON LANDED (2026-06-26):**
   the lazy arithmetic DPLL loop is now an `IncrementalArithDpll` state, and
   lazy UF+arithmetic CEGAR asserts newly learned UF congruence lemmas into the
   same warm arithmetic Boolean skeleton. The term-level reusable arithmetic
   lemma path remains as fallback for unsupported warm-state shapes. The
   generated rows remain `unknown`, but at 1 s both hard rows now reach actual
   UF refinement (**2** UF rounds, **1** candidate, **282** pair checks,
   **6** equal-argument pairs, **5** violations, **6** learned UF lemmas)
   instead of spending the whole short budget in the first arithmetic solve. At
   10 s the first hard row keeps **6** UF rounds, **5** candidates,
   **23** equal-argument pairs, and **23** learned UF lemmas; the final timeout
   is now inside the warm arithmetic state with **solve_calls=6**,
   **total_rounds=279**, **atoms=531**, **bound_lemmas=664**, and
   **blocking_lemmas=295**. Next practical lever: CEGAR relevance/convergence
   after the fifth candidate, via model-guided UF-pair scheduling or the real
   combined CDCL(T) interface-equality loop.
   **UF BATCHING POLICY GUARDRAIL RETAINED (2026-06-26):**
   a narrower violated-pair-only refinement policy was measured and rejected
   before commit: both generated QF_UFLIA 1 s rows regressed to **0** UF
   candidates and timed out in the first arithmetic solve after **42**
   support-conflict rounds. The retained all-equal-argument batching restores
   the warm-skeleton baseline (**1** candidate / **6** UF lemmas at 1 s,
   **5** candidates / **23** UF lemmas at 10 s). A focused regression test now
   pins the policy that once a candidate exposes any violated congruence pair,
   every currently equal-argument pair in that candidate is batched, including
   pairs whose result values already agree.
   **IMPLICATION FLATTENING REJECTED (2026-06-26):**
   flattening arithmetic-guarded UF implications such as
   `((a <= b) ∧ (b <= a)) => result_eq` into flat disjunctions was measured and
   rejected. Although logically equivalent and smaller in auxiliary Boolean
   variables, it changed SAT search shape enough that both generated QF_UFLIA
   1 s rows lost the first UF candidate (**0** candidates, **0** UF lemmas).
   The code now documents why the implication shape is intentionally preserved;
   the retained baseline stays **1** candidate / **6** UF lemmas at 1 s.
   **INTEGER-BOUND THEORY TAUTOLOGY FOLD LANDED (2026-06-26):**
   the LIA abstractor now folds simple integer-bound contradictions and
   tautologies before allocating Boolean atom props, e.g.
   `x >= 8 ∧ x <= 6` → `false` and
   `not (x >= 8) ∨ not (x <= 6)` → `true`. This reuses the same simple Int
   order-bound interpretation as the certified bound mutex/implication lemmas
   and does not flatten UF implication guards. The generated QF_UFLIA rows
   remain `unknown`, but the 1 s frontier is preserved and the 10 s first row
   now reaches **24** learned UF lemmas before timing out in the warm arithmetic
   state.
   **ARITHMETIC CORE-SOURCE DIAGNOSTICS LANDED (2026-06-26):**
   lazy arithmetic DPLL budget `unknown`s now report dynamic core-source counts
   (`bound`, `diff`, `lp`, `minimized`, `large`) alongside core lengths. On the
   generated QF_UFLIA 10 s hard row the late warm arithmetic timeout is dominated
   by LP-relaxation cores (**core_src_lp=276**) with no deletion-minimized or
   large-cutoff cores. The next lever is therefore LP-core relevance/shrinking
   or preventing the SAT skeleton from feeding so many LP-core-producing
   branches, not core minimization.
   **BOUNDED LP-CORE SHRINKING LANDED (2026-06-26):**
   small LP-relaxation Farkas supports are now deletion-minimized, capped at
   **24** atoms, by re-running the same LP infeasibility checker used for the
   final core self-check. Larger supports keep the cheap Farkas-support path.
   This preserves the short-budget QF_UFLIA frontier (**2** UF rounds, **1**
   candidate, **6** learned UF lemmas at 1 s) and slightly reduces the 10 s hard
   row's warm arithmetic pressure: **total_rounds 305 -> 290**,
   **blocking_lemmas 319 -> 303**, **core_src_lp 276 -> 260**, and
   **core_len_avg 7.3 -> 6.9**. The row still returns `unknown`; next practical
   lever is reducing LP-core-producing SAT branches or moving to a stronger
   combined UF/LIA interface loop.
   **ONLINE UFLIA BOOLEAN BOUNDARY DIAGNOSTIC LANDED (2026-06-26):**
   `uflia_online_probe` now runs the online EUF+LIA route directly on one
   SMT-LIB file, and the online Boolean layer now distinguishes actual QF_UFLIA
   theory atoms from Boolean equality/structure, handles n-ary `and`/`or`,
   encodes Boolean equality as IFF, and reports the first unsupported skeleton
   detail. On both generated QF_UFLIA overbound rows, the direct online probe
   now gets past the prior atom-cap/opaque-decline layer and identifies the next
   blocker precisely: `non-Boolean term with sort Int`, i.e. arithmetic order
   atoms containing UF applications/opaque integer terms. This is not row
   closure; production lazy UFLIA remains neutral and still times out after the
   same useful UF frontier. The next combined-theory slice is online LIA support
   for opaque integer UF apps, or continued reduction of LP-core-producing lazy
   branches.
   **BOUNDED OPAQUE-APP ONLINE UFLIA ORDER SUPPORT LANDED (2026-06-26):**
   the online UFLIA route now admits Int order atoms whose linear terms contain
   Int-sorted UF applications by treating those applications as opaque integer
   LIA variables. This is an UNSAT/conflict/propagation hook only: satisfiable
   opaque abstractions still lack model lifting and therefore replay as
   `Unknown`, while pure equality-only Int UF rows still stay on the EUF path
   and can return replay-checked `Sat`. Direct hard-row probes moved from the
   previous `non-Boolean term with sort Int` boundary to a deliberate guard:
   both generated overbound rows now decline quickly with
   `too many theory atoms for opaque-app online UFLIA: 485 > 128`. That guard is
   load-bearing; before it, the hard direct probe ran for more than **90 s**
   despite a 1 s timeout because opaque-app combined-state/theory assertion is
   not deadline-aware. The production lazy route is preserved but not improved:
   the 1 s frontier remains **2** UF rounds, **1** candidate, **282** pair
   checks, **6** equal-argument pairs, **5** violations, and **6** learned UF
   lemmas. Next practical work is deadline-aware opaque-app online assertion
   plus model lifting, or reducing LP-core-producing lazy branches.
   **DEADLINE-AWARE OPAQUE-APP ONLINE THEORY CHECKS LANDED (2026-06-26):**
   the online `LiaTheory` now carries the Boolean-layer deadline into
   feasibility checks, deletion-minimized core checks, model reconstruction, and
   propagation probes, including the opaque Int-UF application abstraction used
   by UFLIA. `CombinedIncrementalLia` and the enumerative fallback
   `CombinedTheoryLia` pass that deadline into their nested LIA state, and an
   elapsed deadline degrades theory checks to inconclusive `Unknown` rather than
   producing conflicts or propagations. This is a resource-control prerequisite,
   not a solve-rate win: a zero-timeout Boolean opaque-app UFLIA regression now
   returns `Timeout` before theory work, but the generated overbound rows still
   decline at the deliberate **128** opaque-app atom guard
   (`485 > 128`), and the production lazy 1 s frontier remains **2** UF rounds,
   **1** candidate, and **6** learned UF lemmas. Next practical work is using
   this deadline-safe substrate to relax/partition the guard or reducing
   LP-core-producing lazy branches.
   **OPAQUE-APP ONLINE GUARD PARTITIONED BY OPAQUE ATOMS (2026-06-26):**
   the online UFLIA opaque guard now counts actual opaque Int-UF order atoms
   instead of treating total theory-atom count as the expensive proxy. Large
   Boolean skeletons with a small opaque subset are admitted to the
   deadline-aware path; a regression covers **>128** total atoms with only one
   opaque order atom. The generated overbound rows remain guarded, now with a
   precise count: **485** total theory atoms, **334** opaque-app order atoms,
   declining as `opaque_app_order_atoms=334 > 128, total=485`. A broad cap-raise
   experiment to **512** was rejected before commit because both 1 s direct
   probes were still running after **30 s**. Next practical work is
   construction-deadline checks or partitioned opaque-heavy admission, plus
   opaque-app model lifting.
   **SHARED CDCL(T) PROPAGATION DEADLINE CHECKS LANDED (2026-06-26):**
   the generic online `Dpll<T: TheorySolver>` now checks deadlines inside
   Boolean unit propagation and theory propagation, not only between outer
   search iterations. This closes one timeout hole shared by LIA/UFLIA/UFLRA and
   is pinned by a direct unit test. It does **not** yet make opaque-heavy
   generated UFLIA safe to admit wholesale: with the opaque cap temporarily
   raised to **512**, the first 1 s direct probe still ran past **30 s**, so the
   remaining overrun sits in construction, encoding, or theory-propagation
   generation before these inner DPLL checks regain control. The committed guard
   remains **128** opaque-app order atoms.
   **OPAQUE-APP ONLINE CONSTRUCTION/FALLBACK GUARD LANDED (2026-06-26):**
   large combined opaque-app UFLIA layouts now defer LIA feasibility to the
   theory-propagation boundary instead of re-solving on every asserted literal;
   the Boolean UFLIA construction path checks the caller deadline while
   collecting atoms, building the combined state, encoding the Boolean skeleton,
   and adding interface clauses; and opaque-app layouts that cannot build the
   incremental combined state decline instead of restarting through the older
   enumerative fallback. Re-running the broad cap experiment with the opaque cap
   temporarily raised to **512** now makes both generated direct probes decline
   in about **4 ms** with `opaque-app online UFLIA incremental combined state
   could not be built safely` instead of running past **30 s**. This fixes the
   unsafe admission/fallback path, not the solve-rate gap: the committed guard
   remains **128**, and the next solve work is partitioned opaque-heavy
   admission that preserves incremental-build safety, opaque-app model lifting,
   or lazy UF/LIA relevance that reduces LP-core-producing branches.
   **AFFINE FIXED-ARGUMENT UF PRESEED LANDED (2026-06-26):**
   lazy UF functional-consistency preseed now closes a narrow soundness-preserving
   relevance gap: top-level affine integer equalities and paired non-strict
   bounds can derive fixed symbol values for cheap congruence lemmas, not only
   direct singleton bounds. The extractor is checked and conservative (linear
   integer syntax only, multiplication by constants only, one unassigned symbol
   per equality, no one-sided-bound inference). Focused tests pin both the
   positive paired-affine case and the one-sided decline case. The generated
   overbound row is measured neutral, which is useful information: its relevant
   UF arguments still depend on Boolean/model choices such as `fmt1` and
   `arg1`, so `preseeded_lemmas` remains **0** at 1 s and 10 s. The practical
   next lever remains lazy UF/LIA relevance after candidate models, LP-core
   branch pressure, or a stronger combined interface-equality loop.
   **STAGED AFFINE ARITHMETIC CORE EXTRACTION LANDED (2026-06-26):**
   the warm lazy arithmetic loop now has a checked affine integer parser and a
   dynamic two-literal conflict extractor for algebraically equal but
   syntactically different linear expressions, such as `x - y` vs
   `x + (-1 * y)`. The extractor handles constants, symbols, `+`, `-`, unary
   negation, and multiplication by constants with checked overflow, and every
   learned core still goes through the existing arithmetic-lemma self-check. To
   avoid flooding the first pure arithmetic solve, affine cores are enabled only
   after the warm skeleton has been strengthened by UF lemmas and are capped at
   **1** affine core per theory conflict; the existing simple-bound batch cap
   remains **32**. Telemetry now reports `core_src_affine`.

   This is not a generated-row closure, but it is a measured LP-pressure
   reduction without losing the useful UF frontier. On
   `cli__regress2__uflia-error0.smt2`, the 1 s run still reaches **2** UF
   rounds, **1** candidate, **282** pair checks, and **6** learned UF lemmas. At
   10 s the row remains `unknown` but preserves **6** UF rounds, **5**
   candidates, and **24** learned UF lemmas while the final warm arithmetic
   timeout reports **core_src_affine=49** and **core_src_lp=207** (down from the
   prior low-260s LP-core samples), with **total_rounds=286** and
   **blocking_lemmas=300**. Next practical work is still UF/LIA convergence:
   relevance after several candidates, model-guided UF-pair scheduling, or the
   stronger online interface-equality loop.
   **POST-CANDIDATE UF SIBLING SCHEDULING LANDED (2026-06-26):**
   lazy function-consistency CEGAR now records `sibling_lemmas` and, after a
   real violated candidate pair, schedules at most **one** additional valid
   Ackermann lemma between the same unary-Int dynamic application and a sibling
   constant application in that function group. This is deliberately
   post-candidate, not another preseed: the rejected broad preseed hurt the first
   arithmetic solve, while this only fires after the row has already identified
   a relevant violated UF application. Wider caps were measured and rejected:
   cap **16** dropped the 10 s hard row to **3** UF rounds / **2** candidates,
   cap **4** to **4** rounds / **3** candidates, and cap **2** to **5** rounds /
   **4** candidates. The committed cap **1** preserves the frontier.

   On `cli__regress2__uflia-error0.smt2`, the 1 s run remains `unknown` but
   preserves **2** UF rounds, **1** candidate, **282** pair checks, **5**
   violations, **first_candidate_ms=1040**, **sibling_lemmas=1**, and
   **lemmas_added=7**. At 10 s the row remains `unknown` but preserves **6** UF
   rounds and **5** candidates, with candidates spanning
   **first_candidate_ms=1025** to **last_candidate_ms=8324**; it reports
   **sibling_lemmas=5**, **lemmas_added=27**, **total_rounds=285**,
   **blocking_lemmas=300**, **core_src_affine=45**, and **core_src_lp=209**.
   The remaining blocker is still convergence/search after several UF
   candidates, not missing bulk Ackermann constraints.
   **QF_UFLIA CEGAR TUNING REJECTIONS RECORDED (2026-06-26):**
   three narrow follow-up knobs were measured and deliberately not committed.
   Reordering the cap-1 post-candidate sibling lemma to prefer the nearest
   constant to the just-violated constant regressed the 10 s hard row to
   **5** UF rounds / **4** candidates, so the discovery-order cap-1 policy stays.
   Raising the staged affine-core batch cap from **1** to **2** preserved
   **6** rounds / **5** candidates, but increased blocker pressure
   (**blocking_lemmas=323**, **core_src_lp=221**) without closing the row, so
   the cap stays **1**. Raising the simple-bound dynamic batch cap from **32**
   to **64** was neutral/slightly worse (**blocking_lemmas=301**,
   **core_src_lp=210**) and is likewise rejected. The next useful lever is not
   these batch caps or sibling ordering; it is either a different CEGAR
   relevance signal, true combined UF/LIA interface propagation, or reducing the
   500-ish-atom arithmetic Boolean skeleton before the warm loop starts.
   **QF_ALIA/AUFLIA ARRAY ROW REFRESH LANDED (2026-06-26):**
   cvc5 `:arrays-exp` `eqrange` now lowers to finite pointwise equality on
   constant Int ranges, and constant-index self-store array equalities
   (`a = store(...store(a,k,v)...)`) lower to point constraints. The scalar array
   abstraction also treats preprocessing replay failure as an optimization miss
   and falls back to the raw scalar backend before the existing array
   projection/replay gate. The refreshed rows are **QF_ALIA 4/6 decided** and
   **QF_AUFLIA 5/7 decided**, both with **unsupported=0** and **DISAGREE=0**.
   Remaining blockers: QF_ALIA `ios_np_sf`/`constarr3` lazy-extensionality replay
   incompletes, and QF_AUFLIA `bug330`/`bug337` scalar-search timeouts.
   **QF_ALIA CONST-ARRAY STORE-CHAIN REFUTER LANDED (2026-06-26):**
   finite write chains over different constant-array defaults on the infinite
   `Int` index sort now produce a small rechecked unsat certificate. This closes
   the cvc5 `constarr3` row and refreshes QF_ALIA to **5/6 decided (83.3%)**,
   **unknown=1**, **unsupported=0**, **DISAGREE=0**, with PAR-2 mean **3.333 s**.
   The remaining QF_ALIA blocker at that point was `ios_np_sf`, a
   store-chain/readback contradiction needing arithmetic-backed index
   disequality reasoning.
   **QF_ALIA STORE-CHAIN READBACK REFUTER LANDED (2026-06-26):**
   finite store-chain equality over a shared `(Array Int Int)` base now has a
   rechecked readback certificate: unit-affine Int aliases prove a visible write
   index is distinct from every opposite-chain write index, so equality forces
   the opposite side to read the shared base array at that index. An asserted
   disequality against that base read is impossible. This closes cvc5
   `ios_np_sf` and refreshes QF_ALIA to **6/6 decided (100.0%)**,
   **unknown=0**, **unsupported=0**, **oracle-compared=5/6**, **DISAGREE=0**,
   with PAR-2 mean **0.000 s**. The nearby Int-array solve frontier is now
   QF_AUFLIA `bug330`/`bug337` scalar-search depth and QF_AX breadth.
   **QF_ALIA EXACT DOMINANCE AUDIT INGESTED (2026-06-26):**
   QF_ALIA's cvc5 clean slice now has a committed complete dominance audit. The
   two QF_ALIA-specific unsats above are exported as checked
   `const-array-default-mismatch-unsat` and `store-chain-readback-unsat`
   evidence, reconstruct through `ConstArrayDefaultMismatch` and
   `StoreChainReadback`, and real Lean accepts both generated modules with no
   `sorryAx`. The row is **6/6 dominant (100.0%)**, **Lean unsat 5/5
   (100.0%)**, with **mismatches=0**, **audit_errors=0**, and **timeouts=0**.
   The first audit queue is now clear; QF_ALIA's next work is broader
   Int-array generalization, not deciding or certifying this slice.
   **QF_AX CROSS-STORE ARRAY REFUTER LANDED (2026-06-26):**
   same-index reciprocal stores over declared index/element sorts now refute
   direct array disequalities before any finite-domain BV lowering. The structural
   rule derives `A = B` from
   `store(A,i,select(B,i)) = store(B,i,select(A,i))`, iterates that derivation
   through the two-step `arrays4` shape, and deliberately does not match the SAT
   `arrays3` mixed-index shape. Refreshing the current QF_AX cvc5 clean baseline
   records **5/8 decided (62.5%)**, **unknown=1**, **unsupported=2**,
   **oracle-compared=5/8**, **DISAGREE=0**, and PAR-2 mean **10.000 s**.
   **QF_AX EXACT DOMINANCE AUDIT INGESTED (2026-06-26):**
   the decided QF_AX cvc5 clean slice now has a committed complete dominance
   audit. The `arr1` false-implication read-congruence row certifies as
   `array-axiom-unsat`, and the new declared-sort reciprocal-store rows certify
   as checked `cross-store-array-disequality-unsat` evidence reconstructing
   through `CrossStoreArrayDisequality`. Real Lean accepts the generated modules
   with no `sorryAx`. The audited decided slice is **5/5 dominant (100.0%)**,
   **Lean unsat 4/4 (100.0%)**, with **mismatches=0**, **audit_errors=0**, and
   **timeouts=0**. At that point the remaining QF_AX blockers were decide-side:
   declared-sort SAT model construction for `arrays2`/`arrays3` and the
   Bool-array unsat row.
   **QF_AX BOOL-ARRAY READ-COLLAPSE LANDED (2026-06-26):**
   Bool-index arrays now have a checked read-collapse refuter: if
   `select a false = select a true`, an asserted disequality between any two
   reads from `a` is impossible. The route exports
   `bool-array-read-collapse-unsat` evidence and reconstructs through
   `BoolArrayReadCollapse`. Refreshing the cvc5 QF_AX row now records
   **6/8 decided (75.0%)**, **unknown=0**, **unsupported=2**,
   **oracle-compared=6/8**, **DISAGREE=0**, and PAR-2 mean **6.667 s**. The
   exact audit is **6/6 dominant (100.0%)**, **Lean unsat 5/5 (100.0%)**, with
   **mismatches=0**, **audit_errors=0**, and **timeouts=0**. Remaining QF_AX
   blockers are the SAT `arrays2`/`arrays3` rows, which need replay-checked
   declared-sort model construction.
   **QF_AX DECLARED-SORT SAT MODELS LANDED (2026-06-26):**
   pure declared-sort arrays now route through the lazy ROW/extensionality loop
   with a replaying EUF e-graph scalar backend. Generic array model projection
   closes the remaining SAT `arrays2`/`arrays3` rows, and true array-equality
   refinement now checks compatible materialized indices plus finite store
   indices so store-equality witnesses interact with disequality skolems. The
   refreshed QF_AX row is **8/8 decided (100.0%)**, **unknown=0**,
   **unsupported=0**, **oracle-compared=8/8**, **DISAGREE=0**, PAR-2 mean
   **0.004 s**. The exact audit is **8/8 dominant (100.0%)**, **Lean unsat
   5/5 (100.0%)**, with **mismatches=0**, **audit_errors=0**, and
   **timeouts=0**. QF_AX is closed for this small cvc5 slice; next array work is
   AUFLIA scalar-search depth and broader neutral QF_AX/non-BV-array corpora.
   **AUFLIA `bug337` DIRECT PBLS-ARRAY PROBE REJECTED (2026-06-26):**
   a replay-gated experiment admitted `(Array Int Int)` variables into PBLS,
   defaulted arrays, added direct `select(a,i)=v` store repairs, and tried a 5 s
   pure Int-array local-search probe before the array route. It flattened
   `bug337` to 237 conjuncts but still timed out (`Unknown`, 1791 flips in 5 s).
   A temporary 5 s scalar-abstraction local-search budget also failed, merely
   moving the route to a lazy-extensionality deadline after roughly 15.6 s. No
   solver change was retained. The next useful AUFLIA move is a replay-gated
   branch-schedule/model constructor for the queue-lock transition shape, SAT
   relevance in the large scalar skeleton, or finite UF-table/model search for
   `bug330` — not a generic direct PBLS-array hook.
   **AUDIT HARNESS LANDED (2026-06-25):**
   `cargo run --release -p axeyum-bench --example audit_dominance -- <baseline.json>
   [timeout_ms] [limit] [out.json]` now re-runs baseline-decided instances
   through `produce_evidence`, re-checks the evidence, attempts
   `prove_unsat_to_lean_module` for `unsat`, and records `lean_fragment`,
   `lean_checked`, `trust_holes`, and `dominant_candidate` per instance. Smoke
   audits exposed both a positive `QfUfBv` Lean-certified unsat and real gaps
   where baseline-decided instances still lack transferable evidence.
   **FIRST EXACT AUDIT INGESTED (2026-06-25):**
   [`bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json`](bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json)
   is now committed into the generator path: QF_UFBV/cvc5 has exact audited
   `dominant%(D) = 100% (4/4)`, Lean-checked unsat coverage `100% (2/2)`, and
   no audit errors.
   **FINITE-DOMAIN QF_UFBV REFUTER + LEAN ROUTE LANDED (2026-06-25):**
   the former `bug593` evidence-route error is now a certified
   `finite-domain-pigeonhole-unsat` result: three pairwise-distinct `f(g ·)`
   values cannot fit through `f : BV1 -> A`. The one-bit-domain Lean
   reconstruction now proves this certificate by `Bool.rec` over the three
   arguments and `Eq.refl` at the repeated value, so `bug593` is
   `lean_fragment = FiniteDomainPigeonhole` with no trust holes. Next
   measurement step: commit more complete `bench-results/dominance/*.json`
   artifacts for the remaining `audit now` rows.
   **SECOND EXACT AUDIT INGESTED + DECLARED-SORT QF_UFBV SAT FIX LANDED
   (2026-06-25):**
   [`bench-results/dominance/qf-ufbv-bitwuzla-regress-clean-dominance-audit.json`](bench-results/dominance/qf-ufbv-bitwuzla-regress-clean-dominance-audit.json)
   is now complete and ingested. The prior `declsort1` solver error is fixed by a
   replay-gated lazy-Ackermann route for mixed declared-sort QF_UFBV SAT models:
   unconstrained carrier symbols get deterministic distinct tokens, so the lazy
   UF loop does not add false congruence lemmas over arbitrary defaults before
   raw BV fallback. That audit then exposed a proof-side gap in
   `solver__fun__fun1.smt2`: a decided Boolean-UF `unsat` that needed a direct
   Lean/evidence route rather than the trusted reduction fallback. The generator
   now reports missing Lean unsat coverage and trust holes in exact audit rows,
   not just runtime audit errors.
   **BOOLEAN-UF QF_UFBV EXACT ROW CLOSED (2026-06-25):**
   `solver__fun__fun1.smt2` now uses a checked `bool-uf-exhaustive-unsat`
   certificate: the checker enumerates the two Boolean symbols and four unary
   Boolean function interpretations, accepting only when every case falsifies an
   original assertion. The matching `ProofFragment::BoolUfExhaustive` Lean route
   re-runs that checker before rendering a certificate-wrapper module. The exact
   QF_UFBV/bitwuzla audit is now **100% (2/2)** dominant with Lean unsat
   **100% (1/1)**, zero mismatches, zero audit errors, zero timeouts, and no
   trust holes.
   **QUANTIFIED BV CVC5 EXACT ROW CLOSED (2026-06-25):**
   the cvc5 quantified-BV audit now has a checked `bv-forall-nonconstant-unsat`
   route for universal inversion rows such as `forall x. bvadd x a = b`,
   `bvashr`, `concat`, and guarded `bvudiv` variants. The certificate re-scans
   the original IR and verifies the concrete witness schema before Lean
   reconstruction renders a checked wrapper. Together with finite-domain enum
   rows, the exact BV/cvc5 quantified audit is now **100% (37/37)** dominant
   with Lean unsat **100% (8/8)**, zero mismatches, zero audit errors, and zero
   timeouts.
   **QF_UFFF EXACT ROW CLOSED (2026-06-25):**
   the cvc5 QF_UFFF finite-field+UF row now has a checked `bv-uf-local-unsat`
   route. The checker derives local equality facts by exhaustive evaluation over
   only the two small BV symbols involved in each pure-BV field constraint, then
   closes the UF contradiction by congruence or a final tiny pure-BV conflict
   after congruence. Lean reconstruction reruns that checker before rendering
   the certificate-wrapper module. The exact QF_UFFF/cvc5 audit is now **100%
   (8/8)** dominant with Lean unsat **100% (6/6)**, zero mismatches, zero audit
   errors, and zero timeouts.
   **QF_FF EXACT ROW CLOSED (2026-06-25):**
   the cvc5 QF_FF finite-field row now combines two checked Lean/evidence routes:
   ground rows inside the raw 20-bit symbol budget reconstruct through
   `term-level-unsat` / `ProofFragment::TermLevelEnum`, while the wider algebraic
   identity and parity rows use a checked `bv-defined-enum-unsat` route. The
   latter enumerates only independent Bool/BV symbols after re-deriving required
   top-level definitions such as `mac1 = k1 + d*m1` and finite-domain restrictions
   such as bitness guards, then replays the original assertions. The exact
   QF_FF/cvc5 audit is now **100% (24/24)** dominant with Lean unsat **100%
   (10/10)**, zero mismatches, zero audit errors, and zero timeouts.
   **QF_FP EXACT ROW CLOSED (2026-06-26):**
   the Bitwuzla QF_FP row now has a committed exact dominance audit. The checked
   `bv-defined-enum-unsat` route was widened from Bool/BV to finite scalar terms,
   using Axeyum's existing ADR-0026 Float-as-bit-pattern representation. This
   closes the `fp_inf` and `fp_zero` constant-chain rows (`a = b`, `a = +oo/+0`,
   `b = -oo/-0`) with one-case replay through the original assertions, and closes
   `fp_misc` by enumerating only independent assignments after cheap required
   single-symbol constraints such as `fp.isZero (fp.neg a)` shrink Float16 `a` to
   zero bit-patterns and `rm <= 4` shrinks the rounding-mode token. The route is
   guarded by a 20k case cap and a small-DAG restriction enumerator, so SAT rows
   such as `fp_regr3` fall through to model replay instead of spending time in
   pre-solve certification. The exact QF_FP audit is now **100% (16/16)**
   dominant with Lean unsat **100% (7/7)**, zero mismatches, zero audit errors,
   and zero timeouts.
   **QF_BVFP EXACT ROW CLOSED (2026-06-26):**
   the Bitwuzla QF_BVFP row now has a committed exact dominance audit. The two
   prior proof-production timeouts (`Float-no-simp3-main` and `fp_fromsbv`) now
   certify through the checked `bv-defined-enum-unsat` route. The checker collects
   required facts through nested negated implications, replays top-level
   definitions with selected-path `ite`/Boolean semantics so parser-created
   FP-conversion witnesses are ignored only when the chosen semantic path never
   reads them, and permits the no-definition FP-lowered `FpFromBits` slice to
   enumerate its tiny real domain (`x` and restricted `rm`) directly. The exact
   QF_BVFP audit is now **100% (7/7)** dominant with Lean unsat **100% (3/3)**,
   zero mismatches, zero audit errors, and zero timeouts.
   **QF_DT EXACT ROW CLOSED (2026-06-26):**
   the cvc5 QF_DT row is now a committed complete dominance audit. The datatype
   structural checker now flattens Boolean conjunctions, splits top-level
   disjunctions into independently checked branches, and records constructor
   exhaustiveness facts from negative testers plus nullary-constructor
   disequalities. This closes the prior `acyclicity-sr-ground096` unsupported
   row and the former bare `pf-v2l60078` evidence row through checked
   `datatype-structural-unsat` evidence and `ProofFragment::DatatypeStructural`
   Lean reconstruction. The exact QF_DT audit is now **100% (3/3)** dominant
   with Lean unsat **100% (3/3)**, zero mismatches, zero audit errors, and zero
   timeouts.
   **DOMINANCE AUDIT BATCH + PURE-REAL EVIDENCE FALLBACK LANDED (2026-06-25):**
   six more complete audit artifacts are now committed and ingested:
   BV/bitwuzla quantified **100% (4/4)**, QF_BV/bvred **100% (6/6)**,
   QF_LIA/cvc5 **100% (10/10)**, QF_LRA/cvc5 **100% (9/9)**, QF_UFLIA curated
   **50% (1/2)** after the checked integer route picked up `named-expr-use`,
   and QF_UFLIA bounded declared-sort regressions **80% (4/5)**.
   All exact audit rows have **DISAGREE = 0** and **audit_errors = 0**. The LRA
   row initially exposed a practical evidence gap: the pure-real certificate
   front door could decline a Boolean/ITE LRA SAT shape with an unsupported
   `"non-linear or non-real subterm"` message and stop before the general
   replayable evidence fallback. `produce_evidence` now falls through on
   unsupported pure-real certificate declines while preserving stronger
   LRA/SOS/NRA certificates when available.
   **QF_UFLIA EXACT ROWS CLOSED (2026-06-25):**
   the remaining `use-name-in-same-command` proof-step rows are now certified by
   `arith-dpll-unsat`: integer-valued UF applications are treated as opaque
   integer variables inside the lazy-SMT arithmetic checker, and satisfiable
   opaque abstractions decline so the UFLIA backend still owns SAT model lifting.
   The Lean classifier now routes mixed UF+arithmetic rows through
   `ProofFragment::ArithDpll` only after the certificate re-verifies. Exact
   QF_UFLIA curated named is now **100% (2/2)** dominant with Lean unsat
   **100% (2/2)**; the bounded uninterpreted-sort row is **100% (5/5)** dominant
   with Lean unsat **100% (1/1)**, zero mismatches, zero audit errors, and zero
   timeouts.
   **EXACT QF_BV BVRED ROW CLOSED (2026-06-25):**
   [`bench-results/dominance/qf-bv-curated-bvred-dominance-audit.json`](bench-results/dominance/qf-bv-curated-bvred-dominance-audit.json)
   is now exact at **100% (6/6)** dominant with Lean unsat **100% (2/2)**,
   zero mismatches, zero audit errors, and zero timeouts. The previous miss,
   `cvc5__redand-eliminate.smt2`, is still evidence-certified as
   `term-level-unsat` and now reconstructs through the checked structural Lean
   route (`lean_fragment = ArrayAxiom`) with no trust holes. A direct
   `ReflexiveDisequality` Lean fragment now also covers literal top-level
   `not (= t t)` assertions by applying the input assumption to `Eq.refl`.
   **QF_LRA TERM-IDENTITY ROW CLOSED (2026-06-25):**
   [`bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json`](bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json)
   moved to **78% (7/9)** dominant with Lean unsat **33% (1/3)** and evidence
   certified **9/9**. The former `ite_arith` miss is now
   `term-identity-unsat`: the checked certificate re-matches `not (= x (ite
   true x y))`, the Lean route reconstructs it as `ProofFragment::TermIdentity`,
   and the row has no trust holes.
   **QF_LRA DPLL ROW CLOSED (2026-06-25):**
   the two remaining exact QF_LRA misses, `arith__ite-lift` and `simple-lra`,
   are now Lean-reconstructed through `ProofFragment::LraDpll`. Reconstruction
   re-runs the self-checking lazy-SMT certificate before rendering the
   certificate-wrapper Lean module. The exact QF_LRA/cvc5 audit is now
   **100% (9/9)** dominant with Lean unsat **100% (3/3)**, zero mismatches, zero
   audit errors, and zero timeouts.
   **QF_LIA EXACT ROW CLOSED (2026-06-25):**
   the three remaining exact QF_LIA misses are now certified: `dump-unsat-core-full`
   and `named-expr-use` use `arith-dpll-unsat` evidence with
   `ProofFragment::ArithDpll`, while the large Boolean RF-11 ACI normalization
   stress row uses a cheap checked `bool-simplification-unsat` certificate and
   `ProofFragment::BoolSimplification`. The exact QF_LIA/cvc5 audit is now
   **100% (10/10)** dominant with Lean unsat **100% (4/4)**, zero mismatches,
   zero audit errors, and zero timeouts.
   **SYNTHETIC NIA/NRA EXACT AUDITS LANDED (2026-06-25):**
   the dominance audit harness now ingests graduated summary baselines by
   enumerating corpus files and using their `:status` annotations plus the
   committed aggregate `axeyum_decided` denominator. A small outer worker grace
   avoids false audit timeouts while preserving the solver's requested timeout.
   QF_NRA synthetic first landed exact at **80% (24/30)** dominant, Lean unsat
   **62% (10/16)** after certificate-gated SOS reconstruction; QF_NIA
   synthetic is exact at **50% (16/32)** dominant, Lean unsat **0% (0/16)**.
   Both had zero mismatches, audit errors, and timeouts. The remaining QF_NRA
   misses at that point were the higher-degree `bare-unsat` rows
   (`nra-neg-square-d02..d06` and `nra-sos-strict-unsat-d02`), not the already
   certified SOS rows.
   **QF_NIA EXACT ROW CLOSED (2026-06-25):**
   bounded nonlinear-integer UNSAT rows now carry
   `bounded-int-blast-unsat` evidence: the checker re-derives the finite integer
   box, verifies the exact covering width, regenerates the clamped DIMACS, and
   rechecks the DRAT refutation before Lean reconstruction can use
   `ProofFragment::BoundedIntBlast`. The bounded-box evaluator also runs before
   preprocessing, so the synthetic Pythagorean SAT rows return replayable models
   quickly instead of timing out in preprocessing/model reconstruction. Exact
   QF_NIA synthetic is now **100% (32/32)** dominant with Lean unsat
   **100% (16/16)**, zero mismatches, zero audit errors, and zero timeouts.
   **QF_NRA EXACT ROW CLOSED (2026-06-25):**
   the six remaining higher-degree synthetic NRA proof misses now use checked
   `nra-even-power-unsat` evidence. The matcher accepts only original assertions
   where a sum of syntactic even powers of real terms plus a nonnegative rational
   constant is asserted `< 0`; evidence checking re-scans the original query, and
   Lean reconstruction routes through `ProofFragment::NraEvenPower` only after
   that certificate rechecks. Exact QF_NRA synthetic is now **100% (30/30)**
   dominant with Lean unsat **100% (16/16)**, zero mismatches, zero audit errors,
   and zero timeouts.
   **FIRST DOMINANCE AUDIT QUEUE CLEARED (2026-06-25):**
   QF_ABV/cvc5+bitwuzla is now exact at **50% (84/169)** dominant, Lean unsat
   **0% (0/85)**, with **6 audit errors/timeouts**; QF_AUFBV/bitwuzla is exact
   at **49% (20/41)** dominant, Lean unsat **0% (0/20)**, with **5 audit
   errors/timeouts**. The queue of decide-strong rows with an existing Lean
   route is now empty: every such row has a committed per-instance audit
   artifact. One QF_ABV SAT audit error (`rw134`) was closed by completing the
   lazy-extensionality assignment after fresh read symbols are materialized.
   The remaining dominance blocker is no longer "run the audit"; it is the
   measured proof/evidence gap: ABV/AUFBV evidence timeouts, `array-elim` /
   `bit-blast` trust holes, and missing Lean reconstruction for their unsats.
   **EVIDENCE-PHASE DIAGNOSTIC LANDED (2026-06-25):**
   the audit harness now emits per-instance phase timings plus `timeout_phase`.
   Re-running the complete QF_ABV and QF_AUFBV artifacts preserved the same
   dominance counts but localized all **11** array timeout rows to
   `produce-evidence` (QF_ABV 6/6, QF_AUFBV 5/5). The next array-dominance
   timeout target is therefore evidence production itself — solver/refinement,
   proof construction, or reduction-evidence extraction — not evidence checking
   or Lean reconstruction runtime.
   **TIMED EVIDENCE EXPORT GUARD LANDED (2026-06-25):**
   the unified evidence front door now treats reduced-CNF DRAT export for
   BV-reducible theories as an optional offline certificate when a wall-clock
   evidence budget is active. Cheap/stronger cert routes still run first; if they
   decline, a timed `produce_evidence` returns the already-decided bare `unsat`
   instead of entering the expensive array/UF reduction-proof exporter. The old
   unbounded exporter remains available for unbudgeted/offline callers, and the
   new `diagnose_evidence` example isolates `solve`, ABV Alethe emitters, and the
   expensive exporter. Re-running exact audits preserved dominance counts while
   cutting ABV/AUFBV audit errors from **11 → 3**: QF_ABV had **2** remaining
   timeouts (`rw34`, `arraycond9`) and QF_AUFBV had **1** (`fifo32ia04k05`) at
   this intermediate point. The cleared timeout class was optional proof export;
   the next blocker was solver/search work inside `produce-evidence`.
   **ARRAY BUDGET PROPAGATION LANDED (2026-06-25):**
   the remaining ABV/AUFBV dominance-audit timeouts are now eliminated without
   changing dominance counts. Timed `check_auto` now carries a single wall budget
   through probe, preprocessing, reduced dispatch, combined eager reductions,
   scalar backend calls, projection, and replay; late SAT results downgrade to
   `unknown` under an explicit timeout. The older lazy select-congruence path now
   shares the configured deadline across rounds and skips evaluator work for
   syntactically-identical indices. Most importantly, pure ABV dispatch now
   propagates budget `unknown` from the lazy array path instead of treating it as
   `not-applicable` and entering the expensive qf-bv fallback. Re-running exact
   audits preserved **QF_ABV 84/169** and **QF_AUFBV 20/41** dominant coverage
   while reducing both rows to **audit_errors=0, timeouts=0**. Remaining array
   dominance work is now proof-side Lean coverage and true solve-speed/depth, not
   audit runtime plumbing.
   **DIRECT ARRAY-EXTENSIONALITY LEAN ROUTE LANDED (2026-06-25):**
   the first ABV/AUFBV proof-side movement is now measured. The `QfAbv` Lean
   dispatcher tries the direct zero-trust ABV Alethe certificate before the
   elimination certificate; when that proof is pure congruence
   (`a=b ∧ select(a,i)≠select(b,i)`), it reconstructs through the existing EUF
   Lean path. The EUF reconstructor now discharges reflexive congruence side
   hypotheses such as `(= i i)` with `Eq.refl`, which was the missing Lean step
   for the audited direct array-extensionality rows. Re-running exact dominance
   audits moved **QF_ABV 84/169 → 85/169** dominant with Lean unsat **1/83**, and
   **QF_AUFBV 20/41 → 24/41** dominant with Lean unsat **4/20**, still with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining array proof work is the
   larger bare-unsat population: classify ROW/select-congruence/array-elim versus
   bit-blast-heavy shapes and add the next Lean-reconstructable certificate slice.
   **FINITE-ARRAY EXTENSIONALITY CERTIFICATE LANDED (2026-06-25):**
   the next AUFBV proof-side slice is now measured. Added a checked
   `UnsatFiniteArrayExtensionality` evidence variant and a matching
   `FiniteArrayExtensionality` Lean fragment for small BV-index arrays whose reads
   are explicitly equal at every concrete index while the arrays are asserted
   disequal. The exact AUFBV audit moved **24/41 → 28/41** dominant and **Lean
   unsat 4/20 → 8/20**, with **mismatches=0, audit_errors=0, timeouts=0**. This
   closes the non-`uf` `smtextarrayaxiom{1..4}.smt2` rows. Next practical array
   proof work: McCarthy/read-over-write-distinct and conditional select/store
   certificates, then the bit-blast-heavy array-elim population.
   **SMALL ARRAY-AXIOM CERTIFICATE LANDED (2026-06-25):**
   three more AUFBV proof-side rows are now measured. Added a checked
   `UnsatArrayAxiom` evidence variant plus `ArrayAxiom` Lean fragment for direct
   negations of McCarthy read-over-write, select-over-array-`ite`, and
   store-over-`ite` under select. The exact AUFBV audit moved **28/41 → 31/41**
   dominant and **Lean unsat 8/20 → 11/20**, with **mismatches=0,
   audit_errors=0, timeouts=0**. This closes `smtaxiommccarthy.smt2`,
   `smtarraycond1.smt2`, and `smtarraycond3.smt2`. Remaining AUFBV proof-side
   rows are now larger program-array/bit-vector rewrite shapes plus `rw213`; the
   next useful step is classify those ten by whether a BV/ite simplification cert
   can move them before investing in broader array-elim proof reconstruction.
   **BV-ABSTRACTION ARRAY CERTIFICATE LANDED (2026-06-25):**
   one more AUFBV proof-side row is now measured. Added a checked
   `UnsatBvAbstraction` evidence variant plus `BvAbstraction` Lean fragment for
   small array queries whose scalar BV abstraction is already certified-unsat
   after replacing array-dependent reads/equalities by fresh unconstrained
   Bool/BV symbols. This closes `rewrite__array__rw213.smt2`: the two array
   reads are irrelevant to the contradiction once abstracted. The exact AUFBV
   audit moved **31/41 → 32/41** dominant and **Lean unsat 11/20 → 12/20**,
   with **mismatches=0, audit_errors=0, timeouts=0**. Remaining AUFBV
   proof-side rows are the eight larger program-array cases:
   `binarysearch32s016`, `bubsort002un`, `dubreva002ue`, `fifo32bc04k05`,
   `memcpy02`, `selsort002un`, `swapmem002ue`, and `wchains002ue`; the next
   useful step is structural array-program certificates, not another shallow
   BV-only simplifier.
   **ALIGNED WRITE-CHAIN CERTIFICATE LANDED (2026-06-25):**
   one more structural AUFBV program-array row is now measured. Added a checked
   `UnsatAlignedWriteChainCommutation` evidence variant plus
   `AlignedWriteChainCommutation` Lean fragment for generated byte-store chains
   that write two 4-byte aligned words in opposite orders under low-address
   zero guards. The ranges are either disjoint or identical with identical byte
   values, so the store orders commute. This closes `wchains002ue.smt2`. The
   exact AUFBV audit moved **32/41 → 33/41** dominant and **Lean unsat
   12/20 → 13/20**, with **mismatches=0, audit_errors=0, timeouts=0**.
   Remaining AUFBV proof-side rows are now the seven larger program-array cases:
   `binarysearch32s016`, `bubsort002un`, `dubreva002ue`, `fifo32bc04k05`,
   `memcpy02`, `selsort002un`, and `swapmem002ue`.
   **TWO-BYTE MEMCPY CERTIFICATE LANDED (2026-06-25):**
   one more symbolic-memory AUFBV program row is now measured. Added a checked
   `UnsatTwoByteMemcpy` evidence variant plus `TwoByteMemcpy` Lean fragment for
   length-2 memory-copy obligations guarded by no-wrap/no-overlap facts and
   `j < 2`. The checker confirms the two destination stores copy the matching
   source bytes, so the asserted destination/source disequality is impossible.
   This closes `memcpy02.smt2`. The exact AUFBV audit moved **33/41 → 34/41**
   dominant and **Lean unsat 13/20 → 14/20**, with **mismatches=0,
   audit_errors=0, timeouts=0**. Remaining AUFBV proof-side rows are now the six
   larger program-array cases: `binarysearch32s016`, `bubsort002un`,
   `dubreva002ue`, `fifo32bc04k05`, `selsort002un`, and `swapmem002ue`.
   **TWO-ELEMENT BUBBLE-SORT CERTIFICATE LANDED (2026-06-25):**
   one more small program-array permutation row is now measured. Added a checked
   `UnsatTwoElementBubbleSort` evidence variant plus `TwoElementBubbleSort`
   Lean fragment for length-2 bubble-sort obligations. The checker confirms the
   output cells are the conditional swap/min-max of the two original cells, the
   arbitrary read index is guarded into `[start,start+2)`, and the assertion
   demands that read differ from both sorted cells while also asserting the
   sortedness bit. This closes `bubsort002un.smt2`. The exact AUFBV audit moved
   **34/41 → 35/41** dominant and **Lean unsat 14/20 → 15/20**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining AUFBV proof-side rows
   are now five cases: `binarysearch32s016`, `dubreva002ue`, `fifo32bc04k05`,
   `selsort002un`, and `swapmem002ue`.
   **TWO-ELEMENT SELECTION-SORT CERTIFICATE LANDED (2026-06-25):**
   the selection-sort sibling row is now measured as well. Extended
   `array_sort2` with a checked `UnsatTwoElementSelectionSort` evidence variant
   plus `TwoElementSelectionSort` Lean fragment for the generated min-index
   `ite` and selected-minimum two-store update. This closes
   `selsort002un.smt2`. The exact AUFBV audit moved **35/41 → 36/41** dominant
   and **Lean unsat 15/20 → 16/20**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining AUFBV proof-side rows are now four cases:
   `binarysearch32s016`, `dubreva002ue`, `fifo32bc04k05`, and `swapmem002ue`.
   **TWO-CELL XOR-SWAP CERTIFICATE LANDED (2026-06-25):**
   another generated memory-permutation row is now measured. Added a checked
   `UnsatTwoCellXorSwap` evidence variant plus `TwoCellXorSwap` Lean fragment
   for two nested ordinary two-cell swaps compared with the corresponding
   generated three-assignment XOR swaps. This closes `dubreva002ue.smt2`. The
   exact AUFBV audit moved **36/41 → 37/41** dominant and **Lean unsat
   16/20 → 17/20**, with **mismatches=0, audit_errors=0, timeouts=0**.
   Remaining AUFBV frontier rows are now three bare-unsat proof gaps
   (`binarysearch32s016`, `fifo32bc04k05`, `swapmem002ue`) plus the
   solve/search gap `fifo32ia04k05`.
   **TWO-BYTE XOR-SWAP ROUND-TRIP CERTIFICATE LANDED (2026-06-25):**
   the swapmem sibling row is now measured. Extended `array_xor_swap` with a
   checked `UnsatTwoByteXorSwapRoundtrip` evidence variant plus
   `TwoByteXorSwapRoundtrip` Lean fragment for two generated XOR swaps over a
   disjoint two-byte range followed by the same swaps again. The checker
   re-matches the exact four-swap dataflow and the two-byte no-overlap/no-wrap
   guard. This closes `swapmem002ue.smt2`. The exact AUFBV audit moved
   **37/41 → 38/41** dominant and **Lean unsat 17/20 → 18/20**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining AUFBV frontier rows
   are now two bare-unsat proof gaps (`binarysearch32s016`, `fifo32bc04k05`)
   plus the solve/search gap `fifo32ia04k05`.
   **BINARY-SEARCH16 CERTIFICATE LANDED (2026-06-25):**
   the generated binary-search row is now measured. Added a checked
   `UnsatBinarySearch16` evidence variant plus `BinarySearch16` Lean fragment
   for the crafted 16-element obligation: store `search_val` at an arbitrary
   BV4 index, assert the stored array is sorted at all adjacent concrete
   indices, and assert the generated five-probe binary search misses
   `search_val`. The checker re-matches the stored-array dataflow, the complete
   sortedness chain, the generated probe terms, and a finite equal-block check
   for the binary-search recurrence. This closes `binarysearch32s016.smt2`. The
   exact AUFBV audit moved **38/41 → 39/41** dominant and **Lean unsat
   18/20 → 19/20**, with **mismatches=0, audit_errors=0, timeouts=0**.
   Remaining AUFBV frontier rows are now the last bare-unsat proof gap
   `fifo32bc04k05` plus the solve/search gap `fifo32ia04k05`.
   **FIFO BC04 CERTIFICATE LANDED (2026-06-25):**
   the last exact AUFBV proof-side row is now measured. Added a checked
   `UnsatFifoBc04` evidence variant plus `FifoBc04` Lean fragment for the
   generated five-cycle FIFO equivalence benchmark. The checker re-generates
   the exact unrolled transition equality bits and final mismatch guard, and
   independently checks the finite FIFO equivalence theorem for the benchmark
   bound before accepting. This closes `fifo32bc04k05.smt2`. The exact AUFBV
   audit moved **39/41 → 40/41** dominant and **Lean unsat 19/20 → 20/20**,
   with **mismatches=0, audit_errors=0, timeouts=0**. The remaining exact
   AUFBV frontier is now the solve/search gap `fifo32ia04k05`.
   **FIFO IA04 SAT WITNESS LANDED (2026-06-25):**
   the remaining exact AUFBV solve/search row is now measured and closed. Added
   a replay-checked SAT witness for `fifo32ia04k05.smt2`: it simulates the exact
   five-cycle FIFO induction counterexample, assigns all declared scalar and
   16-cell array symbols, and returns the model only after the original assertion
   evaluates to `true`. `produce_evidence` therefore emits the ordinary certified
   `Sat(model)` evidence, with no new trusted proof kind. The exact AUFBV audit
   moved **40/41 → 41/41** dominant, Lean unsat remains **20/20**, and
   **mismatches=0, audit_errors=0, timeouts=0**. The next array-dominance work is
   no longer this bitwuzla AUFBV exact row; it is broader ABV Lean/evidence
   coverage and the cvc5 AUFBV/AUFLIA decide frontier.
   **ABV BTOR-STYLE ARRAY-AXIOM COVERAGE WIDENED (2026-06-25):**
   the broader ABV proof frontier moved next. The checked `ArrayAxiom` recognizer
   now decodes BTOR-style BV1 Boolean assertions (`#b1 = bit`) and only descends
   through asserted-true BV1 conjunctions; its read-over-write check also
   normalizes `select` through store chains when indices are syntactically equal
   or ground BV constants that are definitely distinct. This certifies ABV rows
   such as `write1` and `write13` as `array-axiom-unsat` and reconstructs them
   through the existing `ArrayAxiom` Lean fragment. Re-running the exact ABV
   audit moved **85/169 → 90/169** dominant and **Lean unsat 1/83 → 6/83**,
   with **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV work is the
   still-large BTOR bare-unsat population: guarded read-congruence, store
   shadowing/commutation, extensionality, and conditional-array patterns.
   **ABV READ-CONGRUENCE COVERAGE WIDENED (2026-06-25):**
   the same checked `ArrayAxiom` lane now builds a deliberately small equality
   closure from BTOR-style BV1 formulas and proves impossible read disequalities
   by congruence over arrays, indices, `select`, `bvnot`, `concat`, and
   idempotent `bvand`/`bvor`. This certifies representative `read*` and `ext*`
   rows such as `read1`, `read4`, and `read10` without adding a general BV
   solver inside the evidence checker. Re-running the exact ABV audit moved
   **90/169 → 112/169** dominant and **Lean unsat 6/83 → 28/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV proof work is now
   concentrated in store-shadowing, extensionality, and conditional-array rows.
   **ABV GUARDED WRITE-CASE COVERAGE WIDENED (2026-06-25):**
   the `ArrayAxiom` recognizer now normalizes read-over-write under branch-local
   equality and disequality guards, and accepts negated guarded case splits only
   when every violation branch is independently refuted. This closes the
   BTOR-style write rows `write2`, `write4`, `write7`, `write8`, `write9`, and
   `write10`, plus the related `verbose2` row. Re-running the exact ABV audit
   moved **112/169 → 119/169** dominant and **Lean unsat 28/83 → 35/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work is
   now mostly larger extensionality/store-shadowing rows, conditional-array rows,
   and the cvc5-specific BV/array proof gaps.
   **ABV NONZERO-OFFSET ROW COVERAGE WIDENED (2026-06-25):**
   the read-over-write normalizer now recognizes `i` and `i + c` as definitely
   distinct for BV indices when `c` is a nonzero constant modulo the index width,
   while preserving the `+0` SAT controls. This closes the four
   `rwpropindexplusconst{1..4}` rows through the existing `ReadOverWrite`
   certificate path. Re-running the exact ABV audit moved **119/169 → 123/169**
   dominant and **Lean unsat 35/83 → 39/83**, with **mismatches=0,
   audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work is now the larger
   extensionality/store-shadowing rows, conditional-array rows, residual write
   shapes, and cvc5-specific BV/array proof gaps.
   **ABV STORE-SHADOWING COVERAGE WIDENED (2026-06-25):**
   the same checked `ArrayAxiom` lane now normalizes store chains by removing
   earlier writes that are shadowed by later writes to the same syntactic index,
   preserving the base array and surviving write order. This closes the BTOR
   write rows `write22`, `write23`, and `write24` as `array-axiom-unsat` through
   the new `StoreShadowing` certificate path. Re-running the exact ABV audit
   moved **123/169 → 126/169** dominant and **Lean unsat 39/83 → 42/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work is
   larger extensionality/store-shadowing rows, conditional-array rows, residual
   write shapes (`write14`, `write16`, `write17`), and cvc5-specific BV/array
   proof gaps.
   **ABV CONDITIONAL-SELECT COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` read-congruence now tracks raw BV1 branch facts, matches
   `distinct`-encoded BV1 literals, simplifies array-valued `ite`s under those
   facts, and proves OR-of-conjunctions false when each branch locally refutes a
   guarded read disequality. This closes the BTOR rewrite rows `rw30`, `rw31`,
   `rw32`, and `rw33` through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **126/169 → 130/169** dominant and
   **Lean unsat 42/83 → 46/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining ABV bare-unsat work is now larger extensionality
   rows, conditional-array families, residual write shapes (`write16`,
   `write17`), and cvc5-specific BV/array proof gaps.
   **ABV CONTEXTUAL BV1-FALSE COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` now proves asserted-true BV1 terms false when contextual
   read-over-write normalization, ground-BV evaluation, and known array-valued
   `ite` branches reduce the bit to `#b0`. This closes `write14` and
   `arraycondconst` through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **130/169 → 132/169** dominant and
   **Lean unsat 46/83 → 48/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining ABV bare-unsat work is larger extensionality rows,
   conditional-array families, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV NESTED BV1 COMPLEMENT COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` contextual BV1 evaluation now flattens BV1 `bvand`/`bvor`
   chains enough to recognize complementary leaves. Thus `x ∧ ¬x` nested inside
   a BTOR/AIG-encoded condition proves that condition false, and `x ∨ ¬x` proves
   the dual true, before the existing array-valued `ite` and read-congruence
   checks run. This closes `arraycondconstaig` through the existing
   `ReadCongruence` certificate path. Re-running the exact ABV audit moved
   **132/169 → 133/169** dominant and **Lean unsat 48/83 → 49/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work
   is larger extensionality rows, conditional-array families, residual write
   shapes (`write16`, `write17`), and cvc5-specific BV/array proof gaps.
   **ABV FINITE-EXTENSIONALITY BIT COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` contextual term equivalence now recognizes the BTOR BV1
   encoding of finite array extensionality: a conjunction of read-equality bits
   over a complete small BV-index domain is equivalent to the array-equality
   bit. The checker accepts only complete covers: all concrete indices for small
   domains, or the two definitely-distinct indices of a BV1 domain. This closes
   `ext5` and `ext21` through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **133/169 → 135/169** dominant and
   **Lean unsat 49/83 → 51/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining ABV bare-unsat work is larger extensionality rows,
   conditional-array families, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV BV-NOT INJECTIVITY READ-CONGRUENCE COVERAGE WIDENED (2026-06-25):**
   the local `ArrayAxiom` equality closure now records the inverse fact for
   bit-vector complement literals: from `bvnot x = bvnot y` it records `x = y`
   (and analogously for disequality). This is enough to refute BTOR read
   congruence obligations whose index equality is hidden behind bitwise
   complement. This closes `read22` through the existing `ReadCongruence`
   certificate path. Re-running the exact ABV audit moved **135/169 → 136/169**
   dominant and **Lean unsat 51/83 → 52/83**, with **mismatches=0,
   audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work is larger
   extensionality rows, conditional-array families, residual write shapes
   (`write16`, `write17`), and cvc5-specific BV/array proof gaps.
   **ABV CONCAT-SUFFIX ROW COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` index reasoning now recognizes that two BV terms are definitely
   distinct when their known concrete low-bit suffixes disagree, even if their
   concat boundaries differ. This proves `(concat v0 #x00)` distinct from
   `(concat v1 #b1)` by the low bit, enabling read-over-write normalization.
   This closes `3vl1` through the existing `ReadOverWrite` certificate path.
   Re-running the exact ABV audit moved **136/169 → 137/169** dominant and
   **Lean unsat 52/83 → 53/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining ABV bare-unsat work is larger extensionality rows,
   conditional-array families, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV STORE SAME-CELL INJECTIVITY COVERAGE WIDENED (2026-06-25):**
   the `ArrayAxiom` read-congruence equality closure now records the injectivity
   fact for equal stores at the same base/index: from
   `store(a, i, v) = store(a, i, w)` it records `v = w`. This closes the BTOR
   `extarraywrite1` row through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **137/169 → 138/169** dominant and
   **Lean unsat 53/83 → 54/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. The refreshed artifact now has **50** `array-axiom-unsat`
   rows and **29** remaining `bare-unsat` rows. Remaining ABV bare-unsat work is
   larger extensionality rows, conditional-array families, residual write shapes
   (`write16`, `write17`), and cvc5-specific BV/array proof gaps.
   **ABV STORE SELF-UPDATE READ COVERAGE WIDENED (2026-06-25):**
   the same equality closure now records the read consequence of a self-update:
   from `a = store(a, i, v)` it records that `select(a, i)` is equal to `v`.
   This closes the BTOR `ext22` row through the existing `ReadCongruence`
   certificate path. Re-running the exact ABV audit moved **138/169 → 139/169**
   dominant and **Lean unsat 54/83 → 55/83**, with **mismatches=0,
   audit_errors=0, timeouts=0**. The refreshed artifact now has **51**
   `array-axiom-unsat` rows and **28** remaining `bare-unsat` rows. Remaining
   ABV bare-unsat work is larger extensionality rows, conditional-array
   families, residual write shapes (`write16`, `write17`), and cvc5-specific
   BV/array proof gaps.
   **ABV EQUAL STORE-CHAIN READBACK COVERAGE WIDENED (2026-06-25):**
   the `ArrayAxiom` read-congruence proof context now also handles Boolean
   top-level equality/disequality conjunctions, and it can use asserted equal
   array/store terms by reading both sides back at candidate store/select
   indices when direct ROW facts discharge the intervening writes. This closes
   the BTOR `ext27` and `ext28` rows through the existing `ReadCongruence`
   certificate path. Re-running the exact ABV audit moved **139/169 → 141/169**
   dominant and **Lean unsat 55/83 → 57/83**, with **mismatches=0,
   audit_errors=0, timeouts=0**. The refreshed artifact now has **53**
   `array-axiom-unsat` rows and **26** remaining `bare-unsat` rows. Remaining
   ABV bare-unsat work is conditional-array families, residual extensionality
   rows, residual write shapes (`write16`, `write17`), and cvc5-specific
   BV/array proof gaps.
   **ABV BV1-ORDER EXTENSIONALITY COVERAGE WIDENED (2026-06-25):**
   the `ArrayAxiom` read-congruence proof context now records the BV1 endpoint
   consequence of asserted true `bvult` facts (`lhs = #b0`, `rhs = #b1`) and
   finite array equality can use those known read values when they cover the
   whole BV1 index domain. This closes the BTOR `ext16` and `ext26` rows through
   the existing `ReadCongruence` certificate path. Re-running the exact ABV
   audit moved **141/169 → 143/169** dominant and **Lean unsat 57/83 → 59/83**,
   with **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact now
   has **55** `array-axiom-unsat` rows and **24** remaining `bare-unsat` rows.
   Remaining ABV bare-unsat work is conditional-array families, remaining
   extensionality/order rows, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV CONCAT-XOR FINITE EXTENSIONALITY COVERAGE WIDENED (2026-06-25):**
   the equality closure now records the zero-xor fact `bvxor(x, y) = 0 -> x = y`,
   pushes equality through same-shaped `concat` terms, and lets finite array
   equality consume asserted read-equality facts when those reads cover the full
   finite BV-index domain. This closes the BTOR `ext23` row through the existing
   `ReadCongruence` certificate path. Re-running the exact ABV audit moved
   **143/169 → 144/169** dominant and **Lean unsat 59/83 → 60/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact now has
   **56** `array-axiom-unsat` rows and **23** remaining `bare-unsat` rows.
   Remaining ABV bare-unsat work is conditional-array families, remaining
   extensionality/order rows, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV FINITE ROW-WISE EXTENSIONALITY COVERAGE WIDENED (2026-06-25):**
   the finite-array equality checker now reads both arrays at candidate indices
   collected from store chains and recorded read facts, normalizes those reads
   through contextual read-over-write facts, and accepts row equality only when
   equalities or known BV1 read values prove agreement over a complete finite
   BV-index domain cover. This closes the BTOR `ext19`, `ext24`, and `ext25`
   rows through the existing `ReadCongruence` certificate path. Re-running the
   exact ABV audit moved **144/169 → 147/169** dominant and **Lean unsat
   60/83 → 63/83**, with **mismatches=0, audit_errors=0, timeouts=0**. The
   refreshed artifact now has **59** `array-axiom-unsat` rows and **20**
   remaining `bare-unsat` rows. Remaining ABV bare-unsat work is conditional
   array families (`arraycond*`), the remaining extensionality/order row
   `ext13`, residual read/write shapes (`read9`, `write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV SYMBOLIC-COVER/IMPLICATION EXTENSIONALITY COVERAGE WIDENED
   (2026-06-25):** the checked `ArrayAxiom` read-congruence lane now proves
   BV1 disjunctions of the form `¬antecedent ∨ consequent` by assuming the
   antecedent and checking the consequent, recognizes complete symbolic finite
   BV-domain covers from pairwise-distinct read indices, reads back through
   stored arrays whose equality is itself proven by such a complete read cover,
   and has a BV1 order-profile rule for arrays whose false/true rows are aligned
   by equal index-order bits. This closes `read9`, `write16`, `write17`, and
   `ext13` through the existing `ReadCongruence` certificate path. Re-running
   the exact ABV audit moved **147/169 → 151/169** dominant and **Lean unsat
   63/83 → 67/83**, with **mismatches=0, audit_errors=0, timeouts=0**. The
   refreshed artifact now has **63** `array-axiom-unsat` rows and **16**
   remaining `bare-unsat` rows. Remaining ABV bare-unsat work is now mostly
   conditional array families (`arraycond*`), the residual `ext11` row, and
   cvc5-specific BV/array proof gaps.
   **ABV ARRAY-ITE ALL-TRUE BRANCH-COVER COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` read-congruence lane now recognizes BV1-indexed,
   BV1-valued array-valued `ite` terms that are read as true at both concrete
   BV1 indices while every possible leaf array is guarded by an asserted
   `not (read0 && read1)` constraint. This closes `arraycond3`, `arraycond5`,
   `arraycond6`, `arraycond7`, and `arraycond8` through the existing
   `ReadCongruence` certificate path. Re-running the exact ABV audit moved
   **151/169 → 156/169** dominant and **Lean unsat 67/83 → 72/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact now has
   **68** `array-axiom-unsat` rows and **11** remaining `bare-unsat` rows.
   Remaining ABV bare-unsat work is now the residual conditional array family
   (`arraycond11`, `arraycond12`, `arraycond13`, `arraycond14`, `arraycond18`),
   `ext11`, and cvc5-specific BV/array proof gaps.
   **ABV CONTEXTUAL ITE-BRANCH/SELF-UPDATE COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` read-congruence lane now saturates equalities through
   `ite` terms whose conditions are known, reduces equal-branch array `ite`s,
   records compound BV1 guard values, detects equivalent BV1 terms with
   conflicting known values, and handles the narrow self-update branch split
   where `a = store(a, i, v)` forces the readback at `i`. This closes
   `arraycond11`, `arraycond12`, `arraycond13`, `arraycond14`, `arraycond18`,
   and `ext11` through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **156/169 → 162/169** dominant and
   **Lean unsat 72/83 → 78/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. The refreshed artifact now has **74** `array-axiom-unsat`
   rows and **5** remaining `bare-unsat` rows, all cvc5-specific:
   `bug637.delta`, `issue9041`, `bvproof2`, `issue9519`, and `proj-issue321`.
   **ABV CVC5 SAME-CELL STORE/RANGE COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` read-congruence lane now detects contradictory
   derived equalities when same-cell store injectivity forces two same-width BV
   values whose conservative unsigned ranges are disjoint. The range recognizer
   is intentionally small (constants, symbols, zero-extension, concat,
   equal-branch `ite` union, and non-wrapping add) and only refutes equalities
   already derived by the certificate lane. This closes the cvc5
   `issue9519` and `proj-issue321` rows through the existing
   `ReadCongruence` certificate path. Re-running the exact ABV audit moved
   **162/169 → 164/169** dominant and **Lean unsat 78/83 → 80/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact now has
   **76** `array-axiom-unsat` rows and **3** remaining `bare-unsat` rows:
   `bug637.delta`, `issue9041`, and `bvproof2`.
   **ABV CVC5 STORE-RESTORE NO-OP COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` store-chain lane now recognizes the cvc5
   `bug637.delta` no-op/restore pattern: write a definitely distinct cell,
   perform a store that writes the original value back to the other cell, then
   restore the first cell from the original array. This closes the row through
   the existing `StoreShadowing` certificate path without invoking bit-blast
   trust. Re-running the exact ABV audit moved **164/169 → 165/169** dominant
   and **Lean unsat 80/83 → 81/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. The refreshed artifact now has **77** `array-axiom-unsat`
   rows and **2** remaining `bare-unsat` rows: `issue9041` and `bvproof2`.
   **ABV CVC5 SAME-VALUE STORE-CHAIN COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` store-chain lane now proves same-base store chains
   equal when every write stores the same definitely equal value and both write
   index sets cover each other, including small concrete BV ranges such as a
   zero-extended BV1 index covered by concrete writes at `0` and `1`. This
   closes the cvc5 `bvproof2` row through the existing `StoreShadowing`
   certificate path without invoking bit-blast trust. Re-running the exact ABV
   audit moved **165/169 → 166/169** dominant and **Lean unsat 81/83 → 82/83**,
   with **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact
   now has **78** `array-axiom-unsat` rows and **1** remaining `bare-unsat`
   row: `issue9041`.
   **ABV CVC5 SIGNED-BV1 READ-CONGRUENCE GAP CLOSED (2026-06-25):**
   the checked `ArrayAxiom` read-congruence lane now uses conservative static
   BV range facts for `bvult` guards, fixed-sign `sign_extend`, full-width
   `extract`, singleton-range equivalence, and disjoint-range index
   distinctness. It also recognizes Boolean contradictions of the form
   `P = not Q` once the certificate lane independently proves `P = Q`. This
   closes the cvc5 `issue9041` row through the existing `ReadCongruence`
   certificate path without invoking bit-blast trust. Re-running the exact ABV
   audit moved **166/169 → 167/169** dominant and **Lean unsat 82/83 → 83/83**,
   with **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact
   now has **79** `array-axiom-unsat` rows and **0** remaining `bare-unsat`
   rows; the residual ABV non-dominant audit entries are checked `unknown`
   search-frontier rows (`rw34`, `arraycond9`).
   **EXACT ABV DOMINANCE ROW CLOSED (2026-06-25):** the checked
   `ArrayAxiom` read-congruence lane now recognizes ITE branch exhaustion:
   `ite(c,t,e)` cannot be disequal from both `t` and `e`. The evidence front
   door runs this structural refuter before the general solver only on small
   assertion DAGs, so tiny unsat frontier rows avoid the expensive bit-blast
   path while large SAT rewrite rows still replay models first. This closes
   BTOR `rw34` and `arraycond9` as `array-axiom-unsat` with real-Lean
   reconstruction. Re-running the exact ABV audit moved **167/169 → 169/169**
   dominant and **Lean unsat 83/83 → 85/85**, with **mismatches=0,
   audit_errors=0, timeouts=0**. The refreshed artifact now has **84**
   `sat-model` rows, **81** `array-axiom-unsat` rows, **3**
   `bv-abstraction-unsat` rows, **1** `alethe-unsat` row, and no `unknown` or
   `bare-unsat` exact-audit entries.
4. **Two of the three "deprioritized hard rows" are actually cheap, decider-already-
   built, dominance-*eligible* wins — do NOT deprioritize them.** The deciders exist;
   the blocker is **one IR change**, and it is itself the highest-leverage move:
   - Add **`Sort::Uninterpreted(SortId)`** (an interned `Copy` id, mirroring the
     existing `Sort::Datatype(DatatypeId)`) and generalize **`Sort::Array`
     index/element to `SortId`** — **one change** that unlocks **both** QF_UF-over-
     uninterpreted-sorts (route to the *already-built* `solve_qf_uf_online` e-graph,
     not the BV over-approximation the parser currently forces) **and** Int-indexed
     arrays (QF_ALIA/QF_AUFLIA, currently ~0% purely on this). Both already have
     Alethe/Lean cert routes (`euf_alethe`, congruence/ROW certs) → directly
     Pareto-dominance-eligible. This is *one* keystone, not two, and it is near-term.
     **SLICE LANDED (2026-06-25):** arity-0 SMT-LIB `declare-sort` now stays
     first-class as `Sort::Uninterpreted(SortId)` with replayable EUF model tokens;
     parser/writer round-trip declared sorts, and `check_auto` routes pure
     many-sorted EUF through the e-graph path.
     **ARRAY SLICE LANDED (2026-06-25):** `Sort::Array` now carries sort-valued
     index/element metadata (`ArraySortKey`) instead of BV widths only; SMT-LIB
     parses/writes free `(Array Int Int)` terms, `select`/`store` typecheck over
     the real component sorts, and `check_auto` proves the congruence-UNSAT
     slice for Int-indexed arrays; at that point model-producing non-BV array SAT
     shapes still returned `unknown` pending generic projection.
     **MODEL/SCALAR ROUTE SLICE LANDED (2026-06-25):** non-BV arrays now have a
     replayable `Value::GenericArray`; the evaluator handles generic
     `const-array`/`select`/`store`; lazy ROW/extensionality projection compares
     full `Value`s and reconstructs generic arrays; and `check_auto` routes the
     Bool/linear-Int array slice through arithmetic DPLL. `(Array Int Int)` free
     reads, ROW conflicts, and disequality witnesses now replay as `sat`/`unsat`
     instead of blanket `unknown`. Local fair-slice remeasurement moved QF_ALIA to
     **3/5 decided, DISAGREE=0** (artifact under `bench-results/local/`), while
     QF_AUFLIA remains **1/3** and QF_UF-overbound remains **4/6**. Remaining
     keystone work: refresh committed baselines, then broaden from the current
     Bool/linear-Int array slice to mixed AUFLIA/UF and other non-BV component
     sorts.
     **ARRAY-ARGUMENT UF PREREQ LANDED (2026-06-25):** UF signatures now admit
     array-valued parameters (but still reject array-valued results), and
     `FuncValue`/UF model projection use full-`Value` tables whenever a signature
     mentions arrays. SMT-LIB now parses AUFLIA shapes such as
     `g : (Array Int Int) -> Int`, and `check_auto` proves the narrow congruence
     conflict `a=b ∧ g(a)≠g(b)` as `unsat`. This is deliberately scoped: the
     broader lazy ROW/extensionality route still needs a scalar backend that can
     solve UF+LIA with array-argument applications before QF_AUFLIA remeasurement
     should be expected to move materially.
     **MIXED ROW+UF ROUTE LANDED (2026-06-25):** lazy ROW/extensionality now has
     a `QF_UFLIA` scalar backend and `check_auto` routes non-BV
     Bool/linear-Int+UF array slices through it. Model projection preserves UF
     interpretations and completes missing UF/non-Int values before replay, so
     SAT shapes such as `select a (idx a)` replay. Local QF_AUFLIA fair-slice
     remeasurement is **2/6 decided, DISAGREE=0** (the common parsed set expanded
     from three to six after array-argument UF admission). Remaining blockers are
     now concrete: scalar Int-array timeout (`bug337`), array term shapes outside
     the current ROW fragment (`bug330`, `swap...`), and missing
     array-equality-to-UF congruence refinement (`bug336`).
     **STORE-DISJUNCTION REFUTER LANDED (2026-06-25):** the array fast path now
     exploits the valid consequence
     `store(a,i,v)=b ∧ store(a,j,w)=b ⇒ i=j ∨ a=b` by splitting the two branches
     and delegating each branch refutation to the checked EUF congruence refuter.
     This closes the `bug336` corpus pattern (`f(x)≠f(y)` refutes `x=y`;
     `g(a)≠g(b)` refutes `a=b`) and moves the local QF_AUFLIA fair slice to
     **3/6 decided, DISAGREE=0**. Remaining QF_AUFLIA blockers: scalar Int-array
     timeout (`bug337`) and array-valued structural terms outside the current ROW
     fragment (`bug330`, `swap...`).
     **STRUCTURAL ROW COVERAGE SLICE LANDED (2026-06-25):** the lazy ROW
     abstraction now preserves array-valued UF arguments at scalar application
     boundaries, lowers `select(ite c a b, i)` to scalar branch reads, permits store
     ROW misses to point at scalar read expressions, and lets mixed array+UF queries
     fall through past the UF-arithmetic overbound `unknown` into the array route.
     Local QF_AUFLIA fair-slice measurement remains **3/6 decided, DISAGREE=0**
     (artifact under `bench-results/local/`), but the frontier moved: `bug330` and
     `swap...` are no longer structural ROW rejections. Remaining blockers are now
     scalar UFLIA Boolean atom cap (`bug330`), swap-chain replay/refinement
     incompleteness, and the scalar Int-array timeout (`bug337`).
     **PROJECTION-COMPLETION SLICE LANDED (2026-06-25):** the AUFLIA ROW scalar
     backend now falls back from non-budget online-UFLIA `unknown` to eager
     UF+arithmetic, and `FunctionElimination::project_model` completes
     non-application symbols before evaluating full-`Value` UF argument keys. This
     removes the concrete array-valued-UF projection failure exposed by `swap...`;
     the local QF_AUFLIA fair slice remains **3/6 decided, DISAGREE=0**. The
     remaining misses are now scalar-engine frontiers, not IR/modeling blockers:
     `bug330` has a 339-atom Boolean UFLIA abstraction (current cap 48),
     `swap...` reaches lazy-LIA timeout, and `bug337` remains a scalar Int-array
     timeout.
     **BOUNDED LIA-PROBE + CLEAN SWAP-CHAIN REFUTER LANDED (2026-06-25):**
     arithmetic DPLL now probes the shared online LIA DPLL(T) spine under a
     real deadline before falling back to the legacy certified route, and the
     array fast path has a narrow sound refuter for clean symmetric store-swap
     chains. Local QF_AUFLIA fair-slice measurement remains **3/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-swap-chain-refuter.json`); the
     cvc5 `swap...` corpus instance is still not closed. The next useful work is
     a stronger scalar UFLIA Boolean/relevance engine for `bug330`, a real
     array-permutation/ROW normalizer for `swap...`, or the scalar Int-array
     timeout in `bug337`.
     **PERMUTATION-CHAIN REFUTER LANDED (2026-06-25):** the clean swap-chain
     recognizer is now a memoized array-permutation normalizer, and proven
     array-unsat refuters run at the `check_auto` front door before expensive
     scalar normalization / UF+arithmetic. This closes the exact cvc5
     `swap_t1_pp_nf_ai_00010_004` instance via `array-unsat-refuter`. Local
     QF_AUFLIA fair-slice measurement is now **4/6 decided, DISAGREE=0**
     (artifact `qf-auflia-after-permutation-refuter.json`; Z3 remains 6/6).
     At that point, remaining QF_AUFLIA misses were only scalar-search frontiers:
     `bug330` (339 Boolean UFLIA atoms vs cap 48, then lazy-LIA timeout) and
     `bug337` (pure Int-array lazy-LIA timeout).
     **UFLIA/UFLRA DEADLINE + CAP DIAGNOSTIC LANDED (2026-06-25):** the
     integrated `Dpll<CombinedIncremental*>` drivers now actually consume the
     computed wall-clock deadline (`solve_with_deadline`) and classify exhausted
     runs as timeout `unknown`; the UFLIA Boolean atom cap is raised to 384 under
     that guard. Local QF_AUFLIA fair-slice measurement remains **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-uflia-deadline-cap.json`). The
     frontier sharpened: `bug330` is no longer rejected by the old 48-atom
     admission cap; it reaches online UF+LIA and declines on an uncertified
     Boolean-layer theory model, then the array route times out. `bug337`
     remains the pure Int-array lazy-LIA timeout.
     **MEASUREMENT TIMEOUT + SCALAR-ABSTRACTION DIAGNOSTICS LANDED
     (2026-06-25):** `measure_corpus` / `measure_graduated` now pass the harness
     timeout into `SolverConfig::timeout` instead of only killing the worker
     externally. Lazy ROW/extensionality now gives each scalar backend call only
     the remaining outer deadline and annotates scalar-backend unknowns with
     CEGAR round/site/lemma counts; the legacy arithmetic DPLL loop likewise
     reports atom/blocking-lemma counts. Local QF_AUFLIA fair-slice measurement
     remains **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-scalar-abstraction-diagnostics.json`). The remaining
     misses are now localized to the initial scalar abstraction: `bug330` fails
     at ROW round 0 with 62 select sites, then 832 arithmetic atoms / 4 blocking
     lemmas; `bug337` fails at extensionality round 0 with 152 select sites,
     then 1374 arithmetic atoms / 2 blocking lemmas. Next useful work is scalar
     relevance/atom reduction, not more array lemmas.
     **ARITHMETIC ATOM CANONICALIZATION LANDED (2026-06-25):** the legacy
     arithmetic DPLL abstraction now shares reversed order atoms, pushes negated
     order atoms to their order-complement, folds self-comparisons/equalities to
     constants, and caps the online LIA probe at 1s under a wall-clock budget so
     large abstractions leave most time to the fallback. Local QF_AUFLIA remains
     **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-arith-atom-canonicalization.json`). `bug330` improves from
     832 to 802 arithmetic atoms and from 4 to 7 fallback blocking lemmas before
     timeout; `bug337` is unchanged at 1374 atoms / 2 blocking lemmas.
     **SCALAR BOOLEAN SHORT-CIRCUITING LANDED (2026-06-25):** the arithmetic
     abstractor now folds Boolean constants/identical branches for `and`/`or`/
     `xor`/`=>`/Bool equality/Bool `ite` and skips dead branches before allocating
     their arithmetic atoms. This is a sound cleanup, but it is neutral on the
     current hard slice: local QF_AUFLIA remains **4/6 decided, DISAGREE=0**
     (artifact `qf-auflia-after-boolean-simplification.json`), `bug330` remains
     802 atoms / 7 blocking lemmas, and `bug337` remains 1374 atoms / 2 blocking
     lemmas. Next useful work is no longer shallow Boolean simplification; it is
     scalar relevance / Boolean-layer model certification for `bug330`, or a
     smaller initial extensionality/model-construction route for `bug337`.
     **SCALAR SNAPSHOT PREPROCESSING LANDED (2026-06-25):** lazy
     ROW/extensionality now flattens positive top-level conjunctions before
     sending the scalar abstraction through the existing replay-safe
     `propagate_values`/`solve_eqs` preprocessing wrapper. This exposes generated
     aliases and constants to word-level elimination while preserving the normal
     projection/replay gate for `sat`. Local QF_AUFLIA is still **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-scalar-preprocess-flatten.json`),
     but `bug337` moves from 1374 atoms / 2 blocking lemmas to 946 atoms / 7
     blocking lemmas at 10 s; at 30 s it reaches 19 blocking lemmas and still
     times out. `bug330` remains 802 atoms and times out after 6 blocking lemmas.
     Next useful work is a real `bug337` SAT/model-construction shortcut or
     `bug330` Boolean-layer model certification/relevance.
     **ONLINE LIA/LRA BOOLEAN-LEAF MODEL LIFT LANDED (2026-06-25):** standalone
     online arithmetic drivers now lift final DPLL assignments for declared
     Boolean leaves into the returned arithmetic model before replay. This fixes
     a real replay gap for Boolean-structured scalar formulas, with LIA/LRA
     regressions of the form `p ∧ (x < y ∨ y < x)`. It is neutral on the current
     AUFLIA slice: **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-online-boolean-model-lift.json`), `bug330` remains 802 atoms
     / 6 blocking lemmas and `bug337` remains 946 atoms / 7 blocking lemmas. A
     trial 3s online-LIA probe cap was rejected because it did not decide either
     hard file and reduced `bug330` fallback progress; keep the 1s cap until the
     online path itself is stronger.
     **SCALAR LIA BOUND-LEMMA + LARGE-CORE CUTOFF LANDED (2026-06-25):** the
     legacy arithmetic DPLL fallback now seeds certifiable two-literal integer
     bound mutex lemmas for simple asserted lower/upper contradictions
     (`x >= 1` with `x <= 0`, etc.) and skips deletion-based core minimization
     on scalar abstractions above 128 theory atoms. Small formulas still get
     minimized cores; large formulas avoid spending most of their budget in
     simplex core shrinking. Local QF_AUFLIA remains **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-bound-lemmas-core-cutoff.json`),
     but scalar throughput moved materially: at 10 s `bug330` reaches 40
     blocking lemmas (27 upfront bound lemmas) and `bug337` reaches 46 blocking
     lemmas (150 upfront bound lemmas); a 30 s `bug337` run reaches 84 blocking
     lemmas before the pure Boolean skeleton times out. The next useful work is
     now Boolean-skeleton scaling / relevance / incremental SAT after many
     learned clauses, or a replay-gated SAT/model-construction shortcut for
     `bug337`.
     **WARM SCALAR BOOLEAN SKELETON LANDED (2026-06-25):** the legacy arithmetic
     DPLL fallback now encodes its pure-Boolean scalar skeleton to CNF once and
     keeps a warm `IncrementalSat`, adding each learned theory blocking clause
     incrementally instead of rebuilding through the general SAT-BV path every
     round. SAT candidates still go through arithmetic model reconstruction and
     original-assertion replay. Local QF_AUFLIA remains **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-warm-scalar-bool-skeleton.json`),
     but the scalar frontier moved sharply: at 10 s `bug330` reaches 608 learned
     scalar clauses and `bug337` reaches 788; a 30 s `bug337` run reaches 1670
     before `rustsat-batsat` times out. The next useful work is now SAT search
     quality / relevance over the learned-clause Boolean skeleton, or a
     replay-gated SAT/model-construction shortcut for `bug337`; CNF rebuild
     overhead is no longer the bottleneck.
     **CURRENT-POLARITY INTEGER-BOUND CORES LANDED (2026-06-25):** dynamic
     scalar LIA conflicts now try a cheap two-literal integer-bound core before
     falling back to the large full-theory slice. This captures assigned
     complement bounds such as `not (x <= 1)` as lower bounds (`x >= 2`) and
     keeps the resulting lemmas on the existing certificate/replay path. Local
     QF_AUFLIA remains **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-cheap-bound-core.json`), but route diagnostics improve:
     `bug330` reaches 1143 scalar blocking lemmas at 10 s (was 608 after the
     warm skeleton), while `bug337` reaches 860 (was 788). The residual blocker
     is still learned-clause search quality / relevance on a large scalar
     Boolean skeleton, or a replay-gated `bug337` model-construction shortcut;
     cheap bound-core extraction is not enough by itself to close the two hard
     files.
     **INTEGER LOCAL-SEARCH SCALAR PROBE LANDED (2026-06-25):** the deterministic
     one-sided `pbls` model finder now supports `Int` variables with finite,
     formula-constant-guided moves, and the lazy ROW/extensionality scalar
     boundary runs it for 100 ms after model-sound preprocessing and before the
     exact scalar backend. Any `sat` still reconstructs through preprocessing and
     replays through the array path; misses fall through. Local QF_AUFLIA remains
     **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-int-local-search-scalar-probe.json`; axeyum PAR-2 6.668 s).
     The diagnostic split is clearer: `bug330` is out of this probe's current
     scope because UF applications remain in the scalar snapshot; `bug337` is
     in-scope but the probe times out, then the exact scalar loop times out after
     857 rounds. Next useful work: finite UF-table local search for `bug330`, or
     SAT relevance / replay-gated model construction for in-scope `bug337`.
     **CAPPED STRUCTURAL PBLS SCORING LANDED (2026-06-25):** the one-sided
     `pbls` model finder now uses a structural Boolean cost for compact
     assertions, so nested `and`/`or`/`not`/implication/Bool-eq/xor/Bool-ite
     formulas give local-search gradients instead of a single root-satisfied bit.
     The scorer is capped by assertion DAG size and variable incidence; large
     generated constraints keep the previous cheap root score. Local QF_AUFLIA
     remains **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-structural-pbls-score.json`; axeyum PAR-2 6.668 s).
     Diagnostics remain: `bug330` is UF-out-of-scope for this probe; `bug337` is
     in scope but local search times out and the exact scalar loop reaches 865
     blocking lemmas before `rustsat-batsat` timeout. Next useful work is still
     SAT relevance / replay-gated model construction for `bug337`, or finite
     UF-table model search for `bug330`.
     **CAPPED INTEGER-DIFFERENCE CORES LANDED (2026-06-25):** scalar arithmetic
     DPLL(T) now recognizes current literals of the form `x + c <= y + d` / `<`
     as integer-difference constraints and extracts compact negative-cycle cores
     before the full-slice fallback. The common two-edge cycle (`x <= y` with
     `y + 1 <= x`) is handled directly; full Bellman-Ford is capped to
     small/medium snapshots so the large AUFLIA generated slices decline this
     extractor instead of losing SAT-search budget. Local QF_AUFLIA remains
     **4/6 decided, DISAGREE=0** (artifact `qf-auflia-after-capped-idl-core.json`;
     axeyum PAR-2 6.668 s). Diagnostics are baseline-preserving rather than a
     close: `bug330` reaches 1140 blocking lemmas and `bug337` reaches 849 before
     SAT timeout. Next useful work is still SAT relevance / model construction on
     the large scalar skeleton, or a different array/branch abstraction shortcut.
     **COMPACT BOUND-IMPLICATION LEMMAS LANDED (2026-06-25):** scalar arithmetic
     DPLL(T) now seeds asserted simple-bound monotonicity lemmas such as
     `x <= 0 => x <= 1` and `x >= 2 => x >= 1` for compact skeletons only. Each
     implication is recorded as a normal certifiable LIA core
     `{stronger_bound, not weaker_bound}`. A broader all-polarity version was
     measured and rejected on the current hard AUFLIA slice because it inflated
     upfront clauses and reduced SAT refinement rounds; the landed version is
     asserted-bound-only and gated at 256 arithmetic atoms. Local QF_AUFLIA
     remains **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-compact-bound-implications.json`; axeyum PAR-2 6.668 s).
     Hard-file diagnostics are baseline-preserving (`bug330`: 27 upfront bound
     lemmas / 1137 blocking lemmas; `bug337`: 150 / 854). Next useful work is
     still large-skeleton SAT relevance/model construction, finite UF-table model
     search for `bug330`, or a higher-level array/branch abstraction shortcut.
     **PBLS AFFINE INTEGER REPAIR CANDIDATES LANDED (2026-06-25):** the
     replay-gated `pbls` model finder now adds assertion-local integer repair
     moves for unit-affine shapes (`x`, `x + c`, `c + x`, `x - c`) inside
     equality and order atoms, using the current value of the opposite side to
     propose boundary candidates. The candidate set is capped and remains a
     one-sided model-search heuristic; accepted `sat` models still replay through
     preprocessing and the array projection path. Local QF_AUFLIA remains **4/6
     decided, DISAGREE=0** (artifact
     `qf-auflia-after-pbls-affine-repairs.json`; axeyum PAR-2 6.668 s, Z3 PAR-2
     0.105 s). Route diagnostics are flat: `bug330` remains UF-out-of-scope for
     local search, and `bug337` still times out in local search before the exact
     scalar loop reaches 855 blocking lemmas. This should be treated as a useful
     small-query model-search primitive, not a current AUFLIA frontier closer.
     The next useful AUFLIA work remains finite UF-table model search for
     `bug330`, SAT relevance/model construction for `bug337`, or a higher-level
     array/branch abstraction shortcut.
     **FOCUSED OR BRANCH REPAIR FOR PBLS LANDED (2026-06-25):** wide
     OR-shaped assertions now keep the cheap root-truth persistent score, but
     when selected by `pbls` they get a bounded structural tie-break plus a
     branch-repair planner that tries to satisfy one disjunct by applying simple
     literal repairs as a unit. This targets generated branch-selector formulas
     like `bug337` without raising the global structural-cost cap. A broad cap
     increase and a 1 s scalar local-search probe were measured and rejected:
     neither closed the hard files. Local QF_AUFLIA remains **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-pbls-focused-or-repair.json`;
     axeyum PAR-2 6.668 s, Z3 PAR-2 0.104 s). Route diagnostics remain
     baseline-shaped: `bug330` is still UF-out-of-scope for local search and
     times out after 1144 scalar blocking lemmas; `bug337` still local-searches
     to timeout, then scalar LIA times out after 851 blocking lemmas. Treat this
     as a reusable branch-model-search primitive, not a current AUFLIA frontier
     close. The next AUFLIA move should be a real branch-schedule/model
     constructor, finite UF-table reasoning for `bug330`, or SAT relevance in
     the large scalar skeleton.
     **REPLAY-PROJECTION REPAIR LANDED (2026-06-26):** lazy-extensionality
     last-candidate projection now groups asserted direct select equalities by
     concrete `(array, index)`, repairs the projected array entry, and aligns
     direct scalar read-result symbols before the existing full replay gate.
     This keeps the SAT-only soundness condition unchanged. On `bug337`, the
     10 s probe still times out at round 2 with 4096 sites / 150 array-equality
     atoms / 6973 congruence lemmas / 146 diff-skolems, but replay repair sees
     154 select candidates, makes 3 array-entry and 2 scalar-symbol changes,
     and moves the first false flattened conjunct from the direct read equality
     to ordinal 209 / term 3654: the generated queue-lock transition branch
     disjunction. `diagnose_evidence` can now render generated arena terms by
     stable term id. Next useful work is replay-guided branch-schedule/model
     repair for that disjunction, not more select-equality projection.
     **BRANCH-REPLAY DIAGNOSTICS + STORE-BASE REPAIR LANDED (2026-06-26):**
     replay failures on false branch disjunctions now report branch count, best
     branch, false-literal count, first false literal, and equality values. A
     narrow replay-only repair handles `target = store(base,i,v)` by copying the
     target array into the base everywhere except the store index, preserving the
     base cell that the store overwrites. This is pinned by a target-readback
     regression and remains behind full replay. `bug337` still does not close:
     the best branch is branch 0 with one false literal,
     `x_353 = store(x_339, x_351, 2)`, where `x_353` has extra readback entries
     `[1 -> 3]` and `[2 -> 3]` not stably propagated through the current local
     projection loop. Next useful work is a branch-consistent store-chain/readback
     projection for the queue-lock transition, not another scalar timeout knob.
     **BRANCH READBACK ALIGNMENT LANDED (2026-06-26):** the store-base repair now
     immediately aligns direct scalar readback symbols for the repaired base
     array, preventing the following select-repair pass from using stale scalar
     reads to undo branch-consistent base entries. The focused regression now
     includes a stale `z = select(a,j)` read on the repaired base. `bug337` still
     does not close, but the first false replay point moves to generated branch
     ordinal 210 / term 3879, best branch 3, with one false direct array equality
     `x_339 = x_325`: `x_339` has `[0 -> 1]`, `[1 -> 3]`, `[2 -> 3]` while
     `x_325` is still default. Next useful work is replay-gated direct
     array-equality branch repair, or the more general branch-schedule projection
     that chooses equality direction from readback support.
     **BRANCH ARRAY-EQUALITY REPAIR LANDED (2026-06-26):** a single false direct
     array equality in the chosen branch is now repaired by copying the side with
     stronger projected readback evidence into the weaker side, scored by
     non-default projected entries and direct asserted `select` support, then
     aligning scalar readbacks for the target. This is still full-replay gated.
     `bug337` still does not close, but the first false replay point moves again:
     generated branch ordinal 233 / term 10144, best branch 0, now **two** false
     literals. The first is `x_17 = store(x_2, x_15, 2)`, where `x_17` has
     `[0 -> 1]`, `[1 -> 3]`, `[2 -> 3]` and the RHS store has incompatible
     `[1 -> 2]`, `[2 -> 1]`. Next useful work is a multi-literal branch-schedule
     / store-chain projection for the queue-lock branch, not more one-literal
     local repair.
     **MULTI-LITERAL BRANCH SCHEDULE REPAIR LANDED (2026-06-26):** the selected
     false branch term is now retained, and replay projection can try a bounded
     branch-local schedule repair on a copy of the assignment: direct scalar
     equalities first, then equality-shaped array/store literals, keeping the copy
     only if that branch's false-literal count decreases. This removes the
     generated branch disjunction as `bug337`'s first replay blocker. The 10 s
     probe now reaches direct equality ordinal 185 / term 2957,
     `x_361 = x_22`, with values 1 vs 0, after 207 projection repair changes.
     Next useful work is replay-gated scalar equality projection for generated
     non-branch equalities, with direction chosen from branch/readback support.
     **SCALAR EQUALITY PROJECTION REPAIR LANDED (2026-06-26):** replay projection
     now tries bounded scalar equality repair for false generated equalities,
     testing both directions where possible and keeping only assignments that
     reduce the positive replay-conjunct false count. Scalar repair has separate
     telemetry and remains full-replay gated. A final post-scalar stabilization
     reruns select repair if scalar-triggered branch repair mutates arrays. On
     `bug337`, the 10 s probe now reports **5** scalar repairs and advances to
     direct equality ordinal 190 / term 3017, `x_366 = x_92`, values 1 vs 0,
     after 218 projection repair changes. Next useful work is support-aware
     scalar/readback propagation for the remaining generated equality chain.
     **SUPPORT-AWARE SCALAR/READBACK PROJECTION LANDED (2026-06-26):** scalar
     equality direction choice now scores asserted-select readback support,
     support-aware scalar trial counters are included in replay failure notes,
     and the bounded projection stabilization loop can walk the repeated
     queue-lock readback chain under a named 32-round cap. The `bug337` 10 s
     probe advances past the scalar chain to branch disjunction ordinal 209 /
     term 3654; best branch 0 has one false literal,
     `x_345 = store(x_331, x_334, x_351)`, after 417 projection repair changes.
     The row still does not close. Next useful work is branch-consistent
     store-chain/readback projection for that target array; a blanket
     one-literal target-readback alignment was tested and rejected because it
     regressed existing single-false branch repair behavior.
     **TARGETED REPLAY BRANCH REPAIR LANDED (2026-06-26):** after the general
     projection pass, the last-candidate replay path can now repair the exact
     single false branch literal named by full original replay and replay again.
     This remains SAT-only because the original evaluator replay is still the
     only acceptance gate. On `bug337`, the 10 s probe moves past branch term
     3654 / first false term 495 to direct readback equality ordinal 208 / term
     3440, `x_384 = x_344`, values 0 vs 1, after 419 projection repair changes.
     A wider 96-round projection cap did not move the frontier, and a targeted
     scalar fallback cycled among branch 3654, equality 3440, and lower branch
     3879. Next useful work is therefore a component-level branch-choice /
     store-chain readback projection for that three-node queue-lock cycle.
     **REPLAY BRANCH-CHOICE CANDIDATES LANDED (2026-06-26):** targeted replay now
     tries every positive branch of a failed generated disjunction on a projection
     copy, rejects full-replay-worsening trials, and chooses deterministically by
     `(total_false, branch_false, ordinal)`. This is still behind the full
     original-assertion replay gate. A focused regression covers the case where
     the reported best branch is an unrepaired Boolean literal and a later branch
     is repairable. On `bug337`, the 10 s probe moves to generated branch
     disjunction ordinal 232 / term 9841; best branch 3 has one false literal
     `x_31 = x_17`, with arrays
     `(array default 0 [0 -> 1] [1 -> 3] [2 -> 3])` vs
     `(array default 0 [1 -> 2] [2 -> 1])`, after 457 projection repair changes.
     The row remains `unknown`; next useful work is component-level
     store-chain/readback projection for this lower queue-lock branch.
     **SELECTED CARRY-COMPONENT PROJECTION LANDED (2026-06-26):** targeted replay
     branch-literal repair now solves direct array equalities as a selected carry
     component: it gathers adjacent selected/best-branch array equalities touching
     the failed pair, tries every component member as representative, aligns
     direct readback symbols, and keeps only branch-improving/full-replay-
     non-worsening candidates. A narrow targeted direct-select equality repair
     is covered too, but a direct-select stabilization experiment was rejected
     because it regressed `bug337` to branch 9841 and raised projection churn to
     1848 changes. The retained `bug337` 10 s probe moves past branch 9841 /
     `x_31 = x_17` to direct readback equality ordinal 34 / term 555,
     `x_388 = select(x_325, x_337)`, values 1 vs 0, after 571 projection repair
     changes. The row remains `unknown`; next useful work is readback/store-chain
     component repair around the `x_325/x_339` transition.
     **COUPLED BRANCH-PAIR REPLAY REPAIR LANDED (2026-06-26):** targeted replay
     now has a bounded two-generated-OR branch scheduler before the existing
     single-OR branch choice. It repairs each branch candidate of the failed OR,
     observes the next full-replay blocker, and if that blocker is a different
     OR, tries each branch candidate there on the same projection copy. A pair is
     retained only when both ORs evaluate true and the full original replay false
     count strictly decreases, so SAT remains gated by the original evaluator
     replay. On `bug337`, this is a real but incomplete frontier move: the 10 s
     diagnostic advances from OR ordinal 211 / term 4108 to OR ordinal 219 / term
     6084, with branch 3's local repair pointing back to ordinal 211. Projection
     churn rises to 647 changes and the diagnostic wall time rises to ~45 s, so
     the next AUFLIA move should be a cost-controlled multi-OR/beam branch
     scheduler or pair-edge diagnostics for the 219↔211 cycle, not unbounded
     branch-pair widening.
     **BRANCH-PAIR EDGE DIAGNOSTICS LANDED (2026-06-26):** final replay failure
     notes now include a bounded `branch_pair_candidate_diagnostics` section:
     for repairable first-OR branches whose next blocker is another OR, it scores
     each second-OR branch candidate and records the post-pair global blocker.
     On `bug337`, this proves the current monotone two-OR policy cannot move the
     new frontier. From OR 219 branch 3, all OR 211 second-branch candidates
     locally repair but worsen full replay: branches 0/3 leave two false
     conjuncts, branches 1/2 leave four, and the best branch-3 path lands on OR
     212 / term 4341. The next AUFLIA repair should therefore be a bounded
     branch-schedule/beam search that can take temporary uphill moves inside the
     beam, but still accepts only final full-replay improvement, with explicit
     caps and cycle/tabu handling for the 219 → 211 → 212 queue-lock chain.
     **BOUNDED BRANCH-BEAM REPLAY REPAIR LANDED (2026-06-26):** targeted replay
     now has a capped generated-OR beam after strict pair repair: width 8,
     64 expansions, depth 6, and at most `current_false + 4` temporary false
     conjuncts inside the beam. The projected assignment is changed only when
     the final candidate strictly improves full original replay; SAT remains
     accepted only by evaluator replay. A regression covers a four-OR schedule
     where strict pair repair rejects the temporary two-false state but the beam
     repairs later ORs to reach a replaying assignment. On `bug337`, this crosses
     the 219/211/212 branch cycle but does not close the row: the new first false
     replay point is direct readback equality ordinal 34 / term 555,
     `x_388 = select(x_325, x_337)`, values 1 vs 0, after 655 projection changes.
     The next AUFLIA move should inspect why existing select/store-chain readback
     repair cannot stabilize this post-beam assignment, or add readback
     stabilization inside accepted beam states; do not widen the beam blindly.
     **BEAM READBACK STABILIZATION LANDED (2026-06-26):** accepted branch-beam
     candidates now align direct scalar readback symbols for all asserted
     `x = select(a,i)` equalities against the candidate's repaired arrays before
     scoring the beam state. This fixes the simple stale-readback shape in a
     regression (`a = store(b,i,v)` plus `y = select(a,i)`) while preserving the
     full evaluator replay SAT gate. It does **not** move `bug337`: the first
     false replay point remains direct readback equality ordinal 34 / term 555,
     `x_388 = select(x_325, x_337)`, values 1 vs 0, after the same 655
     projection changes. The next AUFLIA move should be a direct-select repair
     diagnostic for term 555 that reports chain/direct candidates, replay false
     counts, and first blockers; the simple scalar-readback-alignment hypothesis
     is now rejected.
     **DIRECT-SELECT REPAIR DIAGNOSTICS LANDED (2026-06-26):** final replay
     failure notes now include `select_candidate_diagnostics` for direct
     `x = select(a,i)` equality misses. The diagnostic replays both targeted
     select-repair candidates on copies (store-chain/readback and direct
     array-entry), reporting whether the select equality becomes true, repair
     changes, full replay false count, and the next global blocker. On `bug337`,
     this shows select repair is reached and locally works: the chain candidate
     makes term 555 true, but only ties full replay (`same_full_replay`,
     changes=37, total_false=2) and moves the blocker to generated OR ordinal
     210 / term 3879. The direct array-entry candidate also makes term 555 true
     but worsens full replay (total_false=3) and exposes ordinal 35 / term 560
     (`0` vs `1`). The next AUFLIA move should compose the same-full-replay
     chain candidate with generated-OR scheduling under the existing final
     strict replay-improvement gate; more one-step direct-select repair is not
     the bottleneck.
     **MIXED SELECT/OR REPLAY BEAM LANDED (2026-06-26):** direct-select targeted
     replay repair now first tries a bounded mixed beam over direct select
     failures and generated OR failures, accepting only a composed strict
     full-replay improvement before mutating the projection (width 8, 64
     expansions, depth 6, `current_false + 4` temporary false conjuncts, at most
     two visits per failure ordinal). This moves `bug337` from direct select
     equality ordinal 34 / term 555 to generated OR ordinal 210 / term 3879,
     after 587 projection changes. The row is still `unknown`: OR 210 branch 0
     repairs locally but returns to the select equality at ordinal 34 with
     total_false=2, while branch 3 flows to OR 211 and the old 211→212 pair
     cycle. The next AUFLIA move should either invoke the same mixed beam from
     generated-OR failures or diagnose the 210 branch-0 → 34 select cycle
     directly; keep cost caps explicit because the 10 s diagnostic route now
     takes about 76 s wall.
     **GUARDED OR/SELECT REPLAY BEAM RETAINED (2026-06-26):** invoking the same
     mixed beam from every generated-OR replay failure was measured and rejected:
     on `bug337` it regressed the final miss from OR 210 back to select equality
     34 / term 555 and raised the 10 s diagnostic route to about 149 s wall.
     The retained OR-start path is therefore admitted only for small,
     multi-false replay surfaces (`current_false > 1`, <=64 positive conjuncts),
     with a focused regression covering an OR repair that ties replay until a
     follow-up select repair is composed. On the large AUFLIA row the guard
     restores the OR 210 frontier and ~76 s diagnostic wall time. The next
     useful AUFLIA move is cycle-specific: diagnose or repair the concrete
     210 branch-0 -> 34 select transition, not a broader OR-start beam.
     **BRANCH-SELECT CYCLE DIAGNOSTIC LANDED (2026-06-26):** final generated-OR
     replay diagnostics now compose each repairable OR branch trial with the
     direct-select store-chain/direct array-entry candidates when that branch's
     next global blocker is a direct `x = select(a,i)` equality. On `bug337`,
     this confirms the concrete 210/34 queue-lock: branch 0 followed by the
     select-34 store-chain repair makes term 555 true but remains
     `worse_full_replay` at total_false=2 and lands back on OR 210 / term 3879;
     the direct array-entry select repair also makes term 555 true but worsens
     to total_false=3 and exposes ordinal 35 / term 560. The next useful AUFLIA
     move is no longer diagnostic: implement a cycle-aware replay repair for
     `210 -> 34 -> 210` that can keep the branch-0 chain repair while forcing an
     alternate OR-210 branch or component-level store-chain change, still under
     the final strict full-replay improvement gate.
     **GUARDED BRANCH-SELECT CYCLE REPAIR LANDED (2026-06-26):** the
     alternate-branch version of that pattern is now implemented for small
     replay surfaces: after branch repair -> direct select repair -> same OR,
     try a different branch from the post-select state and accept only a final
     strict full-replay improvement (8 branches, 32 trials, current_false <= 2,
     <=64 replay conjuncts). A focused regression covers the useful shape. The
     large `bug337` attempt was measured and rejected before the guard: it did
     not move the frontier from OR 210 / term 3879 and raised route time from
     ~77 s to ~93 s, so the production repair is guarded off for that large
     row. The next AUFLIA move is specifically component-level store-chain /
     branch-state repair inside `210 -> 34 -> 210`; simply trying another OR
     branch after the select repair is ruled out for `bug337`.
     **RETURNED-OR BRANCH/SELECT DIAGNOSTIC LANDED (2026-06-26):**
     branch/select candidate diagnostics now include OR-local details for the
     first global blocker after a composed branch+select trial. On `bug337`,
     branch 0 -> select 34 chain repair returns to OR 210 with best branch 0
     and exactly one false literal: term 580,
     `x_339 = store(x_325, x_337, 2)`, with lhs
     `(array default 0 [0 -> 2] [1 -> 3] [2 -> 3])` and rhs
     `(array default 0 [0 -> 2] [1 -> 2] [2 -> 1])`. The next repair target is
     therefore preserving the select-34 store-chain readback while repairing
     branch-0 store-definition term 580 / its component arrays.
     **GUARDED SAME-BRANCH STORE RESIDUAL REPAIR LANDED (2026-06-26):**
     a target-side residual repair now handles the small-surface case where the
     branch/select cycle returns to the same OR, the same branch is still best,
     and exactly one false literal remains with shape
     `target = store(base, i, v)`: rebuild `target` from the current repaired
     `base` and accept only under a strict full-original-replay improvement.
     A focused regression covers preserving `c = store(a,3,7)` after
     `5 = select(a,i)` repairs `a[2]`. The unguarded large `bug337` probe was
     measured and rejected: it did not move the frontier from OR 210 / term 3879
     and raised route time to ~87 s. With the small-surface guard restored,
     `bug337` is back in the prior unknown regime (solve ~76.9 s before evidence
     cleanup). The next AUFLIA move is residual-candidate/component-array
     diagnostics explaining why the concrete term-580 target-side repair is not
     accepted on the large row, not another broad branch-choice or store-target
     repair.
     **SAME-BRANCH RESIDUAL DIAGNOSTIC LANDED (2026-06-26):** branch/select
     candidate diagnostics now try the same-branch residual candidate on
     diagnostic copies and emit rows such as
     `chain+same_branch_store_target`. On `bug337`, term 580's target-side
     repair is locally effective and keeps select term 555 true, but full replay
     remains `worse_full_replay` with total_false=2 and the first global blocker
     moves to OR 209 / term 3654. OR 209's best branch is branch 3 with one
     false literal, term 3650, over the same two array values flipped:
     `(array default 0 [0 -> 2] [1 -> 2] [2 -> 1])` vs
     `(array default 0 [0 -> 2] [1 -> 3] [2 -> 3])`. The next AUFLIA move is a
     paired OR-210/OR-209 component-array consistency repair, not another
     isolated term-580 target repair.
     **RESIDUAL FOLLOW-UP OR DIAGNOSTIC LANDED (2026-06-26):** the same
     diagnostic now tries one best-branch follow-up when the residual state
     exposes a different generated OR, emitting rows such as
     `chain+same_branch_store_target+followup_or209_branch3`. On `bug337`,
     this repairs OR 209 branch 3 locally and preserves select 34, but full
     replay remains total_false=2 and moves to OR 219 / term 6084. OR 219's
     best branch 3 has one false literal, term 1402, comparing
     `(array default 0 [0 -> 1] [1 -> 2] [2 -> 1])` with
     `(array default 0 [1 -> 2] [2 -> 1])`. The next AUFLIA move is therefore a
     bounded multi-hop component-array chain repair/diagnostic with explicit
     replay-improvement gating, not a two-OR special case.
     **BOUNDED RESIDUAL CHAIN REPAIR LANDED (2026-06-26):** on small replay
     surfaces, the production branch/select-cycle repair now follows up to four
     generated-OR hops after the same-branch residual store-target repair,
     records the best strict full-replay improvement, and preserves the original
     OR + select at every hop. A focused regression clears the two-OR analogue.
     The large `bug337` diagnostic now shows the chain reaches OR 236 / term
     13052 at `same_full_replay`, total_false=1; OR 236 best branch 0 has 2/2
     false literals, first false term 12950 (`3` vs `1`), and blindly repairing
     that branch worsens to total_false=2 at scalar equality term 2611. The next
     AUFLIA move is scalar-aware OR-236 handling after the residual chain, not
     more component-array-only hops.
     **SCALAR-CHOICE BRANCH REPAIR LANDED (2026-06-26):** follow-up OR repair
     now compares the greedy branch repair with a bounded scalar-choice
     candidate that explores both directions of direct scalar equalities and
     scores completed branch repairs by full replay. The small `u = v` with an
     existing `u = 0` regression now chooses `v := 0` and clears replay. On
     `bug337`, this does not move the large frontier: OR 236 still selects the
     ordinary `branch` candidate, then worsens to scalar equality term 2611.
     Therefore the next AUFLIA move is an OR-236-specific diagnostic for both
     false branch literals and their scalar side effects, not another generic
     scalar-direction heuristic.
     **OR-236 SCALAR SIDE-EFFECT DIAGNOSTICS LANDED (2026-06-26):** replay OR
     notes now include bounded false-literal details for the selected best
     branch plus simulated direct scalar choices and their replay side effects.
     On `bug337`, OR 236 branch 0 is now explicit: false scalar term **12950**
     (`510 = 2609`, values **3 vs 1**) can be locally repaired by setting
     symbol **460** from term **510** to **3**, but the next blocker becomes
     term **2611** (`2609 = 2610`, **3 vs 1**) with **branch_false=1** and
     **total_false=2**. The sibling false scalar term **12951** (`510 = 2613`,
     **3 vs 2**) symmetrically drives blocker **2615** (`2613 = 2614`,
     **3 vs 2**) with the same counts. The next AUFLIA move is a paired
     repair/diagnostic over those sibling scalar chains, or a proof that this
     late OR-236 branch must be handled by a stronger combined repair.
     **PAIRED SCALAR-CHAIN DIAGNOSTIC LANDED (2026-06-27):** the OR replay
     note now applies the selected branch's false scalar literals as a coupled
     repair, then follows up to four scalar equality blockers. On `bug337`,
     forcing OR 236 branch 0 is an oscillation: setting symbols **460/461** from
     term **510** to **3** repairs branch terms **12950/12951** and reaches
     **branch_false=0**, but the downstream blockers **2611/2615** require
     setting those same symbols back from terms **2610/2614** to **1/2**,
     returning to OR **236** with **branch_false=2** and **total_false=1**.
     The next AUFLIA move is scalar-closure-aware OR-236 branch selection:
     score candidate branches after their local scalar closure, not just by raw
     false-literal count.
     **SCALAR-CLOSURE BRANCH SCORING LANDED (2026-06-27):** replay OR notes
     now score candidate branches after branch repair plus bounded scalar
     closure. On `bug337`, this rules out a simple alternate-branch fix for
     OR 236: reported branches **0..7** all locally repair to
     **raw_branch_false=0**, then scalar closure returns replay to OR **236**
     with **final_branch_false=2** and **final_total_false=1**. The next AUFLIA
     move is no longer branch choice; it is either learning/refining the
     scalar/array constraint that makes this OR-236 branch family impossible
     under the current model or preventing production repair from spending time
     on branches that immediately close back to the same OR.
     **SCALAR-CLOSURE BRANCH REJECTION GUARD LANDED (2026-06-27):**
     residual follow-up OR repair now routes candidate branch repairs through a
     bounded scalar-closure guard. The guard declines only when scalar closure
     takes at least one scalar equality step, replay returns to the same
     follow-up OR, the repaired branch is false again, and the full replay false
     count is not lower than before the candidate. On `bug337`, the route still
     reaches OR **236** with **total_false=1** and reports the same closure-loop
     branch family, but it no longer spends a follow-up repair on
     `followup_or236_branch0_branch`. The next AUFLIA move is learning/refining
     the missing scalar/array constraint that explains the OR-236 family, not
     raw OR branch forcing.
     **SCALAR-CLOSURE SCHEDULE GUARD LANDED (2026-06-27):** the same
     returned-OR guard now wraps general multi-literal branch schedule repairs,
     including the projection repair pass and targeted replay repair. This
     blocks an earlier raw branch-forcing route that could set several scalar
     symbols, make a branch locally true, then let scalar closure return to the
     same OR with no full replay improvement. On `bug337`, the row is still
     `unknown`, but the measured diagnostic now completes normally in about
     **55 s** instead of exiting through the 180 s timeout wrapper after about
     **89 s**; projection repair changes drop from **587** to **565**. The next
     AUFLIA move remains a real scalar/array refinement for the OR-236 family.
     **SELECT-BACKED SCALAR REPAIR LANDED (2026-06-27):** scalar equality,
     direct branch-literal, and multi-literal branch-schedule repairs now use
     asserted readback equalities as backing constraints. When a repair wants
     `y = v` and the original assertions contain `y = select(a, i)`, it writes
     `a[i] := v`, realigns direct select readback symbols, and then stores the
     scalar value only if still needed. This removes the measured OR-236
     oscillation on `bug337`: the diagnostic still returns `unknown`, but the
     first replay blocker moves to scalar equality **term 3408**
     (`x_383 = x_330`, values **0 vs 1**) after **430** projection repair
     changes, with `check_auto_explained` / `solve` / `produce_evidence` each
     around **49.3 s**. The next AUFLIA move is now term-3408 scalar equality
     explanation/repair, not OR-236 branch forcing.
     **SCALAR-CANDIDATE DIAGNOSTICS LANDED (2026-06-27):** top-level scalar
     replay failures now report bounded repair candidates using the same
     select-backed path as production. On `bug337`, term **3408** has two
     locally productive choices: `x_383 := x_330` exposes OR **210** / term
     **3879**, and `x_330 := x_383` exposes OR **211** / term **4108**, both
     with `total_false=2`. A targeted scalar replay repair exists for small
     replay surfaces, but the unguarded large-row version was measured/rejected
     after raising the first diagnostic call to **113 s** and still returning
     to term **3408**; it is therefore guarded off for large generated AUFLIA
     rows. A bounded scalar+OR follow-up diagnostic now composes those exposed
     ORs with one guarded best-branch repair. On `bug337`, both obvious
     compositions are negative: OR **210** branch **0** and OR **211** branch
     **3** become locally true but worsen full replay to **total_false=3** and
     return to scalar equality term **3408**. Closure-level diagnostics now show
     the next shape: repairing scalar equality after the OR-210 branch repair
     restores **total_false=2** but exposes OR **211**, while repairing scalar
     equality after the OR-211 branch repair restores **total_false=2** but
     exposes OR **210**. A second-hop OR diagnostic now closes this as a local
     cycle: OR **210** -> OR **211** -> OR **210**, and OR **211** -> OR
     **210** -> OR **211**, each reported as `returns_first_or` after scalar
     closure. A production guard now rejects this two-hop no-progress shape for
     small replay surfaces (<=64 positive conjuncts) in branch-choice repair and
     the final single-literal OR fallback. The ungated large-row version was
     measured/rejected after moving `bug337` backward to OR **210** and about
     **72.5 s**, so the large row remains diagnostic-only at term **3408**. The
     follow-up branch-term diagnostic now identifies the concrete pair:
     OR **210** branch term **3805** (store-definition branch) and OR **211**
     branch term **4107** (copy/no-store branch). Returned-OR literal
     diagnostics refine the blocker further: 4107 fails on term **4041**
     (`x_303 = x_317`, inserted-cell array vs default array), while 3805 fails
     on term **583** (`x_331 = store(x_317,x_320,x_337)`, default array vs
     inserted-cell store RHS). A small-surface returned-OR stabilizer now
     handles the synthetic version of that shape under the strict replay gate,
     but the ungated `bug337` attempt regressed the first diagnostic phase to
     **231.8 s** and was capped at <=64 replay conjuncts; the large row is back
     to ~**52.5 s** and remains at term **3408**. A diagnostic-only direct
     returned-OR stabilization probe then ruled out the obvious large-row
     literal repair: repairing OR **210** branch **3805** false literal
     **583** (`x_331 = store(x_317,x_320,x_337)`) is `worse`
     (`total_false=3`) and returns to term **3408** with values **0 vs 1**;
     repairing OR **211** branch **4107** false literal **4041**
     (`x_303 = x_317`) is also `worse` (`total_false=3`) and returns to term
     **3408** with values **1 vs 0**. The next AUFLIA move is therefore a
     paired scalar+array or relevance-guided learned large-row constraint that
     preserves the term-3408 scalar equality while relating the 4041/583
     array-cell disagreement, not direct single-literal repair, greedy
     single-OR forcing, or more local branch enumeration.
   - Pair it with a **single-witness extensionality skolem** for arrays
     (`a≠b ⇒ select(a,k)≠select(b,k)`, one fresh `k` — what Z3/cvc5 do) replacing the
     current **`2^index-bits` enumeration** (`MAX_ARRAY_EQ_INDEX_BITS=8`), which is
     *infinite* for Int indices and already walls QF_AX at 9-bit. axeyum already has
     the lazy machinery (`ArrayElimination::abstraction()`).
   - The QF_UF weak row is **mostly Tier-B front-end coverage** (unhandled
     `(Set …)`/`(Seq …)` sorts, `sin`, `fmf.card` ≈ 25 files) — **not** a congruence
     cap (only ≈5 files hit the BV-width wall). Fix the parser, not a decider.
5. **Aim the cert budget at the *valuable* frontier, not just the easy one.** The
   highest-value certification targets are the **hard rows where cvc5 has NO proof**:
   narrow certifiable **NRA/NIA-unsat** and **array-unsat** sub-fragments. Certifying
   even a narrow nonlinear-unsat fragment to a Lean kernel is a capability **no stack
   on earth has.** Promote the existing degree-2 **SOS→Lean** chain (ADR-0040) as the
   seed and define the next narrow nonlinear-unsat cert slice as a tracked keystone.
6. **NRA path: correct the label and the overclaim.** The target is **NLSAT
   (model-constructing, single-cell projection)** / **cylindrical algebraic coverings
   (CDCAC)** — *local, model-guided* — **not** global upfront "CAD." axeyum's `nra.rs`
   is already the cvc5-style **linearization front-end**; the measured QF_NRA-cvc5
   misses are dominated by **Fourier–Motzkin LRA-backstop blowups (10/27)**, so the
   cheapest real NRA gain is a **competent LRA core to replace Fourier–Motzkin**
   ([P1.6]) + a larger cross-product budget — *before* any new nonlinear engine. The
   gap-analysis doc's "strong CAD decision side" is **overstated** (no general
   multivariate CAD module exists; `nra_degree` frontier = 2 — the scoreboard is the
   truth); align that prose down.
7. **The Lean *tactic backend* is unbuilt — demote from "pure win" to roadmap item.**
   axeyum emits Lean *modules out-of-band*; there is no in-tree tactic that imports a
   Lean goal, decides it, and discharges it in place ([P3.7] unshipped). Until it
   exists, axeyum does not beat manual Lean *in Lean's own workflow*. Build it — and
   make it **fail rather than `sorry`** (lean-smt's silent-hole fallback is the exact
   UX trap to avoid).

**Net:** certify where we're strong AND convert the one cheap IR keystone (uninterp
sorts + Int-array sorts) that is *itself* dominance-eligible; spend cert budget on
the valuable (nonlinear/array-unsat) frontier cvc5 can't touch; keep the moat claim
scoped to the axiom-clean kernel sub-fragment; and stop the decide-race only where
it's genuinely a 15-year catch-up (high-degree NRA), not where one IR change closes it.

## What "done" means

See [`docs/plan/00-north-star.md`](docs/plan/00-north-star.md) for the full
definition. In one line: **Z3 parity** = feature coverage + competitive
measured performance on the decidable/semidecidable fragments, with honest
`unknown` where undecidable; **Lean parity** = every `unsat`/`valid` result
carries a machine-checkable proof a Lean-grade kernel accepts, produced by an
untrusted search and validated by small independent checkers.

## The two load-bearing fronts

1. **Performance, measured head-to-head (Track 1).** There is no parity claim
   without a clean Z3 comparison on real corpora. **Measured reframe (2026-06-18,
   public p4dfa 113 vs Z3 — see [findings](docs/research/05-algorithms/lazy-bitblasting-p21-findings.md)
   + ADR-0037):** the lever is **word-level *reduction* before bit-blasting**
   (`solve_eqs`/canonicalize/`ite`-handling), *not* lazy bit-blasting — that slice
   is arithmetic-free, so lazy-bv CEGAR is inert (0/113 heavy ops). Reduction moved
   the number 2→7/113. The remaining gap **partitions** into: ~6 *EncodingBudget*
   (deeper reduction pulls them under the encode ceiling — the proven mechanism),
   ~9 *search-bound* (kissat-class CDCL cracks them; batsat/`xor_cdcl`/PBLS all
   miss), and ~90 *large-CNF* (reduction + genuinely hard). **Decision (both in
   parallel):** reduction leads near-term; the proof-producing CDCL core is
   incrementally modernized toward competitive as a slower parallel track. Track
   the honest pulse: **Timeout→decided**.
2. **Reduction certificates (Track 3).** Today only the clausal layer (DRAT) and
   the bit-blast reduction (miter) are independently checked; every other
   reduction is trusted. Certifying them — via an **Alethe emitter** checked by
   the Rust **Carcara** checker — is the critical path to Lean parity.

## The two engineering keystones

- **Incremental e-graph + CDCL(T) loop** (Track 1, P1.4/P1.5). Almost every lazy
  theory and all quantifier work depends on a shared congruence-closure equality
  bus and a theory-propagation loop. Build it once; it unlocks Track 2.
- **Alethe term/proof IR + emitter** (Track 3, P3.2). The format that is
  simultaneously Rust-checkable (Carcara, no C/C++), BV-shaped (matches axeyum's
  lowering and existing miter), and the on-ramp to Lean. Everything downstream in
  the proof track depends on it.

**Sequencing — pivot from leaf-BFS to keystone-DFS (2026-07-09).** A traversal
analysis over the [dependency DAG](docs/plan/01-dependency-dag.md) — the two
keystones above, a keystone-blocked deep interior (lazy arrays/EUF/BV/datatypes,
quantifier maturity, combination-at-scale, warm memory, CHC/Horn), and a skirt of
independent theory leaves — is written up in
[build-sequencing-bfs-dfs.md](docs/research/08-planning/build-sequencing-bfs-dfs.md).
Its conclusion, ranked by quality × efficiency:

1. **DFS the engine keystone `P1.4 → P1.5` now.** The breadth-first pass over the
   theory decide-rate leaves (LIA/NRA/strings) has **empirically exhausted its
   ROI**: every remaining leaf now needs this keystone (eager encodings no longer
   scale), a large-scale engine (dense-ILP MILP; 200–360 KB LPs), or a
   research-grade completeness proof (Nielsen strings). That wall — reached this
   session — is the data-driven trigger to pivot from BFS to keystone-DFS. Build
   the independent congruence checker alongside so the eager→lazy migration is
   trust-preserving.
   **First DFS follow-through (2026-07-09):** the generic `CdclT` LIA/LRA adapters
   now forward checked theory propagations from `LiaTheory`/`LraTheory` into the
   shared driver, with tests proving the propagation path fires. **Second
   follow-through:** `StringTheory::propagate` now emits conservative whole-atom
   variable-equality consequences (equality closure + disequality transport) with
   asserted-literal reasons, while deeper word-core facts stay conflict-only.
   **Third follow-through:** `solve_qf_uf_online` / `prove_unsat_qf_uf_online` now
   route through the generic replay-checked `CdclT` driver, retiring the embedded
   EUF DPLL from production (it remains test-only diagnostics). **Fourth
   follow-through:** the existing `euf-online` front-door route now calls
   `check_qf_uf_online_cdclt` with the caller's `SolverConfig`, so ADR-0055's
   QF_UF criterion (2) has fired and pure QF_UF online dispatch is default-on;
   offline EUF stays as the fallback after online `unknown`. **Fifth
   follow-through:** pure QF_LIA/QF_LRA now lead with the generic `CdclT`
   adapters (ADR-0060 update); LRA deadlines cover theory construction and every
   Fourier–Motzkin pass, and a deterministic 1,024-atom resource cap avoids the
   eager per-assert stack/cost cliff. Curated 5 s A/B preserves 10/11 LIA and
   9/11 LRA decided with zero disagreements/replay failures; the two LRA unknown
   rows improve from 5.250 s / 11.853 s to 4.838 s / 5.031 s. **Sixth
   follow-through:** Boolean-structured QF_UFLIA/QF_UFLRA now drive
   `CombinedIncrementalLia` / `CombinedIncremental` through canonical `CdclT`;
   their propagation gates exercise that production route. The arithmetic-local
   driver remains only for standalone fallback and learned-lemma diagnostics.
   **Seventh follow-through:** canonical `CdclT` now carries deterministic
   conflict-side VSIDS and phase saving, with mechanism tests and all EUF/string/
   arithmetic oracle gates clean; the 2,500-case UFLIA sweep is runtime-neutral
   at 426.17 s → 426.19 s. **Eighth follow-through:** deterministic Luby
   restarts now preserve learned clauses/activity/phases, balance the theory
   stack, and leave the same sweep neutral at 425.18 s. **Ninth
   follow-through:** deterministic LBD-based learned-clause reduction now keeps
   originals, glue clauses, and every active reason while tombstoning the worst
   half of eligible learned clauses in stable order. A forced-reduction
   pigeonhole gate matches a never-delete baseline and the full oracle matrix is
   clean; UFLIA remains neutral at 425.90 s. The planned VSIDS/phase/Luby/LBD
   search-feature migration is complete. The arithmetic-local driver remains a
   standalone fallback/diagnostic implementation rather than being retired.
   **Tenth follow-through:** the P1.6 prerequisite is now real rather than nominal:
   lazy UFBV/UFLIA routes use a projection-preserving function abstraction that
   never constructs the eager quadratic Ackermann pair set. Eager elimination
   remains unchanged for fallback and proof production. **Eleventh
   follow-through:** bounded scalar QF_UFBV now puts the e-graph and warm BV
   solver behind canonical `CdclT` with explicit same-function argument/result
   equalities. BV-infeasible arrangements learn clauses; congruence propagates
   result equality into exact BV semantics; accepted models project and replay.
   Three deterministic 512-case eager/front-door/Z3 matrices are clean, and the
   public corpus decides/agrees on 6/6 with zero replay failures. This is an
   architecture result, not a speed claim: the six-row mean is 0.061 s and
   `bug520` is about 0.332 s online versus about 0.009 s in Z3. Next reduce wide
   BV cores, generate interface equalities by relevance, and bring arrays onto
   the live bus while retaining eager certifying fallbacks. **Twelfth
   follow-through:** warm BV conflicts now reuse BatSat's failed persistent
   decision-frame selectors from the same solve, omitting irrelevant earlier
   levels with deterministic full-core fallback. A one-selector-per-literal
   prototype was measured and reverted (mean 0.061 s → 0.072 s; `bug520` 0.332 s
   → 0.382 s); decision-frame cores are neutral at 0.063 s / 0.332 s while the
   1,536-case differential matrix and 6/6 public corpus stay clean. Next pursue
   within-level precision only if it avoids repeated assumption overhead, then
   BV propagation and relevance-driven interface generation. **Thirteenth
   follow-through:** exact BV-to-EUF propagation is now live for interface sets
   up to 64 atoms (128 total probes). One round-robin candidate per state is
   proved by refuting its opposite polarity in the same warm CNF; failed frame
   selectors become the reason, pending facts survive monotone trail growth, and
   backtracking clears them. `bug520` exercises 50 interface atoms (93 probes,
   31 BV hits, 46 total combined propagations in the diagnostic run). An exact
   five-run enabled/disabled A/B measures 149.96-152.79 ms versus
   347.10-352.39 ms on that row, with corpus mean 0.034-0.036 s versus
   0.065-0.066 s; 1,536 differential comparisons and public 6/6 remain clean.
   Z3 is still ~9-11 ms, so next reduce the interface census by relevance rather
   than simply raising caps. **Fourteenth follow-through:** exact ground-distinct
   pair pruning now omits a same-function application pair only when cached
   empty-assignment evaluation proves one argument position unequal (ADR-0069).
   Equal-valued, symbolic, and failed-evaluation pairs remain. `bug520` falls
   50→20 interface atoms and 93/31/46→69/14/16 probes/BV hits/combined
   propagations; a 24-concrete-key table moves from cap-decline to `sat` with
   zero generated interfaces while the 24-symbolic-key control still declines.
   Exact release medians improve `bug520` 15.32→8.88 ms (~1.72x) and six-row
   PAR-2 mean 3.84→2.89 ms (~1.33x), with enabled variance retained and Z3 at
   8-10 ms on the row. Public 6/6, 1,536 differentials, replay, and the 760-test
   solver library remain clean. This is narrow row-level parity, not general
   UFBV parity. Next make symbolic interface creation dynamic/model-based, then
   bring arrays onto the live bus. **Fifteenth follow-through:** symbolic
   interfaces are now replay-guided and dynamic (ADR-0070). Canonical `CdclT`
   starts from the function-free relaxation, exposes a complete BV candidate,
   and materializes only equal-argument/unequal-result application pairs before
   rebuilding; partial-round UNSAT transfers and SAT remains projection/replay-
   gated. Bounds are 64 rounds / 512 materialized raw interfaces under one
   deadline. One-pair and nested two-pair fixpoints fire; a 24-symbolic-key table
   moves cap-decline→replayed `sat` with zero pairs, while a forced 276-violation
   control stops after 256 pairs at the cap. `bug520` needs one round / zero
   pairs. Ten release samples improve its median 8.88→2.84 ms (~3.12x) and
   six-row mean 2.89→0.647 ms (~4.47x); Z3's row median is 12.5 ms, making this
   narrow row ~4.4x faster. Public 6/6, 1,536 comparisons, replay, and 763 solver
   tests remain clean. Next bring arrays onto the live bus; retain cross-round
   learned state only if wider telemetry makes
   rebuild cost dominant. **Sixteenth follow-through:** base-array selects now
   participate in those replay-guided canonical rounds (ADR-0071). A new
   `abstract_arrays` boundary applies exact read-over-write without constructing
   the eager O(k²) select-pair set; equal-index/unequal-result candidates add
   index/result atoms plus select congruence. QF_AUFBV composes array-first and
   function-second abstraction, then projects functions before arrays and
   replays originals. Gates pin a two-round array conflict, a three-round
   array→UF fixpoint, a 24-symbolic-read zero-interface SAT, and the shared cap;
   768 eager/front-door/Z3 comparisons are clean. Public 1 s runs are QF_ABV
   185/193 and QF_AUFBV 48/53 decided, both DISAGREE=0 with zero replay failures.
   This is base-select congruence after exact eager ROW, not full lazy arrays.
   **Seventeenth follow-through:** read-over-write is now lazy on that same bus
   (ADR-0072). The canonical route reuses the existing ROW abstraction and
   materializes one exact guarded hit/miss axiom only when a candidate violates a
   store site. UF-bearing ROW metadata stays visible to function abstraction;
   partial UNSAT transfers and function-then-array replay still gates SAT. Gates
   pin one-axiom hit/miss conflicts, a UF-index fixpoint, and a 24-write concrete-
   miss SAT with zero ROW axioms; all 768 differential comparisons remain clean.
   Public 1 s decisions move QF_ABV 185→187/193 and QF_AUFBV 48→49/53 with zero
   disagreements/replay failures, though one tight-cap AUFBV SAT row becomes
   Unknown, so no broad performance claim is made. The recorded P1.6
   BV+LIA/`str.len` marker was already closed by ADR-0052 and is corrected as
   DONE/OBE. **Eighteenth follow-through:** array equality and disequality now
   use the same canonical bus (ADR-0073). Shared `RowCtx` equality flags receive
   one bounded diff witness plus paired reads at query/store indices; only
   candidate-violated congruence or witness implications materialize. UF-bearing
   observations remain function-abstraction roots, and cloned online probes leave
   every fallback arena pristine. Five focused extensionality mechanisms plus two
   isolation gates pass. Half of the 768-comparison AUFBV matrix now carries
   equality-bearing cases and remains clean. Public decisions hold at QF_ABV
   187/193 and QF_AUFBV 49/53 with zero disagreements/replay failures; PAR-2 means
   move 77→84 ms and 155→221 ms, so this is not a speed claim. **Nineteenth
   follow-through:** projected arrays now use deterministic majority-default
   models shared by canonical and fallback routes (ADR-0074). Votes count
   distinct observed indices, ties choose the smallest stable value, and only
   true overrides remain. Focused compact-BV/tie/generic tests pass; an end-to-end
   16-read canonical model uses default `7`, four overrides, one round, and full
   replay. The 768 comparisons stay clean and public decisions remain QF_ABV
   187/193 / QF_AUFBV 49/53 with zero disagreement/replay failures. A single
   AUFBV PAR-2 sample moves 221→206 ms but is not a speed claim. At that
   checkpoint, next was:
   merge-triggered/cross-atom queue states, e-graph-class/warm model ownership,
   proof integration, and opaque-heavy arithmetic model exchange. **Twentieth
   follow-through (proof spine):** direct equal-array/select conflicts now emit
   literal SMT-LIB `select` with `eq_reflexive`/`eq_congruent`, optional `symm`,
   and resolution (ADR-0075). Forward and reversed artifacts pass the in-tree
   checker and installed Carcara; deleting the array-equality antecedent is
   rejected. `produce_evidence` carries no reduction trust step, and the
   67-family representative real-Lean gate checks the reversed artifact. This is
   ordinary select congruence, not the disequality/diff-witness direction of
   array extensionality. At that checkpoint, next remained
   merge-triggered/cross-atom queue states,
   e-graph-class/warm models, full ROW/diff-witness proof logging, and
   opaque-heavy arithmetic model exchange. **Twenty-first follow-through:** the
   first cross-atom queue slice is live (ADR-0076). Equality obligations carry
   deterministic `new`/`delayed`/`applied` state; a candidate-false equality
   whose endpoints are connected by candidate-true flags schedules its own diff
   index only along one stable shortest path. `a=b ∧ b=c ∧ a≠c` now returns
   UNSAT with exactly two cross observations; disconnected disequalities remain
   delayed and replay SAT; a store/UF path composes with ROW; and a stress case
   declines after exactly 512 observations. The expanded 20-shape matrix keeps
   all 768 comparisons clean, now 456 equality-bearing. Public decisions and
   PAR-2 remain QF_ABV 187/193 at 84 ms and QF_AUFBV 49/53 at 206 ms, with zero
   disagreements/replay failures. This avoids the eager cross product but still
   rebuilds outer `CdclT` rounds. **Twenty-second follow-through:** ADR-0077
   identifies the queue as a compensating mechanism and supersedes it. Each array
   flag now retains its original array equality at the same canonical theory-atom
   index, so `EufTheory` handles reflexivity, transitivity, congruence, and
   backtracking directly. The transitive conflict, self-disequality, store/UF
   path, and former 512-observation stress case all refute in one round with no
   extensionality work. Candidate-true direct-symbol classes also project one
   shared majority-default model; a transitive SAT class with disjoint reads now
   replays. The strengthened 768-comparison matrix remains clean (456 equality-
   bearing), and public 1 s results remain QF_ABV 187/193 at 84 ms and QF_AUFBV
   49/53 at 205 ms, with zero disagreements/replay failures. **Twenty-third
   follow-through:** explanation-guarded base-parent select scheduling is live
   (ADR-0078). Base read parents are pre-registered on `EufTheory`; final live
   classes schedule only candidate equal-index/unequal-result pairs. A
   cross-parent lemma carries the exact merge explanation as its guard, so a
   rebuilt round can backtrack to another equality branch without retaining an
   invalid unconditional result equality. Direct-symbol equalities no longer
   prepare every query index: the new 80-array/80-read gate replays SAT in one
   round below the former 4,096-site failure boundary. Direct, transitive,
   UF-index, and Boolean-backtracking gates pass; structural store equality still
   uses ROW plus its retained observation. All 794 solver tests and 768
   comparisons pass. Public 1 s results remain QF_ABV 187/193 at 84 ms and
   QF_AUFBV 49/53 at 206 ms, with zero disagreements/replay failures.
   **Twenty-fourth follow-through (measured-leaf skirt):** ADR-0079 removes the
   BV/BV-only admission artifact while preserving the finite-scalar boundary.
   Canonical ABV/AUFBV now accepts Bool or BitVec independently at each array
   component and projects mixed shapes through the existing generic array model.
   Exact public rows `issue5925` and `issue4240` move unknown→unsat/sat in 20/5
   ms. A new 384-comparison Bool/mixed matrix joins the existing 768 comparisons;
   all 1,152 are clean, all SAT models replay, and 797 solver tests pass. The
   current host's sustained I/O load pushed four unrelated boundary rows over
   the 1 s cap, so ADR-0078's 187/193 and 49/53 remain the last comparable
   aggregate pending a low-load rerun. **Twenty-fifth follow-through:** ADR-0080
   extends the same explanation-guarded final-class scheduler to original store
   parents. A store read now participates in select congruence while retaining
   its independent lazy ROW obligation. Same-parent, congruent-parent,
   alternate-branch, unrelated-parent, UF-index, and 80-parent scaling gates
   pass; the new 384-comparison structural matrix brings the clean total to
   1,536, and all 802 solver tests pass. A fresh load sample still showed four
   blocked tasks and 13-25% I/O wait, so the comparable public aggregate remains
   ADR-0078's baseline. **Twenty-sixth follow-through:** ADR-0081 moves bounded
   local ROW final-check into the live search. Each store site reserves three
   atoms dormant; a violated candidate inserts two permanent valid ROW clauses
   and resumes the same `CdclT` instance with learned clauses, phase state, and
   activities retained. Hit/miss and two nested obligations close in one outer
   round; a replayable equality branch backtracks safely; a UF-bearing index
   reuses its aligned e-graph atom; and the shared 512-interface cap remains
   exact. The new 384-comparison dynamic-ROW matrix brings the clean total to
   1,920, and all 807 solver tests pass. Commit `07be0883` passed the exact-SHA
   pre-push gate. Next: array-valued ITE/default/UF and pair-generating merge
   events with general dynamic atom insertion, store/ITE/array-valued-UF class
   models, warm reuse, full ROW/diff-witness/equality-chain proof logging,
   opaque-heavy arithmetic model exchange, and the low-load public aggregate
   remeasure. **Twenty-seventh follow-through:** ADR-0082 lands the general
   bounded scalar-interface insertion required by that next step. `CdclT` now
   maps appended SAT variables explicitly to theory atoms, so atoms created
   after Tseitin auxiliaries preserve all existing clause/trail/reason indices.
   `EufTheory` grows equality atoms only over pre-observed sides, while exact BV
   owns the arena clone and extends aligned atom state. Candidate-violated
   function, explanation-guarded base/store-select, and bounded array-equality/
   extensionality refinements now resume the same canonical search with learned
   clauses, phases, activities, e-graph state, and warm BV state retained. The
   former two/three-round controls pin one round; the new 384-comparison dynamic-
   interface matrix brings the clean total to 2,304, and all 809 solver tests
   plus the 11-test differential binary pass. Commit `39cc92ce` passed the exact-
   SHA pre-push gate and is on `origin/main`. Next: array-valued ITE/default/UF
   and merge-triggered events requiring new e-graph terms, store/ITE/array-valued-
   UF class models, warm reuse, full ROW/diff-witness/equality-chain proof
   logging, opaque-heavy arithmetic model exchange, and the low-load public
   aggregate remeasure. **Twenty-eighth follow-through (deadline robustness):**
   ADR-0083 closes a measured pre-SAT cancellation hole. A 1 s public AUFBV row
   with five BV1024 dividers had returned after 437.5 s because lowering was
   deadline-blind. One-shot and incremental AIG construction now poll the shared
   absolute deadline through DAG and wide-circuit loops; expiry is
   `Unknown(Timeout)`, and canonical BV shares the cumulative conservative
   clause estimator. The exact row now declines in 1 ms at 157,298,694 projected
   clauses versus the 64M ceiling. A fresh nine-row cvc5-regress-clean run is 7
   SAT / 1 encoding-budget unknown / 1 unsupported, with DISAGREE=0 and zero
   replay failures; admitted scalar and AUFBV divider regressions exercise the
   polling path. Commit `85e007b2` passed the exact-SHA gate. Next remains the
   structural array target: array-valued UF/select events, cyclic function/array
   projection, non-symbol class models, warm reuse, and online proof logging;
   retain a broader low-load ABV/AUFBV aggregate remeasure as the measured skirt.
   **Twenty-ninth follow-through:** ADR-0084 closes the array-valued UF-result
   boundary. IR/SMT-LIB and abstraction now admit finite Bool/BitVec array
   results; original applications remain e-graph parents while their fresh
   result arrays own projected observations. Final parent classes union split
   reads across congruent applications, then array-first/function-second
   projection supplies both array results and array-valued function keys before
   mandatory replay. Stores, array ITEs, direct equality/disequality, and nested
   scalar-UF use pass 288 analytic/front-door/Z3 comparisons with zero
   disagreements; all 815 solver unit tests and the exact-SHA push gate pass.
   Commits `b1bc1836`/`e944f7c1` are on `origin/main`. Next: structural store/
   ITE/default class projection, warm reuse, online ROW/extensionality/equality-
   chain proof logging, opaque-heavy arithmetic exchange, and the low-load
   public aggregate remeasure.
   **Thirtieth follow-through:** ADR-0085 closes the bounded structural class-
   equation slice. Array-ITE equality is decomposed exactly before search, so a
   selected branch equality reaches the live e-graph; candidate-true store/ITE/
   constant equations then realize total leaf-array values without changing any
   scalar read, under explicit leaf/depth/fixed-point/deadline caps. Array-result
   owners and array-valued UF keys compose with the same array-first/function-
   second projection and mandatory replay. A 16-shape matrix contributes 192
   direct/front-door/Z3 comparisons with zero disagreements; all 816 solver
   units, the existing AUFBV and array-result matrices, strict clippy, and the
   exact-SHA gate pass. Design/implementation commits `e47da7a1`/`da957695` are
   on `origin/main`. Next: true warm array/UF ownership with learned-clause reuse,
   nested/extended array operators, online ROW/diff-witness/equality-chain proof
   logging, opaque-heavy arithmetic exchange, and the low-load public aggregate.
   **Thirty-first follow-through:** ADR-0086 advances the deferred half of
   ADR-0030 with retained warm structural reads. `IncrementalBvSolver` now gives
   observed store/constant/array-ITE reads private scalar owners and installs
   their exact definitions once in the persistent CNF; user roots and equality-
   dependent cross-array lemmas remain scoped, only direct leaf owners project
   models, and original replay gates SAT. Exact 512-node/256-depth admission
   limits defer one-over inputs. A 64-seed matrix contributes 192 warm/
   `check_auto`/Z3 comparisons with zero disagreement; 816 solver units, 77
   symbolic-execution tests, and the complete EVM suite pass. Design/
   implementation commits `4caed2ec`/`47c152ec` are on `origin/main`.
   Measurement is honest: EVM depth 32 is 0.368 ms for frontend ITE folding vs
   30.933 ms for observation-triggered retained definitions. Next: activate warm
   ROW definitions only after candidate violation, then warm structural equality/
   extensionality and array-valued UF parents, memory BMC/k-induction, and proofs.
   **Thirty-second follow-through:** ADR-0087 makes retained warm ROW candidate-
   triggered. Each observed structural read keeps one exact bounded transitive
   scalar summary as dormant metadata; a candidate-false summary becomes a
   permanent root in the same CNF/SAT instance under one shared deadline.
   Replayable misses install zero summaries, nested violated store chains close
   through one compact summary, selectors/cores remain sound, direct leaves alone
   project, and original replay still gates SAT. The 64-seed warm/`check_auto`/Z3
   matrix remains 192/192 clean; all 816 solver units, 77 symexec tests, and the
   complete EVM suite pass. Design/implementation commits `c777e756`/`3977f78b`
   are on `origin/main`. Measurement improves depth 32 from 30.933 ms to 11.257
   ms, while ITE folding still wins at 0.405 ms and remains default. Next: warm
   structural equality/extensionality and array-valued UF parents, then memory
   BMC/k-induction, online array proofs, and the remaining performance gap.
   **Thirty-third follow-through:** ADR-0088 retains scalar-keyed array-valued UF
   applications as first-class warm leaves. Finite Bool/BV arguments and read
   indices reuse the scalar warm abstraction; private application arrays and
   read owners are constrained by conditional argument/index congruence; and
   equal concrete argument tuples merge split observations before full-value
   function projection, owner filtering, and original replay. Store and array-
   ITE parents compose with ADR-0087 summaries. Exact 64/65-parent admission,
   ten all-feature mechanism/differential tests, and 192 warm/`check_auto`/Z3
   comparisons are clean; all 816 solver units, 77 symexec tests, the canonical
   array-result integration, and complete EVM gates pass. Design/implementation
   commits `41019413`/`f2bb16ab` are on `origin/main`. The EVM corpus has no
   array-valued UF application, so this increment makes no EVM timing claim.
   ADR-0089/0090 subsequently land warm relations and structural equality;
   ADR-0091 lands relation flags, ADR-0092 lands direct array-valued UF
   parameters, and ADR-0093 lands supported structural parameter expressions.
   Nested array-valued application keys, memory BMC/k-induction, online array
   proofs, and the remaining performance gap remain.
   **Thirty-fourth follow-through:** ADR-0089 adds retained warm array
   relations without approximating structural equality. Positive equality
   accepts direct symbols and scalar-keyed array-result UFs, tracks applications
   independently of reads, merges projection classes before function-table
   construction, hides private owners, and replays. Top-level disequality over
   symbol/store/constant/ITE/application parents introduces one private BV diff
   index and two exact retained reads, so ADR-0087 summaries supply structural
   semantics on demand. Eight default/nine all-feature mechanism/differential
   tests add 192 warm/`check_auto`/Z3 comparisons with zero disagreement; all
   816 solver units, 77 symexec tests, the ADR-0088 suite, and complete EVM gates
   pass. Design/implementation commits `d891c901`/`70c8a15c` are on
   `origin/main`. EVM has no whole-array relation root, so no timing change is
   claimed. ADR-0090 takes the positive structural-equality step next, and
   ADR-0091 subsequently lands Boolean relation flags. Array-valued parameters,
   memory BMC/k-induction, online proofs, and the remaining performance gap stay
   open.
   **Thirty-fifth follow-through:** ADR-0090 lands retained warm structural array
   equality. Top-level positive equality over supported store/constant/array-ITE
   parents now uses cached private constructor owners, bounded old/future shared-
   index observations plus a private probe, class-aware fixed-point realization
   before array-valued function construction, private-owner filtering, and
   original replay. Default structural-equality gates cover no-read SAT,
   constants/store conflicts, selected/unselected ITE branches, array-result UF
   composition, push/pop and one-shot cores, Bool elements, BV256 components,
   exact limits, timeout, and a 64-seed warm/`check_auto` matrix. ADR-0090 is
   accepted. ADR-0091 subsequently closes Boolean relation flags; array-valued
   parameters, memory BMC/k-induction, online array proofs, and broader low-load
   aggregate timing remain.
   **Thirty-sixth follow-through:** ADR-0091 lands retained warm Boolean array
   relation flags. Supported array equality atoms nested under scalar Boolean
   structure now become private candidate-sensitive flags. The true branch adds
   guarded paired-read equality observations and participates in owner merging
   and structural realization only when the candidate assigns the flag true; the
   false branch adds one guarded private diff witness. Existing and newly
   introduced read indices are observed under the guard, private symbols stay
   filtered, and replay gates SAT. Five focused relation-flag tests cover
   forced-true structural equality, no-read total model projection, forced-false
   disequality, conflict with an active equality, push/pop, one-shot cores, and
   private filtering. The ADR-0088/0089/0090 suites remain green with stale
   nested-Boolean deferrals converted to positive coverage. Next: array-valued
   parameters, memory BMC/k-induction, online array proofs, and broader low-load
   aggregate timing.
   **Thirty-seventh follow-through:** ADR-0092 lands retained warm direct array-
   valued UF parameters. Direct finite-array symbols can now key retained array-
   valued UF parents. Scalar keys still use the warm scalar abstraction; array-
   key equality uses either an active retained equality class or a private
   ADR-0091 relation flag, so congruence roots stay Boolean/BV-only. Projection
   now separates non-equal array-key classes with deterministic full array
   values before building `FuncValue` tables, preserves user-visible select
   constraints, ignores private guarded relation reads as public entries, and
   keeps original replay as the SAT gate. The focused warm array-UF parent suite
   covers independent-key SAT replay, asserted-equality UNSAT, the private
   relation-flag count, and structural array-key deferral. ADR-0093
   subsequently lands supported structural array-valued parameter expressions.
   Nested array-valued application keys, memory BMC/k-induction, online array
   proofs, and broader low-load aggregate timing remain.
   **Thirty-eighth follow-through:** ADR-0093 lands retained warm structural
   array-valued UF parameters. Supported store/constant/array-ITE expressions
   can now key retained array-valued UF parents; scalar dependencies inside
   those keys are retained before solving, private structural key owners are
   realized against the original structural terms before full-value function
   projection, and application read congruence reuses active equality classes or
   ADR-0091 relation flags. The focused warm array-UF parent suite covers scalar
   UF dependencies inside a structural key, relation-flag separation of
   independent structural keys, asserted structural-key equality UNSAT, and
   the former nested array-valued application-key deferral. ADR-0094
   subsequently lands supported nested application keys.
   **Thirty-ninth follow-through:** ADR-0094 lands retained warm nested array-
   valued UF parameters. Supported array-valued `Apply` terms can now key
   retained array-valued UF parents directly (`f(g(a))`) and under supported
   structural keys (`f(store(g(a), k, v))`). Direct nested keys use the inner
   application's private projection symbol; structural keys use replay-safe
   rewritten structural terms whose nested applications are projection symbols,
   preserving array-first/function-second projection order. The focused warm
   array-UF parent suite covers direct nested-key SAT replay, asserted
   nested-key equality UNSAT, structural keys with nested application bases, and
   the existing structural relation-flag separation gate. **Fortieth
   follow-through:** memory-aware k-induction extends the reachability driver to
   array/symbolic-memory transition systems. `prove_safety_k_induction_with_memory`
   runs the base case through `bounded_model_check_with_memory`, checks each
   inductive step with `IncrementalBvSolver::check_with_memory`, maps unsupported
   theory shapes to `SafetyOutcome::Unknown`, and keeps Safe unbounded but
   validation-backed until array proof export exists. Focused BMC tests cover an
   inductive array property and a reachable symbolic-memory counterexample.
   Next: certified memory k-induction, memory PDR/IMC, online array proofs,
   nested/extended arrays, and broader low-load aggregate timing.
2. **Keep a thin measured-leaf-BFS skirt in parallel** — measured-ROI leaves only
   (NRA tail, strings-Nielsen); fold the feature/scale-blocked leaves
   (dense-ILP MILP, large-LP performance) into a funded engine phase rather than
   grinding them as slices (measure-don't-seed).
3. **Run the proof/trust-ledger spine (`P3.5 → ledger→0`) in parallel** — the
   quality axis of the north star; each theory that becomes lazy under (1) drops
   a trust-ledger entry via its Alethe reduction proof.
4. **After P1.5 lands: DFS the categorical gap `P3.8 → P4.6 CHC/Horn`** — the
   largest single categorical gain vs Z3 (unbounded verification); its Farkas/LRA
   interpolant slice can start early inside the (2) skirt, de-risking the path.

## Track map

| Track | Folder | Theme |
|---|---|---|
| 1 — Engine & Performance | [`track-1-engine/`](docs/plan/track-1-engine/README.md) | SAT inprocessing, preprocessing, SAT-core modernization, e-graph, CDCL(T), theory combination, PBLS, strategy; 2026-06-27 `bvumulo` now uses the word-width threshold encoding `a > all_ones / b` instead of a doubled-width multiplier, avoiding BV512 multiplication terms for BV256 overflow checks while preserving SMT-LIB totality |
| 2 — Theories & Breadth | [`track-2-theories/`](docs/plan/track-2-theories/README.md) | lazy BV, lazy arrays, EUF, LIA cuts (+ unbounded backstop), NRA/CAD, quantifiers, strings, FP polish, datatypes, **breadth backlog** (sequences/sets/sep-logic/finite-fields/co-datatypes/rec-fun) |
| 3 — Proofs & Lean | [`track-3-proof-lean/`](docs/plan/track-3-proof-lean/README.md) | trust ledger, LRAT, Alethe IR+emitter, Carcara-checked QF_BV, embedded checker, reduction proofs, Lean kernel + reconstruction, **Craig interpolation**; 2026-06-27 `prove_unsat_to_lean_module` now falls back to normalizing the assertion spine by splitting top-level conjunctions and stripping repeated top-level double negations after direct reconstruction declines, closing the consumer-facing shape-sensitivity gap for common `hyps ∧ ¬goal` queries without perturbing existing direct routes |
| 4 — Use Cases & Frontend | [`track-4-usecases-frontend/`](docs/plan/track-4-usecases-frontend/README.md) | warm lazy memory, symexec/CFG frontend, OMT/MILP, SMT-LIB command surface, benchmarking & the perf gate, **CHC/Horn (PDR/Spacer)**, **synthesis/abduction**; 2026-06-27 memory-aware incremental assumptions now cover one-shot array/UF branch feasibility through the full dispatcher, `SymbolicMemory` gives frontends a typed load/store helper plus conservative write-log normalization / compact read-over-write `ite` construction, `SymbolicExecutor::branch` and `explore_cfg` auto-promote array/UF queries to the memory/theory-aware route when needed, `explore_cfg` / `explore_cfg_checked` provide DFS with model-witnessed targets plus concrete replay hooks, and `minimize_model` / `produce_evidence_minimized` / `prove_minimized` give property/verification frontends replay-checked lexicographic counterexample minimization over selected Bool/BV<=127/Int symbols, with metadata-aware variants for signed two's-complement BV objective order. `axeyum-property` v0 is now the first typed SDK over that surface: Bool/BV/Int handles, assumptions, proof/minimized-counterexample calls, `ProofCertificate` packaging for checked `EvidenceReport` plus best-effort standalone Lean modules and stable evidence/trust/Lean summaries, scalar/tuple/derived-struct `Symbolic` declarations and model lifting including signed-order two's-complement fixed-width Rust integers, named-field `symbolic_struct` bundles, `.equals()` aliases, property-owned Bool/BV/Int builder aliases, and `Property::all`/`any` Boolean folds that keep construction errors explicit, reusable typed BV overflow predicates, native-scalar counterexample-to-`#[test]` rendering with caller-owned prelude/setup snippets, helper-rendered Boolean / `Result<(), E>` / `Result<bool, E>` replay adapters, deterministic `#[cfg(test)]` module assembly, deterministic multi-case fixture file assembly, direct named/tuple aggregate initializer snippets, and explicit nested aggregate field composition, and the committed/generated SDK corpus gate with 16 graduated workflows, deterministic executable baseline comparisons for scalar counterexamples, an actual fixed-seed proptest shrunk counterexample, struct and replay counterexamples, proved assertions, assumption-backed proved assertions, and a Kani-style assume/assert counterexample baseline, machine-readable `corpus.json`, DISAGREE=0, and 1/1 Lean-required coverage. The SMT-LIB front door also now handles `push`/`pop`/`check-sat-assuming`/`reset-assertions` in both incremental and single-query helpers without flattening scoped scripts, exposes `solve_smtlib_get_model` for user-declared model bindings, `solve_smtlib_get_assignment` for active top-level named assertions, and `solve_smtlib_get_assertions` for scoped rendered assertion snapshots, records `set-info`/`set-option`/`get-info`/`get-option` metadata with `solve_smtlib_get_info` and `solve_smtlib_get_option` responses, and explicitly rejects full `(reset)` in the shared-arena model |
| 5 — Verified Systems (IR reflection) | [`track-5-verified-systems/`](docs/plan/track-5-verified-systems/README.md) | the seL4-inspired application trajectory (ADR-0056, 2026-07-06): reflect compiled Rust — rustc MIR **and** LLVM IR — into `axeyum-ir` and discharge panic-freedom / memory-safety / constant-time (2-safety) / cross-IR & cross-profile translation-validation / protocol-FSM-refinement obligations push-button, every `sat` replayed against the real compiled function and every `unsat` on the Track 3 certificate ladder; prototyped green 2026-07-02/03 (rounds Q–U in `crates/axeyum-verify/tests/`): shared-vocabulary CFG symbolic executors for both IRs, 16 cross-IR equivalence proofs (if-conversion, strength reduction, O0≡O2, switchInt≡switch, umin idiom, hypothesis-gated `unreachable`), a 5-shape wrong-transform refutation corpus with replay-checked countermodels, exact panic specifications from rustc's own checks (overflow; division `b==0`; signed `∨ (a==MIN ∧ b==-1)`; array bounds over all 2^64 indices) with `catch_unwind` witness replay, and a checksum micro-module proved end-to-end on both platforms incl. the protocol receiver property — individual proofs in milliseconds; phases P5.1 front end (crate-ify; ADR-gated) → P5.2 contracts/modular → P5.3 kernel obligations (page-table math, constant-time, FSM refinement) → P5.4 fuzz-oracle loop → P5.5 a real external target, measured (DISAGREE=0, no seeding) |

Track 4 optimization note (2026-06-27): all three OMT modes now span LIA and BV
(`box`, `lexicographic`, and `Pareto`). BV Pareto is covered for unsigned,
signed, maximize, and minimize directions, and malformed/out-of-fragment BV
Pareto objectives degrade to `Unknown` instead of hard solver errors.

Cross-cutting: [`00-north-star.md`](docs/plan/00-north-star.md) (definition of
done), [`01-dependency-dag.md`](docs/plan/01-dependency-dag.md) (the end-to-end
DAG, keystones, critical paths), and
[`gap-analysis-z3-cvc5-2026-06-22.md`](docs/plan/gap-analysis-z3-cvc5-2026-06-22.md)
(the latest practical gap analysis against Z3/cvc5), plus
[`references/`](docs/plan/references/README.md) (the distilled top-down review of
Z3, cvc5, bitwuzla, CaDiCaL/Kissat, Carcara, lean4/nanoda, lean-smt that this
plan is built on).

## Consumer-track integration (2026-06-27): converge the apps onto `main`

The demand-pull consumer track (apps that *use* axeyum to hunt bugs / prove
software properties — the [`docs/consumer-track/`](docs/consumer-track/README.md)
program) was started on an isolated `consumer-track` worktree/branch and has
**diverged** from `main`. This section is the standing plan to **merge and
integrate** it, one verifiable new-crate-only increment at a time. It is owned by
the consumer-integration lane and does not touch core IR/solver/rewrite files.

**State at takeover (2026-06-27).** Two efforts forked:
- On `main`: `axeyum-property` (+ `axeyum-property-macros`) — the typed
  prove-or-counterexample SDK — built out independently and is now a **superset**
  of the branch's version (phantom `Bv<W>`, derive, counterexample→`#[test]`
  replay fixtures, signed minimization, `ProofCertificate`/Lean modules, a
  committed `property/SCOREBOARD.md` with proptest/Kani baselines, DISAGREE=0).
- On `consumer-track` (worktree `../axeyum-consumer`): `axeyum-property`
  (+ `-derive`) **plus** the apps that never landed on `main` —
  **`axeyum-evm`** (EVM symbolic bug-hunter, Phase 1+2), **`axeyum-verify`**
  (+ `-macros`, the `#[axeyum::verify]` Rust verifier, Phase 1+2), and
  **`axeyum-consumer-bench`** (the measurement backbone).

**Reconciliation decisions.**
1. **`axeyum-property`: `main`'s is canonical.** It supersedes the branch's
   design; the branch's `axeyum-property` + `axeyum-property-derive` are
   **retired, not ported**. Any unique helper the apps need (e.g. a `Witness`/
   reproduce export, `BvArray` shape) is folded into `main`'s `axeyum-property`
   as a small additive slice.
2. **`axeyum-evm` ports as a new crate.** It depends only on
   `axeyum-ir` + `axeyum-solver` (zero property coupling), so the port is
   low-friction; adapt to `main`'s (newer, warm-array) solver API. Independent
   concrete-interpreter revalidation of every witness keeps **DISAGREE = 0**.
3. **`axeyum-verify` (+ `-macros`) ports as new crates.** Its only tie to the
   branch's SDK is `axeyum_property::Witness` (2 call sites) → rebind to
   `main`'s `axeyum-property` counterexample/replay surface.
4. **`axeyum-consumer-bench` ports and is extended** into the headline
   deliverable below.

**The measurement deliverable (answers the standing review).** The ~190
warm-incremental symbolic-execution commits (array/memory/UF readback folding —
the angr/unicorn foundation, and the right capability) are **real but
unmeasured**: the frontier dashboard has only SMT levers, nothing for
symbolic-execution depth, memory-shape coverage, or vs-hevm/angr. Integration
stands up a committed **EVM/symexec capability scoreboard** — the analog of
`DOMINANCE.md` for the symbolic-execution engine: paths explored / memory-shapes
decided / bug-classes found, with **DISAGREE = 0** vs an independent oracle (the
EVM app's own concrete interpreter always; vs hevm/halmos when installed,
honestly install-gated). This gives the engine work a number, and the shape
coverage it reports is what decides **special-case folding vs the general warm
array/UF theory (U6)** — driven by which memory shapes the corpus actually
exercises, not an unbounded fold-list.

**Sequenced increments (each: builds + gates + DISAGREE=0, committed).**
- **I0** — ✅ DONE (`79193f2`) — recorded this plan; reconciled the docs.
- **I1** — ✅ DONE (`3a22101`) — ported `axeyum-evm` (no API drift); folded the
  `reproduce` layer into `main`'s `axeyum-property`; added the workspace member.
- **I2** — ✅ DONE (`19d11b4`) — ported `axeyum-verify` + `axeyum-verify-macros`
  (own `Witness` enum; `syn`/`quote` declared directly).
- **I3** — ✅ DONE (`c840cab`) — **EVM/symexec capability scoreboard**
  (`docs/consumer-track/evm/SCOREBOARD.md`, `cargo run -p axeyum-evm --example
  measure_evm`): 6/6 decided, DISAGREE=0, 5 memory-shape classes.
  `axeyum-consumer-bench` deliberately *not* ported (retired-API + duplicative).
- **I4a** — ✅ DONE (`b774df2`) — reconciled `UPSTREAM-FEEDBACK.md`: U6 is now
  *measured* by the scoreboard (it is the special-case-vs-general arbiter).
- **I4b** — ✅ DONE (`0945c69`, `fad0650`) — `MemoryEncoding::{IteFold (default),
  WarmArray}` in `axeyum-evm`; WarmArray lowers storage to real `select`/`store`
  via `SymbolicMemory` + `assume_auto`. Scoreboard gained warm-vs-`ite` + a
  store-chain depth sweep. **Measured result (refuted the naive hypothesis):**
  `ite`-fold is *faster* and the gap **grows** with depth (depth 32: ~3 ms vs
  ~14 ms), because the array path falls to the one-shot memory dispatcher while
  `ite`-fold stays warm with constant-folding concrete guards. Recorded in
  `UPSTREAM-FEEDBACK.md` U6: the gap is *incremental-array performance*, not
  capability — a true warm lazy-array engine (retained state across
  `enter`/`backtrack`), not one-shot re-dispatch. `ite`-fold stays the default.
  **ADR-0086 update (`4caed2ec`/`47c152ec`):** supported store/constant/ITE
  reads now retain exact private definitions and SAT state instead of taking the
  one-shot dispatcher. The release rerun still loses at depth 32 (0.368 ms ITE-
  fold vs 30.933 ms warm), localizing the next lever to candidate-triggered ROW
  activation rather than more frontend folding.
  **ADR-0087 update (`c777e756`/`3977f78b`):** exact transitive scalar summaries
  now stay dormant until a violating candidate, then persist in the same warm
  CNF. Depth 32 improves 2.75x to 11.257 ms; ITE-fold remains faster at 0.405 ms,
  so the default is unchanged and the remaining gap is explicit.

**Forward backlog (autonomous continuation — pick the top unblocked item).**
Each is a self-contained increment under the standing discipline below; do them
in order unless a dependency says otherwise. Update the STATUS consumer lane +
this list as each lands. Done: scoreboard coverage broadened to 8/8 incl. the
`INVALID` bug class (`db36e0e`); per-app PLAN/STATUS co-located on `main`
(`a059c6f`).

*App A — `axeyum-evm` (Phase 3):*
1. **Multi-tx invariants** — a call sequence with persistent storage between txs.
   The keystone; sliced for soundness (each slice gated DISAGREE=0):
   - **A1.1** — ✅ DONE (`4159cd3`) — `max_txs` DFS driver: on a normal halt with
     txs remaining, advance to the next tx with **fresh per-tx calldata**,
     **persisting storage** but **resetting stack/memory**. Multi-tx safe proofs
     work; a multi-tx-only revert is reached soundly (reported `Unknown` until a
     validated witness exists, never a wrong verdict). Default `max_txs=1`
     preserves all single-tx behavior.
   - **A1.2** — ✅ DONE (`e0751c4`) — `concrete::run_sequence` (persistent storage
     across txs) is the multi-tx oracle; `revalidate` replays the sequence.
   - **A1.3** — ✅ DONE (`e0751c4`) — `lift_witness` lifts the full per-tx input
     sequence; `Finding.prior_txs`; the cross-tx *init-then-revert* bug is now
     *reported* with a replay-validated 2-tx witness, and the scoreboard has a
     Multi-transaction section (bug-found + safe-proved), DISAGREE=0 over 8 cases.
   - Note: `bounded_model_check_with_memory` needs a full `TransitionSystem`
     encoding of a whole-contract step — heavier than the DFS re-entry used here.
   **A1 keystone COMPLETE.** Next A-item: **A2 `CALL`/`DELEGATECALL` modeling**.
2. **`CALL`/`DELEGATECALL`/`CREATE`/`EXTCODE*` + environment modeling** so paths
   explore *past* these opcodes instead of going `Unknown`. The soundness key
   (keeps DISAGREE=0): model each as a **witnessed symbolic environment input** —
   a fresh symbol on the symbolic side, *replayed from the witness* on the
   concrete side (the env-oracle generalizes calldata to opcode-produced
   nondeterminism). Sliced:
   - **A2.1** scalar env opcodes that pop `k`, push one fresh value: `GAS`,
     `BALANCE`, `EXTCODESIZE`/`EXTCODEHASH`, `RETURNDATASIZE`, and block/context
     (`TIMESTAMP`/`NUMBER`/`GASPRICE`/`COINBASE`/`CHAINID`/`ADDRESS`/`ORIGIN`/…).
     *Path:* `opcode.rs` (`Op::Env{pops}`), `symbolic.rs` (env-symbol allocator,
     recorded per path), `concrete.rs` (env-value oracle consumed in order),
     witness (`env_inputs`). *Exit:* a contract that branches on `gas()`/context
     explores past it; a bug after it is reported + replay-validated, DISAGREE=0.
   - **A2.1** — ✅ DONE (`a695198`) — scalar env opcodes are witnessed inputs;
     paths explore past them; scoreboard `environment` class, 10/10, DISAGREE=0.
   - **A2.2** — ✅ DONE (`f3f45c8`) — `CALL`/`CALLCODE`/`DELEGATECALL`/`STATICCALL`
     push a witnessed success flag and continue; return-length `>0`/symbolic →
     `saw_unknown` (return data unmodeled, no false safe).
   - **A2.3** — ✅ DONE (`1cfbf47`) — re-entrancy: after a non-static call, storage
     is adversarial (later `SLOAD`s read a witnessed value); `STATICCALL` does not
     dirty. The DAO threat model; SafeUpToBound stays sound.
   **A2 phase COMPLETE.** Scoreboard 12/12 decided, DISAGREE=0, `environment`
   class covering env opcodes + CALL + re-entrancy. Next A-item: A3 (WASM +
   vs-hevm, install-gated) — deferred; pivot to App C (C4) which is fully buildable.
3. **WASM in-browser surface** (the delivery differentiator) + the vs-hevm/halmos
   scoreboard once those tools are installable (the `ExternalOracle` seam exists).
   *Status:* the consumer crates are wasm-clean, but the `wasm32` build is
   **blocked on `UPSTREAM-FEEDBACK` U8** — `axeyum-solver` does not compile for
   `wasm32` (`abv.rs` uses `std::time::Instant` directly instead of the cfg'd
   `web_time` shim). Resume once U8 lands; the vs-hevm part stays install-gated.
4. **Opcode-precision deepening (DONE, ongoing)** — turn `Unknown`-forcing
   havoc/unsupported opcodes into precise models (concrete-operand fast path,
   symbolic→sound `Unknown`), each added to the differential-fuzz pool:
   - **BYTE** (0x1a) — **fully precise** (concrete index → shift+mask; symbolic
     index → bounded 32-way `ite`) (`7b9633b`, `41af539`).
   - **SIGNEXTEND** (0x0b) — **fully precise** (concrete → `sign_ext`+`extract`;
     symbolic → bounded 31-way `ite`) (`22bb92e`, `41af539`).
   - **EXP** (0x0a) — concrete base+exp → constant-fold via `Word::pow`
     (`74c6b6a`); symbolic exponent still havocs (a faithful symbolic 256-bit
     modular pow is heavy).
   - **CALL return data** — `CALL`/`STATICCALL`/`DELEGATECALL` with a concrete,
     32-aligned, bounded (≤4 words) return region now writes *witnessed* fresh
     bytes to memory (over-approximating any callee return) instead of `Unknown`;
     witness replays in the concrete oracle (`58b4fa7`). Symbolic-length/unaligned
     regions stay sound `Unknown`.
   - **LOG0–LOG4** (0xa0–0xa4) — modeled as no-op pops (logs have no effect on
     execution state); previously `Unsupported`, which hid every bug *after* a log
     (`810a6fe`). A major false-`Unknown` source closed — real contracts log on
     essentially every state change.
   - **BLOCKHASH** (0x40 → `Env(1)`) and **MSIZE** (0x59 → `Env(0)`) — witnessed
     env values (`b82eba7`).
   - **CALLDATACOPY** (0x37) — *precise* calldata→memory copy for a concrete,
     32-aligned, bounded region (the calldata is already symbolic, so the witness
     replays) (`a5894be`). In essentially every ABI dispatcher.
   - **CODECOPY** (0x39) — *precise* code→memory copy (code is concrete →
     constant words; raw bytecode now retained on `Program.code`) (`9a68459`).
   - **CREATE/CREATE2** (0xf0/0xf5) — re-entrant deploy: witnessed new-contract
     address + adversarial post-state storage (constructor may re-enter)
     (`fbb2c6e`). Closes the factory-pattern gap.
   - **SELFDESTRUCT** (0xff) — clean halt like STOP (pop beneficiary, end the
     path safely) (`f4bdba4`).
   - *Next candidates:* RETURNDATACOPY tied to a modeled return buffer;
     EXTCODECOPY (external code genuinely unknown → fresh-witnessed both sides);
     symbolic-exponent EXP (heavy). **Common runtime opcodes are now covered** —
     the remaining gaps are rarer or genuinely nondeterministic.

*App C — `axeyum-verify` (Phase 3 / hardening):*
4. **General CFG→`TransitionSystem` lowering** — replace the hand-written
   `CounterLoopSystem` with a system *built from the AST*, giving warm-solver reuse
   across unroll depths for deep loops (scalar state; arrays-in-loop-state stay on
   the one-shot `_with_memory` route, off U6). Sliced:
   - **C4.1** — ✅ DONE (`6c7be0c`) — `ScalarLoopSystem` over **N scalar variables**: `state_vars` =
     one symbol per loop variable per step; `init` = pre-loop values; `trans` =
     `guard ? body-effect : stutter` where the per-variable next-value expressions
     come from lowering the **straight-line** loop body (assignments) against the
     pre-state symbols; `bad` = the in-loop assertion/overflow predicate. Reuse the
     `lower` expression machinery seeded with a pre-state env. *Path:*
     `verify/src/{bmc,lower}.rs`. *Exit:* a multi-variable accumulator loop (e.g.
     `sum += i; i += 1; assert(sum < BAD)`) verified via warm `bounded_model_check`,
     cross-checked against the unroll route (same verdict), DISAGREE=0.
   - **C4.2** — ✅ DONE (`pending-commit`) — nested `if` inside the loop body:
     guarded assignments fold into each variable's next-value via `ite` in the
     `update` closure (demonstrated by an even-counter loop, decided via warm BMC).
   - **C4.3** — ✅ DONE (`pending-commit`) — `loop_system::loop_system(AstLoop)`
     builds a `ScalarLoopSystem` from AST guard/update/assert exprs, **re-lowering
     each BMC step against the step's pre-state via the real `lower_pure_expr`** (no
     duplicated lowering). Update panic classes (overflow/`÷0`) fold into the bad
     predicate, so safety stays sound. Tested: an AST counter loop finds its
     assertion violation, proves safe out of reach, and catches an update overflow
     — all via warm `bounded_model_check`.
   - **C4.4** — ✅ DONE (`pending-commit`) — `loop_from_program` auto-detects the
     `let(const)* ; while { straight-line body }` shape and builds an `AstLoop`
     (params = free state, pre-loop lets = pinned state, body `Assign`/`Assert`
     threaded into per-variable updates + position-correct asserts via expression
     substitution); `check_program_loop` runs it on the warm route. Cross-checked
     against the unroll route (`verify_program`): the two **agree** on a buggy and
     a safe loop.
   - **C4.5** — ✅ DONE (`pending-commit`) — nested `if`/`else` in the loop body
     folds into guarded `ite` updates (`fold_body`): each arm-assigned variable
     becomes `ite(cond, then-value, else-value)`, and arm asserts are guarded by
     the (negated) branch condition. Cross-checked vs unroll on a branching loop.
   - **C4.6** — ✅ DONE (`pending-commit`) — `verify_program_warm` routes a loop
     program's *decision* through the warm BMC route (warm `SafeWithinBound` →
     `Verified`), deferring to the unroll `verify_program` for the bug witness,
     the cert, and out-of-fragment programs. Justified by a measured **~40× warm
     speedup** on safe deep loops (scoreboard scaling sweep, the *opposite* of the
     EVM I4b result); agrees with direct `verify_program` on buggy and safe loops.
     *Follow-up (C4.7):* a cert on the warm route so `verify_program_warm` Verified
     results are `certified`/Lean-backed too.
   **C4 phase COMPLETE** (C4.1–C4.5) — verify has an AST-loop→warm-BMC path
   (straight-line + nested `if`) that agrees with the unroll route.
   - **C5 fragment-widening (DONE, ongoing)** — the `#[verify]` surface now covers
     real Rust idioms beyond the C4 core, each soundness-fuzzed against a std
     oracle: `match`-on-int desugared to a right-folded `if`/`else` chain
     (`4552857`, dispatch fuzz `575ce25`); `wrapping_{add,sub,mul}` (modular, no
     overflow class — `cb9790e`); `saturating_{add,sub,mul}` (signed+unsigned
     clamp via `ite` over the overflow predicate — `89ca038`); `min`/`max`
     (signedness-correct select — `6e01b2e`); `abs` (with its `iN::MIN` overflow);
     `checked_{add,sub,mul}` Option flow — `.unwrap()`/`.expect()`, `.unwrap_or(d)`,
     and `match … { Some(v) => .., None => .. }` via a new boolean `Expr::Overflows`;
     `pow(N)` for a constant exponent (folded to checked `Mul`s); and
     `rotate_left/right` by a constant (`Expr::Rotate` → the IR's constant rotate).
     `rotate_left/right` by a constant; and **first-class (let-bound) `Option`
     values** — `let x = a.checked_add(b);` expanded at use sites
     (`unwrap`/`unwrap_or`/`is_some`/`is_none`/`match`), a scoped virtual binding
     with sound fallback-to-error. Also fixed a latent literal-coercion gap in the
     bare `name = <lit>` assignment path. *Next C5 candidates:* `Option` *returned*
     from a fn (rarer); `count_ones`/`leading_zeros`/symbolic-amount rotate need
     core IR (filed as **U9**).
5. **MIR consumer** — a `stable-mir-json` front-end behind the same lowering core;
   demo verifying one real `axeyum-bv` leaf fn (the self-hosting PoC).
6. **vs-Kani scoreboard** once Kani is installable (DISAGREE=0 + cert-coverage).

*Cross-cutting:*
7. **Lean-cert coverage** rises for free as upstream U1/U4 widen the
   reconstructable fragment; add more in-fragment safe examples to each app's
   metric set as it does. *Progress:* the verify scoreboard now reports Lean-cert
   coverage (2/3); EVM Lean coverage is pending a small core accessor on
   `EvidenceReport` (deferred — core territory).
8. **Port the per-app `PLAN.md`/`STATUS.md`** for `evm`/`verify` from the
   `consumer-track` worktree into `docs/consumer-track/{evm,verify}/` on `main`
   (docs-only) so each app's detailed plan lives beside its scoreboard.
9. **Soundness fuzzing (DISAGREE=0 hardening)** — adversarial differential fuzzes
   with an independent concrete oracle. *Done:* EVM fuzz (random bytecode +
   calldata; concrete REVERT/INVALID ⟹ never `SafeUpToBound`; single-tx +
   multi-tx + totality; pool covers arith/mem/storage/env/call) — **found and
   fixed a real wrong-safe** (bad jump destination treated as a safe path end,
   `b1cd4a2`); verify fuzz (random `a op b`; reachable panic ⟹ never `Verified`).
   *Next:* extend to signed arithmetic + the verify array/index fragment; a
   shrinking pass on any future fuzz failure.

**Coordination.** `main` is clean and compiling at takeover; the solver agent
actively rewrites STATUS.md's *Current focus*, so consumer-integration status
lives in its **own** STATUS.md section (no line collision). All changes are
**new-crate-only + an additive root `Cargo.toml` member line** — zero conflict
with their IR/solver edits. Build/test via `scripts/mem-run.sh` (64 GB cap).

## The gap to Z3/cvc5, itemized (2026-06-22; amended 2026-06-23; re-audited 2026-07-07)

> **2026-07-07 re-audit — read
> [gap-analysis-z3-cvc5-2026-07-07.md](docs/plan/gap-analysis-z3-cvc5-2026-07-07.md)
> first; it supersedes this section's priority ordering.** Three framing
> corrections were verified in code: (1) "still eager Ackermann" is stale — the
> online Nelson–Oppen CDCL(T) route (`cdclt.rs` 1-UIP driver,
> `combined_theory.rs` interface propagation) is now *first* in `check_auto`
> with eager Ackermann the fallback; the gap is spine *migration + default-on*,
> not existence. (2) "no inprocessing" is stale — subsumption/BVE/vivification
> exist in `axeyum-cnf` but are **default-off** (`cnf_inprocessing`/`cnf_vivify`
> in `backend.rs`), so Gap-1's first step is a measurement, not a build.
> (3) The quantifier hole is precisely the **sat direction**: e-matching + MBQI
> refutation exist (`qinst_egraph.rs`, `auto.rs`), but outside finite domains
> only `unsat` is reachable — no MBQI model-finding (T2.6.5), which is why
> quantified LIA/UF rows measure 0%. The 2026-07-07 leverage order is at the
> end of this section.

A grounded audit against `crates/axeyum-solver/src/capabilities.rs` (the golden
capability ledger) corrected the framing: **the gap is not breadth — it is depth,
maturity, and (formerly) ~3 missing engines.** axeyum already has *columns* for QF_BV,
QF_ABV, QF_UF, QF_LRA, QF_LIA, UFLIA/UFLRA, QF_NRA/NIA, QF_FP, datatypes,
quantifiers (finite + e-matching + MBQI), strings, optimization, incremental,
symbolic execution, BMC, and k-induction. The 2026-06-27 Track-4 slice also
closes the immediate symbolic-memory/keccak-as-UF branch-query gap:
`IncrementalBvSolver` scopes deferred array/UF assertions, `check_with_memory`
and `check_assuming_with_memory` dispatch them through the full pure-Rust solver,
`SymbolicExecutor` exposes memory-aware assume/branch/status/model calls,
auto-routes `branch` and CFG branch/assume/status/model queries to that path
when arrays or UFs appear, and now keeps a narrow read-over-write slice warm:
same-index store/read-back constraints collapse to the stored value, and
literal-distinct concrete-address store misses skip the unrelated store to
expose inner read-backs; reads from constant arrays collapse to the default
value, covering zero-initialized toy-memory loads before any symbolic write; and
reads over array-valued `ite`s distribute to scalar branch reads, covering simple
state-merged memories when both selected branches reduce through that slice.
Symbolic-address read-over-write now expands to a scalar conditional
(`select(store(a, i, v), j) -> ite(i = j, v, select(a, j))`) and stays warm when
the remaining base read reduces away, covering symbolic hits/misses over
zero-initialized or otherwise reducible store chains.
Plain `select(a, i)` reads over BV-index/BV-element array symbols now abstract to
retained warm BV variables with scoped same-array select-congruence lemmas and
replay-projected array models, so symbolic-base helper loads and ROW tails whose
base read is a memory symbol no longer need the dispatcher. Direct equality
between supported array symbols is also retained as a scoped warm theory fact:
equal-array classes generate cross-array select-congruence lemmas for committed
assertions and one-shot branch assumptions, and SAT models merge equal arrays
before replay. Scalar Bool/BV
uninterpreted-function applications now get the same retained warm treatment:
`f(args)` is abstracted to an internal warm variable, same-function applications
receive scoped congruence lemmas, and SAT models project touched `FuncValue`
points before replay. Assertions and one-shot branch assumptions encode the
simplified/abstracted BV term while retaining the original memory/UF term for
replay and core reporting.
`SymbolicMemory` also provides a typed frontend
helper for array-backed `load`/`store`, load-equality branch/assume queries, and
conservative write-log normalization that drops shadowed same-index writes before
emitting compact read-over-write `ite` chains. Read-specific write-log loads now
skip writes at literal-distinct addresses and elide exact-hit guards while still
guarding later symbolic aliases; those helper branch/assume calls use the same
automatic warm/memory route, so reducible helper queries avoid the dispatcher
while unreduced memory still falls back soundly.
`explore_cfg` now owns the DFS solver mechanics for frontend-supplied CFG states:
branch feasibility, scope push/pop, infeasible pruning, unknown-safe traversal,
and replay-checked target models; with the default `memory_aware=false` it now
uses the same automatic warm/memory route as direct executor calls, so reducible
or select-abstractable CFG memory branches stay warm before falling back. This
is still a one-shot fallback for deferred theories beyond the narrow same-index /
literal-distinct / const-array / array-`ite` / reducible conditional-ROW /
BV-array select-congruence / direct array-equality / scalar-UF congruence
admission, not final warm lazy theory incrementality or a complete
lifter/emulator frontend. The
checked concrete replay hook now has a reusable tiny-target library surface:
`TinyBvProgram` validates a fixed-width BV register program, lifts instructions
to symbolic CFG steps, extracts model witnesses, and independently replays them
in a concrete emulator. It also exposes bounded program-counter reachability and
safety wrappers: reachable PCs carry concrete-replayed witnesses, and
unreachable/safe is reported only after exhaustive bounded exploration with no
unknowns, witness gaps, mismatches, or truncation. The same tiny target now has
`Load`/`Store` instructions over a zero-initialized SMT array memory, with
concrete replay using the same zero-default map and memory-bearing paths routed
through the memory-aware solver path. Concrete replay now also returns a
machine-usable trace: executed PCs/instructions, register snapshots, final
registers, final explicit memory cells, and terminal outcome.
`TinyBvProgram::from_assembly` gives that toy target a small imported text
format (`const`, arithmetic, `load`/`store`, `beq`, `win`/`lose`) with labels for
branch targets, register-vs-register equality branches (`beq rA rB ...`),
line-numbered parse errors, a public label-to-PC map, a public PC-to-source-line
map for imported instructions, deterministic PC-to-label lookup, typed static
CFG edges via `successors` / `cfg_edges`, source/label-aware basic blocks via
`basic_blocks`, deterministic Graphviz DOT export for the basic-block CFG via
`cfg_dot`, trace-highlighted DOT overlays via `cfg_dot_with_trace`,
block-coverage-highlighted DOT overlays via `cfg_dot_with_coverage`,
edge-coverage-highlighted DOT overlays via `cfg_dot_with_edge_coverage`, block
lookup and compressed block trace paths via `basic_block_containing_pc` /
`trace_basic_blocks`, taken CFG edge reports via `trace_cfg_edges`,
source-aware concrete trace rows via `trace_source_steps`, a consolidated
witness replay report via `trace_report`, replay-checked test-case generation
reports via `test_cases_for_pc_checked` / `test_cases_for_label_checked`, and
block-coverage test-suite reports via `test_cases_for_basic_blocks_checked`,
edge-coverage test-suite reports via `test_cases_for_cfg_edges_checked`, and
label-based reachability/safety query wrappers over the existing checked PC
queries. P4.2 still needs richer byte-level/binary frontend work,
unbounded/certified safety, and eventual warm lazy theory reuse.

> **Reframe (2026-06-22; amended 2026-06-23).** With interpolation done and CHC/abduction opened (item 3
> below) and the NRA CAD decision side complete, the three categorically-missing
> engines are now *addressed*. So the dominant gap is no longer "what can't we
> decide." It is **(A) architecture maturity** — chiefly *online* multi-theory
> combination, still eager Ackermann today (the e-graph keystone and the EUF lazy
> DPLL(T) loop already exist; cross-theory propagation does not) — and **(B) the
> certify-gap**: fragments that now *decide* but cannot yet *prove* their `unsat`
> (NRA CAD, NIA). The honest one-liner: **the gap is now "can we certify and explain
> at the same assurance," not "can we decide."** Leverage order is at the end of this
> section.

The honest gap is three things, in size order:

**1. Depth / completeness on a mostly-complete grid** — most fragments are
`validated`/`sound-incomplete`/`experimental` where Z3 is complete-and-tuned. The
depth ladders are already planned; this audit only sharpens their exit criteria:
- NRA: linear abstraction + McCormick → **nlsat/CAD** — [P2.5](docs/plan/track-2-theories/P2.5-nra-cad.md)
  (active; as of 2026-06-22 the **CAD decision side is complete** — N-var algebraic
  critical-point lifting — and the fuzz-measured QF_NRA Unknown rate fell 109→64,
  QF_NIA 498→146, QF_UFLIA 311→18; remaining = proof/Lean evidence for the new
  unsats. Five standing Z3 differential gates clean).
- LIA: **bounded** bit-blast/B&B → **unbounded-complete** (Omega/Cooper backstop) — [P2.4 T2.4.8](docs/plan/track-2-theories/P2.4-lia-cuts.md) (added).
- Strings: bounded BV-lowered → **unbounded** decision procedure — [P2.7](docs/plan/track-2-theories/P2.7-strings.md).
- Quantifiers: maturity of e-matching/MBQI — [P2.6](docs/plan/track-2-theories/P2.6-quantifiers.md).

**2. Architecture / performance maturity** — the *highest-leverage* axis now:
- **Online multi-theory combination has moved from gap to first production route**
  ([P1.6](docs/plan/track-1-engine/README.md)). Online LRA/LIA theory solvers and
  online UFLRA/UFLIA Nelson-Oppen-style combination are now the default
  `check_auto` route for mixed UF+arithmetic, with eager Ackermann as fallback.
  The remaining Z3-class gap is **quality of the spine**: theory propagation,
  lazy antecedents, 1-UIP theory-clause learning, relevance filtering, then moving
  lazy arrays/BV/datatypes/quantifiers onto it.
- **SAT core: BVE + vivification have landed** (bounded variable elimination /
  subsumption / compaction in the SAT-BV path; `axeyum-cnf::vivify` with DRAT
  accounting). Remaining levers: wire/measure vivification in the SAT-BV pipeline,
  glue/LBD retention, SCC/equiv-lit substitution, probing, and word-level BV
  abstraction. The hard-QF_BV tail (~9 instances) remains mostly search-bound.

**3. ~3 categorically-absent engines** — **ALL THREE now addressed (2026-06-22),
each verify-guarded (untrusted search, trusted small checking); depth/fuller
versions remain:**
- **CHC / Horn (PDR/Spacer)** — *unbounded* invariant discovery, the step beyond
  today's bounded BMC + inductive k-induction. The single biggest categorical hole
  vs Z3. [P4.6](docs/plan/track-4-usecases-frontend/P4.6-chc-horn.md). **OPENED
  (ADR-0048):** verify-guarded single-predicate **IC3/PDR over QF_BV**
  (`prove_safety_pdr`) discovers invariants where k-induction is inconclusive —
  `Safe` only when the discovered invariant passes the 3 implication checks; **MBP
  for LRA** (P2.6-T2.6.6) **landed** as the Spacer predecessor primitive; an **IMC**
  (interpolation-based model checking) consumer of the interpolation API is the next
  slice. Depth: LRA-theory PDR, online LRA solver, multi-predicate Horn core.
- **Craig interpolation** — a feature column *and* CHC's lemma engine; read off
  the already-checked proof. [P3.8](docs/plan/track-3-proof-lean/P3.8-interpolation.md)
  **ENGINE DONE (2026-06-22, ADR-0047):** interpolants land for conjunctive
  **QF_LRA** (Farkas), **QF_UF** (congruence-explanation), **propositional/SAT**
  (McMillan over the LRAT resolution proof), **QF_BV** (joint bit-blast + lifted
  propositional interpolant), and **QF_UFLRA** (Ackermannize → LRA interpolant →
  translate) — every phase-exit fragment, each **verify-before-return** (declines
  rather than emitting anything unverified). Only the SMT-LIB `(get-interpolant)`
  parse surface remains (coordinate `axeyum-smtlib`).
- **Synthesis / abduction (SyGuS, `get-abduct`)** — turns the checker into a
  generator. [P4.7](docs/plan/track-4-usecases-frontend/P4.7-synthesis.md).
  **OPENED (ADR-0049):** `abduct(axioms, conjecture)` — bounded enumeration of
  shared-vocab atoms, each candidate returned only when `check_auto` confirms
  consistency + sufficiency + vocabulary. Depth: SyGuS grammar synthesizing *new*
  atoms, CEGIS, minimality, `(get-abduct)` surface.
- Plus the enumerated **breadth tail** (sequences, sets/bags, separation logic,
  finite fields, co-datatypes, rec-fun) kept *counted*, not forgotten:
  [P2.10](docs/plan/track-2-theories/P2.10-breadth-backlog.md).

**Where axeyum is already ahead:** self-checking evidence (DRAT + Alethe + an
in-tree Lean-grade kernel + universal model replay) — ahead of Z3, competitive
with cvc5. That is the moat and it exists today; the plan's job is to keep
*widening* it (Track 3) while closing depth (Track 2) and adding the three engines.

**Next, in leverage order (2026-07-07)** — full rationale in the
[current gap analysis](docs/plan/gap-analysis-z3-cvc5-2026-07-07.md); every
step gated on a scoreboard re-measure (decide% moves, DISAGREE stays 0, Lean
coverage never regresses):

1. **Measure the built perf levers** (Gap 1): enable
   `cnf_inprocessing`/`cnf_vivify` + the T1.2 reduction passes on the
   committed p4dfa pulse, re-run PAR-2, split every `unknown` by cause
   (`EncodingBudget`/`SearchBound`/`LargeCnf`/timeout), compare
   post-reduction CNF size vs Z3. Flag-flip + measurement before any new
   engine code; the outcome decides encoding-vs-search for the next dollar.
2. **Open the quantified sat direction** (Gap 2): MBQI model-finding for the
   almost-uninterpreted fragment
   ([P2.6 T2.6.5](docs/plan/track-2-theories/P2.6-quantifiers.md)) — the
   refutation side exists; sat is structurally unreachable today (quantified
   LIA/UF rows at 0%). MAM/trigger-inference (T2.6.1/2) follow as throughput.
3. **Bank the CDCL(T) spine** (Gap 3): the default-dispatch ADR for the
   built-but-opt-in `CdclT` routes, then port arrays-lazy
   ([P2.2](docs/plan/track-2-theories/P2.2-arrays-lazy.md)) onto it — the
   measured combination tail (QF_AUFBV/AUFLIA, `bug337`/`bug330`) lives here.
4. **Strings unsupported-fragment machinery** (Gap 4): QF_SLIA (36%) first;
   census-ranked to_int/replace_re/seq.* + the sliced concat-unsat follow-ups
   ([P2.7](docs/plan/track-2-theories/P2.7-strings.md)).
5. **Dominance denominator** (Gap 7): `audit_dominance` over the 12 unaudited
   rows; trusted-reduction ledger → 0 (Fpa2Bv is the load-bearing hole).
6. **NIA residue, then the funded ADR-0058 NRA arc** (Gap 5) — honest
   `unknown` is acceptable parity on the CAD frontier; last by design.

*(Superseded 2026-06-23 order, kept for history:)*
1. **Make online combination a real CDCL(T) spine** ([P1.6](docs/plan/track-1-engine/README.md)):
   theory propagation, lazy antecedents, 1-UIP theory learning, relevance, then
   lazy arrays/BV ([P2.2](docs/plan/track-2-theories/P2.2-arrays-lazy.md)/[P2.1](docs/plan/track-2-theories/P2.1-bv-lazy.md)).
   **LANDING (2026-06-23):** theory propagation (LRA/LIA), **1-UIP theory-conflict
   learning + non-chronological backjump** (LRA/LIA/EUF), and a warm combined-theory
   oracle with combined propagation (UFLRA/UFLIA) are in. Remaining spine quality:
   relevance filtering, then moving lazy arrays/BV/datatypes/quantifiers onto it.
2. **Certify what already decides** — Lean/Alethe evidence for NRA CAD and NIA
   `unsat` ([P2.5](docs/plan/track-2-theories/P2.5-nra-cad.md)/[Track 3](docs/plan/track-3-proof-lean/README.md)).
   Attacks the certify-gap head-on and widens the unique moat. **LANDING:**
   interpolants promoted **Validated→Checked** (LRA/EUF/LIA/UFLRA/UFLIA/QF_BV), and
   Lean reconstruction extended (more QF_LIA shapes, disjunctive QF_LRA, QF_ABV ROW
   Carcara-checked). Remaining: NRA CAD / general NIA `unsat` certificates.
3. **Measure** the levers as they land — this is the [measurement-debt](#true-parity-the-maturity-ladder-and-the-measurement-debt-2026-06-23)
   payoff. **SAT vivification is now wired into the SAT-BV pipeline** (gated by
   `cnf_vivify`, default off) **and exposed to the harness** (`axeyum-bench --vivify`),
   so its QF_BV effect is now measurable; word-level BV abstraction is next.
   **Quantifier maturity** ([P2.6](docs/plan/track-2-theories/P2.6-quantifiers.md);
   MBQI is now MBP-driven).
4. **Deepen the seeded engines** behind a stable API — CHC/PDR ([P4.6](docs/plan/track-4-usecases-frontend/P4.6-chc-horn.md))
   and the `(get-interpolant)`/`(get-abduct)` SMT-LIB surfaces — then the breadth tail.

## True parity: the maturity ladder and the measurement debt (2026-06-23)

A sober big-picture check, because the ledger now reads as "we have almost
everything Z3/cvc5 have." That is true **at the seed level** and misleading as a
parity claim: **a sound, verify-guarded first slice of an engine is not parity
with a 15-to-20-year production engine.** Every capability climbs a ladder, and
naming the rung honestly is the difference between a real roadmap and a feature
checklist:

| Rung | Meaning | Where axeyum mostly is |
|---|---|---|
| **Seeded** | sound, verify-guarded first slice (often conjunctive / bounded / single-predicate) | **most newer engines** — CHC/PDR, abduction, interpolation, online combination |
| **Decides** | complete on the decidable fragment; honest `unknown` outside | QF_BV, QF_UF, QF_LRA; NRA CAD decision side |
| **Measured-competitive** | solved-count + PAR-2 within target of Z3/cvc5 on a *committed* corpus, same hardware/timeout | **QF_BV only** (p4dfa 113, parity, both hard-capped) |
| **Certifying** | every `unsat` carries a Lean-checkable certificate | QF_BV (DRAT), QF_LRA (Farkas), QF_UF, degree-2 SOS — **ahead of Z3** |
| **Production** | tuned, scalable, robust across the division's *full* benchmark suite | **none yet** — Z3/cvc5 are here across all divisions |

**The honest position:** axeyum has **breadth of seeds + a leading *certifying*
story + one measured division.** It is *not* at Z3/cvc5 parity, and the distance
is dominated by two things the ledger does not show — **production depth** (the
bulk of Z3's ~688k LoC) and **measurement debt** (only QF_BV is measured; every
other "parity" is a feature-ledger assertion, not a number).

**The phase pivot.** Breadth acquisition is essentially done — the ledger has a
seed for nearly everything. **The standing rule now inverts: stop adding new engine
seeds; deepen, *measure*, and certify the ones that exist.** A new seed without a
measured corpus behind it adds claim-surface, not parity.

**What true parity actually requires — and the realistic bet:**
1. **Measured per-division corpora vs Z3/cvc5 — the #1 credibility item.** Today
   [P4.5](docs/plan/track-4-usecases-frontend/P4.5-benchmarking.md) measures QF_BV
   alone. Parity is a *number per division* (QF_LRA, QF_LIA, QF_UF, QF_UFLIA,
   QF_ABV, QF_NIA, QF_NRA, QF_S), not a ledger row. **Gate every "parity" claim on a
   committed measured slice; until a division has one, its status is
   "seeded/decides," never "parity."**
2. **Do not race Z3 to production depth on every division** — that is a 15-year
   loss. **Pick the divisions where axeyum can be both measured-competitive *and*
   fully-certifying** — QF_BV, QF_LRA, QF_UF, QF_LIA, QF_ABV — and drive those to the
   top of the ladder. "Fast-enough **and** every `unsat` carries a Lean-checkable
   proof" is a position **neither Z3 nor cvc5 occupies**; that is the winnable parity.
3. **Accept sound-incompleteness on the hard frontiers** (NRA, strings, full
   quantifiers, large-scale CHC) as the honest steady state — match Z3's *practical*
   heuristics where cheap, return first-class `unknown` otherwise, and let
   **certification, not raw decide-rate, be the differentiator.**

In one line: **true parity is measured-and-certified on a chosen set of divisions —
not a feature checklist — and the next phase is depth + evidence, not more seeds.**

## How to use this plan each session

1. Read **[STATUS.md](STATUS.md)** — it names the current focus and the next
   task.
2. Open that task's phase file under `docs/plan/track-*/`. Each task lists its
   goal, the reference file paths to read, its size, and its exit criteria.
3. Do the task as a sound, tested, committed increment (the project's normal
   discipline: `just check`, model replay / independent re-check, ADR if it's a
   new public surface or decision).
4. Update STATUS.md (the phase row + changelog). Keep the capability ledger
   (`crates/axeyum-solver/src/capabilities.rs`) and its golden matrix in sync.

## Standing rules (do not violate)

- Default build is **pure Rust, no C/C++**; native/feature-gated leaves only.
- `unsafe_code` is denied workspace-wide; exceptions need an ADR.
- `unknown` is a first-class result; never a wrong `sat`/`unsat`.
- **Graceful `unknown`, never OOM/crash.** Every solving path must degrade to
  `Unknown` under a *deterministic* resource bound — no unbounded memory/time on
  adversarial input. Precedent: sat_bv's pre-lowering oversized-encoding refusal;
  NRA's `MAX_CROSS_PRODUCTS` admission bound (2026-06-19, refuses ≥3 distinct-operand
  cross-products before building lemmas — bounded *or* unbounded, since the blowup is
  inside a single LRA solve call that the wall-clock checks can't intercept). Add a
  bound before adding a feature that can blow up.
- Every `sat` replay-checks; every new `unsat` route gets an independent checker
  or an explicit, ledgered trust note.
- **Build caps:** use `CARGO_BUILD_JOBS=1` and `--jobs 1` for every Rust
  build/test/bench on this host. On 2026-07-20, a nominal 4 GiB cgroup still
  OOM-killed `rust-lld` because one invocation fanned out into many concurrent
  compilers/linkers. Run Rust work in a user cgroup with aggregate
  `MemoryMax=4G`, `MemorySwapMax=512M`, and `OOMScoreAdjust=200`; disable test/dev
  debug metadata for large gates and record the service memory peak. The
  per-process `scripts/mem-run.sh`/`ulimit` guard is supplementary, not a
  substitute for the aggregate cgroup. Never use Cargo's host-default
  parallelism here.
- **Coordination (multi-agent):** a second agent works `axeyum-rewrite` /
  `axeyum-smtlib` (word-level reduction, P1.2 — the destination-2 near-term lever).
  Treat those crates as theirs; this agent covers measurement, proof/Lean
  (Track 3), breadth/feature-parity (Track 2), and incremental SAT-core
  modernization. Do not edit `canonical.rs` etc. without coordinating.
- **Do not sweep the 41GB public corpus** to "make progress." Measure once on a
  committed slice, then stop.
- Decisions are recorded as ADRs in `docs/research/09-decisions/`.
- Commit trailer:
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.

## Provenance

The plan was synthesized from a top-down review of the cloned reference solvers
in `references/` (Z3 ~688k LoC, cvc5 ~512k, bitwuzla, CaDiCaL, Kissat, Carcara,
lean4, nanoda_lib, lean-smt, drat-trim) by five parallel Opus sub-agents on
2026-06-15; their full reports are in
[`docs/plan/references/`](docs/plan/references/README.md). axeyum today (2026-06-22)
is **~143k LoC of Rust across 14 crates** with a broad, evidence-backed
decidable+arithmetic foundation (destination 1) — including a complete CAD
decision side for NRA, a competitive pure-Rust proof-emitting SAT core, and
self-checking evidence (DRAT + Alethe + an in-tree Lean-grade kernel + universal
model replay) that already leads Z3. This plan is the route to destinations 2
(Z3-class performance) and 3 (Lean-checkable proofs). Live per-session state is in
[STATUS.md](STATUS.md); the foundation phase history is in the research
[roadmap](docs/research/08-planning/roadmap.md).
