# Render strand P0 task board

Coordinator: Claude (Fable 5), opened 2026-08-21. Agents never commit;
the coordinator commits via the private-index procedure.

## Round 1 (parallel, disjoint ownership)
- [ ] CORE  — render/ package: Doc-IR (src/ir.rs), docir.schema.json,
        scripts/validate-docir.py, assembly resolver (fail-closed),
        Markdown + LaTeX emitters, golden + negative tests, check.sh.
        Owns: render/src/{ir,assemble,emit_md,emit_tex,main}.rs,
        render/tests/, render/check.sh, artifacts/ontology/docir.schema.json,
        scripts/validate-docir.py.
- [ ] DESIGN — R-a (pure-Rust DAG layout) + R-b (MathML decision note) +
        the HTML experience: style system, SVG layout module, HTML
        emitter built against the schema AS DATA (hand-written sample IR
        until integration). Owns: render/src/{emit_html,layout}.rs,
        render/assets/, docs/render-2026-08/07-r-notes.md.
- [ ] CERT — P0-A producer: patched noh_wt_certificate with --emit-run,
        real run record JSON, the certificate-page manifest (prose,
        claims, steps, d(k) table, weight-step SVG data). Owns:
        render/producers/, render/examples-input/cert/.
- [ ] FACTS — P0-B producer in Python: artifacts/facts/*.json ->
        per-fact Doc-IR documents + atlas index document with DepGraph
        figure spec. Owns: render/producers-py/, render/examples-input/facts/.

## Round 2 (after round 1 lands)
- [x] INTEGRATE -- HTML emitter wired through assembly (every figure in every
        assembled document was an "unknown figure kind" box until it was);
        the eight P0 exit criteria run one by one, 7 PASS + 1 ADJUSTED, in
        docs/render-2026-08/14-p0-exit-report.md; mutation pass re-measured
        (CORE's kill table holds; two previously-untested rule-4 carriers and
        one inert gate step found and fixed); RunRecord.role landed across
        schema + IR + assembly + the Python validator; the d(k) table is now
        from_run, not transcribed; the atlas ships per-component graphs;
        deliverables in render/out/ (10 files, 1.1 MB, byte-reproducible).
        Diary: docs/render-2026-08/15-integrate-diary.md.
- [ ] REVIEW -- coordinator: read 14-p0-exit-report.md, run the READER TEST
        with the owner on render/out/certificate.html (the one criterion no
        agent can close), commit, status note. P1 queue is the last section
        of 15-integrate-diary.md.

## Round 3 (P1)
- [x] P1-ADR -- ADR-0509 (proposed): Doc-IR + RunRecord + the kernel inventory
        snapshot become public evidence formats (semantics/replay/checker per
        Hard Rules); render/ promotes to axeyum-render on named triggers, not
        yet; no-Node + self-containment and the fail-closed law (assembly
        REFUSES, an emitter REPORTS) become repo-level. Index regenerated.
        Plus the third producer family: render/producers-kernel/ ->
        render/examples-input/kernel/ (3 documents, 5 run records, 2 inventory
        snapshots; 139 Nat + 57 Int statement blocks, the first corpus use of
        FormalRef::Kernel). Diary: docs/render-2026-08/19-adr-kernel-diary.md.
        Owns: docs/research/09-decisions/adr-0509-*, the regenerated ADR index,
        render/producers-kernel/, render/examples-input/kernel/, 19-*.md.

- [x] P1-RUNREC -- ran the fact ledger's own checkers and recorded them: 19
        facts (arith pilot + both Rado headlines), 38 evidence rows, 22 distinct
        commands, 22 green / 0 red / 0 skipped, 1m13s total; 22 production run
        records + 1 negative control in render/examples-input/runrec/, all 23
        valid, plus runrec-index.json mapping (fact, row) -> record. Fact cards
        can now carry Claim blocks -- bridge spec + the four assembly guards
        measured through the real binary in 18-runrec-diary.md. Ledger findings
        for the coordinator: no evidence row in the ledger carries an artifact
        digest (0 of 200, 104 name a file); 13 of 17 kernel-term rows check the
        theorem NAME not its type (negative control shows the checker exits 0
        on a falsified type); F:rado-r4-a5-b4's row sweeps all 104 claims in
        61s when --only scopes it to 0.84s. Diary:
        docs/render-2026-08/18-runrec-diary.md. Owns:
        render/producers-runrec/, render/examples-input/runrec/, 18-*.md.

- [x] P1-CARDS -- the corpus is a SITE: all 324 fact cards rendered to
        render/out/cards/ (328 pages, 1.3s for the cards, whole build 3.8s,
        byte-reproducible), atlas/pilot dep-graph nodes and index rows are real
        links, every card links back to the atlas and to its component graph and
        to its depends_on/dependents. 2085 relative links, 0 broken, checked
        twice (render/tests/link_integrity.rs + check.sh step 10, both with
        negative controls). All four reader-review gripes fixed. Additive:
        Certificate.no_exit_reason and DocMeta.nav across schema + IR + assembly
        + validate-docir.py; `--manifest-dir` batch mode and `--name-by source`
        in the CLI; build-p0-outputs.sh renamed to build-outputs.sh. check.sh is
        11 steps, 21 passed / 0 failed (was 15/0). Four screenshot-only defects
        fixed (fold alignment, 15x repeated provenance line, sentence cells
        clipped by nowrap, atlas index columns behind a scrollbar). Diary:
        docs/render-2026-08/17-cards-diary.md. Owns: render/ (except
        producers-runrec/, producers-kernel/ and their examples-input dirs),
        17-*.md.

## Standing constraints (all agents)
Rust+Python only; outputs md/LaTeX/self-contained HTML (+optional wasm);
NO Node anywhere; real artifacts only — no synthetic evidence; fail-closed
law from 01; ASCII; bounded compute; shared checkout — never run git
mutations; WebSearch budget is EXHAUSTED — use SerpAPI via
`curl "https://serpapi.com/search.json?engine=google&q=...&api_key=$SERPAPI_API_KEY"`
(key is in the environment) and WebFetch for URLs.
