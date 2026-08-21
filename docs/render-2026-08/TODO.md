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
- [ ] INTEGRATE — wire HTML emitter + producers through assembly; run
        the eight P0 exit criteria from 04-prototype-plan.md; mutation
        pass; produce certificate.{md,tex,html} + facts.{md,html}.
- [ ] REVIEW — coordinator: exit-criteria audit, reader test with owner,
        commit, status note.

## Standing constraints (all agents)
Rust+Python only; outputs md/LaTeX/self-contained HTML (+optional wasm);
NO Node anywhere; real artifacts only — no synthetic evidence; fail-closed
law from 01; ASCII; bounded compute; shared checkout — never run git
mutations; WebSearch budget is EXHAUSTED — use SerpAPI via
`curl "https://serpapi.com/search.json?engine=google&q=...&api_key=$SERPAPI_API_KEY"`
(key is in the environment) and WebFetch for URLs.
