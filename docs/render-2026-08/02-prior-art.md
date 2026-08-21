# 02 -- Prior art survey (SerpAPI, 2026-08-21)

What exists, what to steal, what is missing. Links verified by search on
2026-08-21; fetch before depending on any detail.

## System-rendering (traces)

- **Alectryon** (github.com/cpitclaudel/alectryon; systemf.epfl.ch/blog/alectryon).
  Coq/Rocq + Lean snippets in prose; the PROVER emits per-sentence output
  captured into the document; HTML lets the reader toggle each step.
  STEAL: the producer-emits-document-data architecture; per-step foldable
  IO capture; the insight that prose is woven AROUND machine truth, never
  the reverse.
- **Isabelle document preparation** (isabelle.in.tum.de, Isar_Ref
  Document_Preparation). Theories -> LaTeX; tagged regions with
  keep/drop/FOLD semantics; ANTIQUOTATIONS = checked references into the
  formal content that fail the build when dangling.
  STEAL: the verbosity tag semantics verbatim; antiquotation-style checked
  references as the citation mechanism for formal objects.
- **Wolfram computational essays / Pluto.jl** (writings.stephenwolfram.com,
  plutojl.org). CAS-side narrative aesthetics; Pluto's reactivity.
  STEAL: the essay pacing; replace reactivity with per-block
  regenerate-command + input hashes (honest static equivalent).
- **SMT/SAT proof rendering: THE GAP.** Formats exist (Alethe-style,
  ceur-ws.org/Vol-3185/paper9527.pdf; comprehensive cvc5 proofs, Springer
  978-3-032-32526-6_9; DRAT/LRAT), reconstruction exists -- beautiful
  READER-FACING rendering of solver evidence essentially does not.
  Axeyum can own this: certificate boxes, UNSAT-core narratives,
  proof-skeleton statistics, replay affordances.

## Result-rendering (papers, atlases)

- **leanblueprint** (github.com/PatrickMassot/leanblueprint; PFR tour on
  terrytao.wordpress.com 2023-11-18). LaTeX statements anchored to formal
  objects; per-statement status coloring; auto-generated interactive
  dependency graph; links into doc-gen4.
  STEAL: the status-colored dependency graph as atlas navigation; the
  informal<->formal anchoring. LIMIT: Lean-only, binary-ish statuses --
  our epistemic vocabulary is richer, and our objects span CAS + solver +
  kernel.
- **Verso** (github.com/leanprover/verso). Documents as code; one document
  representation, multiple GENRES (manual/paper/blog); typed
  cross-references.
  STEAL: the genre architecture -- R1 and R2 are genres over one IR.
- **sTeX3 / OMDoc / MMT** (kwarc.info cicm22stexsd.pdf; omdoc.org).
  Semantic LaTeX -> PDF and HTML from one source; the academic lineage of
  document IRs for mathematics. CITE; do not adopt (heavy, XML-era).
- **MyST Markdown / Curvenote** (mystmd.org; scipy proceedings NKVC9349),
  **Quarto** (quarto.org). Markdown-first scientific publishing, md ->
  HTML + LaTeX, rich cross-refs.
  DECISION DEFERRED (see 03): emitting MyST-flavored MD could buy a free
  HTML skeleton, but MyST's own HTML build is a Node toolchain -- which
  violates our constraint if we depend on it. Default plan: plain
  CommonMark + `<details>`, own HTML emitter.
- **Distill** (distill.pub). The visual bar for interactive articles.
  STEAL: restraint -- interactivity only where it explains.

## The distinctive position

Nothing surveyed spans CAS + SAT/SMT + kernel with fail-closed claim
rendering. leanblueprint is the nearest relative and is Lean-specific.
An "evidence atlas" whose every badge is backed by an exit status -- and
whose HTML can RE-VERIFY certificates in-browser via WASM (05) -- has no
peer. That is the academic-awareness artifact.
