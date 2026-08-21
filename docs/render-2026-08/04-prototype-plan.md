# 04 -- Prototype plan (P0): smallest end-to-end truth

## Principle

Prototype the whole pipe on ONE producer and ONE result surface before
generalizing: prove the IR by exercising it, not by designing it. The two
P0 consumers are chosen to force both halves of the design (R1 trace
rendering and R2 result rendering) with artifacts that exist today.

## P0-A: certificate page for `noh_wt_certificate` (system genre)

The NoH-p2 weight certificate (axeyum branch agent/noh-p2-axeyum-examples
@ 75663ef8) is self-checking, fail-closed, mutation-tested -- the perfect
first producer.

1. Add `--emit-run out.json` to the example: run record (Provenance +
   summary stats + the claim list it establishes: Theorem 3 bound rows,
   Theorem 4 sharpness witness).           [size: S, pure addition]
2. Hand-write the P0 assembly manifest (JSON): prose blocks + Claim
   blocks referencing the run record + one Steps block (the k=6 self-loop
   derivation) + one Table (d(k) rows) + one Figure (weight step plot as
   generated SVG).                          [S]
3. Implement IR structs + assembly resolver + the three emitters at
   MINIMUM viable block coverage (Prose, Claim, Table, Steps,
   Certificate, Figure-as-inline-SVG).      [M, the core work]
4. Outputs: `certificate.md`, `certificate.tex` (+ compiled PDF),
   `certificate.html` (single file).

## P0-B: fact cards + mini-atlas (result genre)

1. Producer: a reader over `artifacts/facts/F-*.json` (already
   schema-gated) emitting one Doc-IR document per fact + an index
   document with a DepGraph figure over `depends_on`. Pick the ~18
   gf2-lemire facts as the corpus.          [S -- the ledger IS the IR
   for statements; this mostly exercises Statement refs + badges]
2. Emit the atlas as: one `facts.md`, one `facts.html` (index page with
   inline per-card details), skip LaTeX for P0-B.  [S]

## P0 exit criteria (all measurable; strand not "done" until all pass)

- [ ] The three P0-A outputs render from one IR; the (claim,status) set
      is byte-identically equal across formats (property test).
- [ ] LaTeX output compiles standalone; HTML passes the self-containment
      lint (zero external requests; grep-gate for src=/href= against an
      allowlist of `#`, `data:`, `mailto:`).
- [ ] FAIL-CLOSED demonSTRATED, each by a test that dies if its guard is
      deleted: (1) claim without evidence -> build error; (2) run record
      with exit_status=1 -> claim renders REFUTED (and strict mode
      errors); (3) dangling fact ref -> build error; (4) input-hash
      mismatch -> build error.
- [ ] Determinism: two builds byte-identical; `touch`-based mtime attack
      (the repo's known cargo trap) cannot produce a stale render --
      the assembly re-hashes inputs every run.
- [ ] Negative control on the pipeline itself: mutate one d(k) value in
      the run record -> the rendered table changes AND the claim whose
      bound it violates flips to red. (The renderer must propagate
      truth, not decorate it.)
- [ ] A reader test: one person (the owner) reads certificate.html cold
      and can state what was proved, what checked it, and how to replay
      it, without opening the repo.

## Test strategy summary

Golden files per emitter (byte-exact, committed); negative tests per
fail-closed rule (delete-one-guard discipline); the cross-format claim
property; schema round-trip Rust<->Python (serde emit -> python
jsonschema validate -> python re-emit canonical -> byte-equal); HTML
lint; LaTeX compile gate. All wired into a `render/check.sh` that the
aggregate gate can adopt later -- and whose exit status depends on
findings from day one.

## Deliberately deferred past P0

Rewrite-trace Steps capture from axeyum-rewrite (needs producer hooks in
a workspace crate -> after the ADR); solver DRAT certificate pages;
polygon figures with hover; WASM re-verify; MyST interop; the paper
genre (P3, see 06).
