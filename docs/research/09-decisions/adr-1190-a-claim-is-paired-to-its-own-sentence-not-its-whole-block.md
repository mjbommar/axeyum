# ADR-1190: A claim is paired to its own sentence, not its whole block

Status: accepted
Date: 2026-08-31
Index-summary: `scripts/check-absence-claims.py`'s census budget had been
raised twice (141 -> 249) and was red at 250, because it was tracking NOISE
rather than claims: a claim phrase fired on ONE sentence of a multi-paragraph
block and `DECL_RE` harvested every `Root.name` in the WHOLE block as that
claim's subject. Two independent hand audits rejected the surplus (55 of 70 on
2026-08-27; every one of the remaining 249 on 2026-08-31), and the second
recommended this fix and scoped itself out of it. A claim is now paired with
the names in its own unit — a Markdown table row or list item, then a sentence
within it — while the block stays the unit a marker attaches to, and a marker
only silences a claim whose subject it NAMES. Measured on the real tree: 250
bare -> **122**, worst site 93 candidates -> 8. Verified not a weakening
against all 11 declarations of the 8 known-stale claims, pinned as a fixture
regression. Separately: `check.sh` registered only this checker's UNIT TESTS
and `just check` never named it, so the whole expiry mechanism ran only by
hand — ADR-1170's defect, one registration below ADR-1170's own note. Both
gates run the checker now.
Index-status: accepted

## Context

ADR-0611 made an absence claim expirable: `<!-- absent: Root.name -->` reds the
gate the day that declaration lands. Alongside the marker check it runs a
heuristic **census** of absence-claim prose, budgeting the sites that name a
declaration but carry no marker — "unexpirable claims" — so a new one cannot be
added silently.

That budget had become a noise gauge. It was raised 141 -> 249 on 2026-08-31
after a hand audit, and was red at 250 against 249 the same afternoon.

The cause is the granularity of the association, not the claim phrases. The
checker segmented prose into blank-line blocks, matched a claim phrase anywhere
in a block, and then took **every** `Root.name` in that whole block as the
claim's candidate subjects. In this repository a block is routinely a Markdown
table, a diary entry, or an ADR's landed-declarations list, so most harvested
names are cited as *present* evidence in a neighbouring sentence.

Three sites, none of which is an absence claim about the names attached to it:

- `docs/plan/status/draw-15.md:40` — *"`--concl Nat.countRange` is ABSENT
  despite 21 matching declarations"*, which documents a **tool trap** and says
  the declarations exist.
- `docs/plan/status/gauss-assembly.md:94` — a landed-declarations table row.
- `docs/plan/notes/40-autogenesis-program.md:9` — one archived-rows table,
  contributing a single site with **93** candidates.
<!-- was-absent: Nat.countRange -- quoted stale text, kept under the gate: this ADR reproduces another document's sentence, and if the declaration it names is ever renamed the quotation stops pointing at anything -->


Two independent audits reached the same verdict. The 2026-08-27 `absence-adopt`
lane rejected 55 of 70 as not genuine. The 2026-08-31 `absence-and-orphans`
lane sampled every structural class of the remaining 249 — all 66
single-candidate blocks, every `docs/research/09-decisions/` site, every
line-paired candidate — found **zero** further genuine per-declaration claims,
named the structural fix, and deliberately did not attempt it.

## Decision

**Pair a claim with the names in its own UNIT.** A unit is a record first — a
Markdown table row, or a list item at any indent — and then a sentence within
that record. The **block** remains the unit a marker attaches to, because a
marker is written near the paragraph it corrects, not spliced into the
sentence.

Two boundary rules are load-bearing, and both are derived from claims this gate
has actually caught rather than chosen for tidiness:

- **A sentence ends at `.`/`!`/`?` followed by whitespace — never at `:` or
  `;`.** Requiring the whitespace keeps `nat_prelude.rs:1909`, `Ch.22-23` and a
  bare `Root.name` from splitting a sentence in half. Excluding `:` and `;` is
  not cosmetic: `"(do not exist in the merged tree): CReal.alternatingBracketUpper,
  ..."` names its subjects **after** a colon, and `"neither of which has a
  ready-made Nat.gcd_comm ... (this development has no such lemma; only
  gcd_zero_left, ...)"` names its subject **before** a semicolon. Both are among
  the eight stale claims this gate has caught.
- **Only a line that OPENS a record breaks one.** A wrapped item's continuation
  lines stay with the item they continue — `"- ... since Nat.even_or_odd\n does
  not exist"` puts the subject one line above the phrase.
<!-- was-absent: CReal.alternatingBracketUpper, Nat.gcd_comm, Nat.even_or_odd -- the two bullets above quote the stale text of three corrected claims verbatim; all three declarations exist, and this keeps the quotations under the gate -->


`*` is a list bullet in Markdown and a block-comment continuation in Rust, so it
opens a record only in Markdown.

**A marker only silences a claim whose subject it NAMES.** This is not scope
creep; it is required by the change above. With one site per block, one
`annotated` flag covered the block's single claim. At sentence granularity a
block routinely carries several independent claims, and without this a marker
for X would silence a separate claim about Y. Matching is exact first, then
spelling-normalized — the same two-step `Authority.resolve` uses, and for the
same reason: a marker written `CReal.congr_of_uniformly_continuous` must cover
prose written `CReal.congrOfUniformlyContinuous`.

A claim naming no declaration is no longer "annotated" at all. It is
structurally uncheckable by any authority-derived gate, and calling it covered
was meaningless.

**Register the checker itself in the aggregate gates**, not only its unit tests
(below).

## Measurement

Against a fresh `kernel_declaration_projection` (2,636 distinct declarations,
floor 1,750; the binary verified fresh — no kernel source newer than it, and
`diff -rq` of the kernel sources against the tree reporting zero differences):

| | sites | name a declaration | annotated | **bare** | worst site |
| --- | --- | --- | --- | --- | --- |
| block-granular (before) | 987 | 287 | 37 | **250** | 93 candidates |
| unit-granular (after) | 1,050 | 151 | 29 | **122** | 8 candidates |

Budget lowered **249 -> 122**, by narrowing — not by `--update-budget`, and
not by annotating anything.

Three variants were measured before choosing, all preserving the regression
below: candidates unioned over a block's claim sentences (121 bare, but the
printed line then points at the first claim while the names come from a later
one); one site per claim sentence (121, worst site still 93 — the table);
adding record boundaries (**118**, worst site 8). The name-matching annotation
rule then correctly exposed 4 sites that a marker naming something else had
been covering, which is why the honest figure is 122 rather than 118.

## Verification that this is not a weakening

Narrowing that loses a true positive is a weakening, so the eight genuinely
stale claims the `absence-and-orphans` lane corrected — eleven declarations —
are pinned as a regression. Their **pre-correction** text is cut verbatim out
of `335cb3661^` at the block the checker segments, into
`scripts/tests/fixtures/absence-stale-claims/`, and driven by
`StaleClaimRegression`:

    CReal.uniform_converges_add        docs/plan/status/133-ledger-uc.md
    Nat.even_or_odd                    docs/plan/status/133-ledger-uc.md
    CReal.alternatingBracketUpper      docs/plan/status/133-ledger-uc.md
    CReal.alternatingLowerBound        docs/plan/status/133-ledger-uc.md
    CReal.alternatingUpperBound        docs/plan/status/133-ledger-uc.md
    Nat.ascFactorial, Nat.descFactorial  docs/plan/status/200-nat-factorial.md
    Nat.clog                           docs/plan/status/206-nat-log-tier.md
    Rat.ofInt                          crates/.../complex.rs
    CReal.sqrt                         crates/.../nat_prelude/irrational.rs
    Nat.gcd_comm                       crates/.../int_prelude/gcd.rs

All 11 are still attributed to their claim: **11/11 before, 11/11 after.** The
suite also asserts the fixture corpus is not silently empty (a regression whose
fixtures vanished would pass vacuously) and that seven of the eight go red end
to end at a zero budget — the eighth already carried a `was-absent:` marker at
that commit.

**Break/restore, through the real gate on the real tree.**
`docs/plan/status/206-nat-log-tier.md` was rewritten to its pre-correction
content and restored:

    stale text restored   exit 1   census 1049 sites, 123 bare, budget 122
                                   site 64 annotated=False names=('Nat.clog',)
    restored              exit 0   census 1050 sites, 122 bare

## Controls

Seven mutations added to `scripts/tests/mutation_controls.py`; the suite exits
**0** with 45 baseline tests and every mutation a `killed N` measurement — no
`SURVIVED`, no `NOT MEASURED`:

| mutation | dies |
| --- | --- |
| marker gathering block-wide -> file-wide | the own-block test |
| G21 sentence split removed | the neighbouring-sentence test |
| G22 sentence split extended to `:`/`;` | the colon test **and the 11-declaration regression** |
| G23 record regex made unmatchable | the table-row control |
| G23 every line its own record | the wrapped-item test **and the regression** |
| G24 annotation back to block-wide | the marker-names-its-subject test |
| G24 normalized fallback removed | the two-spellings test |

The two `killed 2` rows are the regression suite doing its job: a boundary rule
that a real stale claim depends on cannot be removed without it noticing.

Each new guard also carries a control in the opposite direction — a name in the
claim's own sentence, in its own table row, on the continuation line of its own
wrapped item, and a marker that *does* name the subject — so the narrowing
cannot be satisfied by a matcher that attributes nothing.

## The gate ran nowhere automatic

Found while checking registration, and it is ADR-1170's defect verbatim, sitting
one registration below ADR-1170's own retrospective in the same file:

    scripts/check.sh:358  step absence-claims-tests python3 -m unittest ...

`check.sh` registered the **unit tests** — which drive synthetic fixtures in a
`TemporaryDirectory` — and never `python3 scripts/check-absence-claims.py`.
`just check` did not name `absence-claims` at all; the recipe's own comment
said it was "deliberately NOT part of `check`" on the cost of the release
projection (~20 s warm).

So the 39 markers in the real tree — the entire expiry mechanism ADR-0611
exists to provide — were checked against the kernel only when a human typed
`just absence-claims`. The suite passes, the step name contains the checker's
name, and the real prose is never examined.

Reversed. Both `scripts/check.sh` and the `just check` recipe now run the
checker, and the justfile comment records the reversal and its reason rather
than being deleted.

## Consequences

- The budget is now a measure of unexpirable claims rather than of matcher
  noise, so lowering it further is annotation work rather than tuning. 122 is
  the honest count on this tree; the next lane to reduce it should annotate.
- The census's site count rises (987 -> 1,050) because a block with several
  independent claims is honestly several sites. Each bare line now points at
  the sentence that makes the claim, which is what makes the remaining 122
  auditable at all.
- **What this does not fix.** The claim phrases are still a heuristic, and 899
  sites name no declaration and remain structurally uncheckable by any
  authority-derived gate — stated in the tool's output on every run rather than
  left to be discovered. A narrower matcher reduces false positives; it cannot
  make a prose heuristic into a decision procedure.
