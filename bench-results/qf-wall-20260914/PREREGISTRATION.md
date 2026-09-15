# QF-WALL preregistration

Lane `qf-wall`, 2026-09-14. Branch base: `git merge-base main HEAD` is
`cfcae7fa78bbc8297ccb62d8517895edb87d8c33`, which **is** local `main`'s HEAD.

## What this file is, and what it is not

**This lane's diagnostic phase (steps 1–3 of the brief) ran BEFORE this file
was written, and this file does not pretend otherwise.** Steps 1–3 are a
characterisation: assemble the population, re-derive it, and establish per query
what a successful refutation requires. A characterisation has no arm, no
polarity and no conversion rate, so there is nothing for a preregistration to
protect it from — the instruments are committed with it and every number is
re-derivable from them.

**The rules below govern step 4, the BUILD decision, and they are written before
any lever exists.** That is where preregistration bites: the temptation is to
size a lever after seeing which rows it moved.

## The population

The 13 rows of `lists/population-13.list`, inherited from [ADR-2040] §5 and its
`ref/capability-vs-budget-13.tsv` (11 `CAPABILITY-LIMIT`, 2 `CONVERTED`).

## R — the rules

**R1 — the inherited list is a claim, not the population.** Every row is
re-derived on the current tree before it is counted, and the re-derivation is
reported with its denominator. [ADR-2035] found 8 of 22 censused "declining"
files were decided anyway; an inherited list overstates.

**R2 — the ABSTRACTION is re-derived too, not only the verdict.** The census
that produced these 13 ran `abstract-quantifiers.py` in its default
shared-by-text atom map. That tool's own docstring says the shared map is NOT
unconditionally sound and names `--fresh-per-occurrence` as its control. The
control is run here on every row, and **a row whose shared-map skeleton is
`unsat` but whose fresh-map skeleton is not is INADMISSIBLE** — not a capability
gap but an instrument artefact, reported as such and excluded from every
denominator that follows.

**R3 — every bucket carries its denominator, zeros included; NOT MEASURED is a
separate bucket from zero.** A row whose instrument did not finish is
`DID-NOT-RUN`, never folded into either side.

**R4 — a capability claim must be established by MECHANISM, not by a verdict
count.** Naming a capability means exhibiting two queries that differ on that
axis and nothing else, handed to ONE solver, and showing the verdict moves. A
flag that is silently ignored prints the same number as a flag that is live.

**R5 — every weakening claimed is stated with its direction and checked.** Each
instrument here (quantifier abstraction, purification, propositional
abstraction) is a weakening, so `abstract unsat` entails `concrete unsat` and
the converse is not claimed. Where an instrument could instead STRENGTHEN (the
shared-atom maps), that is called out and controlled (R2).

**R6 — three authorities on any new verdict, with the comparable denominator
printed beside any zero** ([ADR-1957]). `z3 -T:` SECONDS, `cvc5 --tlimit`
MILLISECONDS.

**R7 — Wilson 95 % on every proportion.** With n ≈ 13 the interval is wide and
is quoted rather than hidden.

**R8 — if a lever is built: interleaved per file, ONE binary and two env
values, arms back to back on the same pinned core with the order alternating,
polarity stated in the runner header, 3 passes per arm on every moved row, a
published noise floor from two byte-identical arms, and a control shown
NON-VACUOUS by measuring that the lever's site EXISTS in the control
population.** A control whose lever never fires is reported WEAK, not banked.

**R9 — the build gate.** A lever ships `On` only if it converts **≥ 4 rows of
this population net, with 0 losses, 0 flips, every moved row STABLE-GAIN over 3
passes per arm, and 0 authority disagreements.** Below that it ships `Off` and
the lane says so. Chosen before any lever exists: 4 is the smallest count that
cannot be one file moving inside a noise band this lane has not yet measured.

**R10 — no lever is built at all unless step 3 names ONE capability and its
implementation site is bounded to a named set of functions.** "Eleven unrelated
capabilities" is a complete and publishable lane outcome. Do not manufacture a
lever.

**R11 — the A/B measures THIS BRANCH.** The post-merge value is predicted with
its reason.

**R12 — freshness is licensed by `find -newer`, never by exit status.** Snapshot
and target paths here are reused.

**R13 — no waiter greps for a process by a pattern its own command line
contains.** Every waiter watches an artifact.

**R14 — an unfinished check is reported as "did not run".** Never an intention
described as an observation.

## The predictions

**P1.** Fewer than 13 rows survive R1+R2. Specifically ≥ 1 row is INADMISSIBLE
under R2's fresh-atom control.

**P2.** The 11 `CAPABILITY-LIMIT` rows do NOT need 11 different capabilities.
Between 1 and 3 named capabilities cover ≥ 6 of them.

**P3.** At least one row's refutation needs no theory solver at all — it is
propositional over opaque atoms, and we ship a SAT solver.

**P4.** The minimal unsat subsets are small: median ≤ 5 conjuncts.

**P5.** The `AUFLIRA` six behave as one family, because they come from two
generators in one directory tree.

[ADR-1957]: ../../docs/research/09-decisions/adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-2035]: ../../docs/research/09-decisions/adr-2035-two-populations-reach-one-boundary-and-a-round-cap-can-convert-neither.md
[ADR-2040]: ../../docs/research/09-decisions/adr-2040-the-reach-half-is-worth-two-and-the-whole-remaining-shape-is-the-ground-checker.md
