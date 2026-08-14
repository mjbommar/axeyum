# Decision Records

Status: draft
Last updated: 2026-06-11

## Purpose

The research-questions register says every open question should resolve into
"an ADR, benchmark, implementation result, or explicit deferral" — this
directory is where those resolutions live. Research notes describe the option
space; decision records close questions.

## Process

- One file per decision: `adr-NNNN-short-slug.md`, numbered sequentially.
- Status is one of: `proposed`, `accepted`, `superseded by adr-NNNN`,
  `deferred`.
- Each ADR links the research-questions entries it closes; the closed
  question in `08-planning/research-questions.md` gets a link back.
- ADRs are immutable once accepted; reversals get a new ADR that supersedes
  the old one.
- **Never edit the index by hand.** Write the ADR file and run
  `python3 scripts/gen-adr-index.py`; `--check` is a gate in `scripts/check.sh`
  and `just check`. The index used to be appended by every lane — 60 touches in
  24 hours on 2026-08-13/14, with two rows silently overwritten.
- Two optional front-matter lines control the row this file gets. Use them when
  the row should say more, or less, than the ADR's own heading and status:

  | line | effect |
  |---|---|
  | `Index-summary: …` | the row's Title cell (default: the `# ADR-NNNN:` heading) |
  | `Index-status: …` | the row's Status cell (default: the whole `Status:` line) |

  377 ADRs carry an `Index-summary:` because the hand-maintained index had
  accumulated a curated one-line summary that existed nowhere else; migrating
  them into the ADRs is what let the index be generated without losing them.
  New ADRs need neither line if the heading and status already read well.
- Front matter is the run of `Key: value` lines at the top of the file, ending
  at the first line that is not one. `- Status: …` and `- **Status:** …` are
  also recognised; nine committed ADRs use those shapes.

## Template

```markdown
# ADR-NNNN: Title

Status: proposed | accepted | superseded by adr-NNNN | deferred
Date: YYYY-MM-DD

## Context

What question this closes and why it must be decided now.
Link the research notes and register entries involved.

## Decision

The decision, stated as a single committed sentence, then detail.

## Evidence

Benchmarks, prototypes, references, or reasoning that justified it.

## Alternatives

What was rejected and why.

## Consequences

What becomes easier, what becomes harder, what gets revisited and when.
```
