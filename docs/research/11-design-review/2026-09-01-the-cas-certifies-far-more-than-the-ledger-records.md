# The CAS certifies far more than the ledger records

> **CORRECTED 2026-09-01 by the audit this document dispatched
> (`docs/research/11-design-review/2026-09-01-cas-certificate-reconstruction-audit.md`,
> ADR-1400). BOTH headline numbers below were wrong, in opposite directions,
> and the errors nearly cancelled — so the gap this document reported is
> roughly twice the real one.**
>
> | | this document said | measured | why mine was wrong |
> | --- | --- | --- | --- |
> | certificate-carrying modules | 40 of 53 | **27 of 55** | my grep was unmasked, so it matched `certificate` inside Rust comments and string literals. A second, declaration-shaped query gives 23; the union is 30. |
> | CAS facts in the ledger | 19 | **48** | I counted the `F-cas-*` **filename** convention. The ledger's own notion is `proof_route: cas-certificate`, which `validate-facts.py` prints. The 29 I missed are named for their mathematics — nine telescoping, seventeen geometry, four GF(2). |
>
> Joining both sides per module gives the number that actually answers the
> question: **13 certificate-carrying modules with no naming fact, not 34.**
>
> One specific claim below is **false** and is left in place rather than
> silently edited, because the way it failed is the point: I wrote that
> Zeilberger creative telescoping has "no fact at all". `telescoping.rs` and
> `telescoping_check.rs` are each named by **nine settled facts**. `gosper.rs`
> genuinely has none.
>
> I ran an unmasked survey grep and published its output as a measurement,
> which is a banned idiom in this repository's own notes, in a document whose
> subject is under-measurement. Verify both numbers before quoting either.

**Measured 2026-09-01, in the shared checkout.**

`crates/axeyum-cas/` is ~77,600 lines, 685 public functions, 53 modules in
`src/*.rs` plus four subdirectories. **40 of those 53 modules carry a
certificate or checker surface** — a `Certificate` type, a `fn verify`, or a
`fn check_*`:

```
/usr/bin/grep -l "certificate\|Certificate\|fn verify\|fn check_" \
  crates/axeyum-cas/src/*.rs | wc -l
  -> 40 of 53
```

The fact ledger records **19** `F:cas-*` facts against 2,523 facts total:

```
ls artifacts/facts/ | /usr/bin/grep -c "^F-cas-"   -> 19
```

and they cluster on IVT / EVT / MVT / Taylor / partial fractions / a handful
of number theory certificates. **Whole certificate-carrying subsystems have
no ledger fact at all** — on a first pass: Gröbner with cofactor witnesses
(`groebner.rs`, `groebner_cert.rs`, `cofactor_ansatz.rs`), Gosper and
Zeilberger creative telescoping (`gosper.rs`, `telescoping.rs`, and
`telescoping_check.rs`, whose checker shares no code with its producer),
Horowitz–Ostrogradsky rational integration (`ratint.rs`, and `lib.rs::integrate`
which self-certifies), Sturm isolation (`sturm.rs`), real algebraic numbers
beyond the quintic witness (`real_algebraic.rs`), Hermite and Smith normal
forms (`normalforms.rs`), the seven-module GF(2) development, `gfp.rs`,
`orthopoly.rs`, `sos/`, `interval_arith.rs`, `series.rs`, `combinatorics.rs`.

## Why this is a defect and not a backlog

Two reasons, and the second is the one that costs.

**It understates the system to a referee.** ADR-0603 makes row 3 — the
decidable-fragment exact form settled by the CAS with a certificate that
reconstructs into the kernel — a first-class row of a graded statement family.
A row-3 result that exists in code and not in the ledger is a result the
project cannot point at, and the ledger is what a referee reads.

**It understates the system to US.** This session opened with the coordinator
describing the curriculum as having "three routes" and omitting the CAS
entirely, and separately reporting the CAS at 72,008 lines / 363 functions
against a true 77,590 / 685. Both errors came from reading prose rather than
the crate. The ledger is the artifact that would have made either impossible,
and it is the artifact that is thin. A subsystem with no fact is a subsystem
the next reader will forget again.

## What a fix looks like

Not "add 34 facts". The obligation per ADR-0601 is sharper: **CAS evidence must
either reconstruct into the kernel, or be visibly labelled `cas-internal`.**
So the work is, per certificate-carrying module:

1. Decide whether its certificate reconstructs today, could reconstruct with
   bounded work, or is `cas-internal` by nature.
2. Record the ones that reconstruct as facts with a `checker_command` whose
   exit status depends on what the run found.
3. Record the `cas-internal` ones **as such**, so the boundary is visible
   rather than implied by absence.

An honest "this module's certificate is `cas-internal` and here is why" is a
complete result. An absent fact is not.
