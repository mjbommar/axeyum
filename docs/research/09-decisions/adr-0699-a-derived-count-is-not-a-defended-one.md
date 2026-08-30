# ADR-0699: A derived count is not a defended one — the cas-substance floor is a per-fact ratchet plus an absolute number

Status: accepted
Date: 2026-08-30
Index-summary: `check-cas-substance.py`'s headline count was derived from the
ledger — 12 mutants each killed a control and the number moved under mutation —
and was still not defended: deleting a `cas-certificate` fact outright, or
downgrading it consistently, exited 0 with a quietly smaller number. A gate that
reports a smaller number as success cannot notice deletion. The floor is now the
SET of facts that reached kernel reconstruction with the two properties this
gate can verify, plus an absolute count.
Index-status: accepted

- **Lane:** `gate-survivors`
- **Answers:** the third of five survivors in
  [the 2026-08-30 session audit](../11-design-review/2026-08-30-session-audit.md)
  §5b.
- **Files:** `scripts/check-cas-substance.py`,
  `scripts/check-cas-substance.ratchet`,
  `scripts/tests/test_check_cas_substance.py`.

## Context

The audit measured three things on the shipped gate:

```
strip a fact's kernel reconstruction AND its cas_substance block  -> exit 0, "OK: 13 ..."
strip the reconstruction but KEEP the block                       -> exit 1, G12 fires
delete the fact file outright                                     -> exit 0, "OK: 13 ..."
```

So it caught an **inconsistent** downgrade and passed a **consistent** one. The
count in `OK: 14 …` is genuinely derived — all twelve registered mutants die and
the number moves under mutation, so it is not a literal — and that is a
different property from being defended. Derivation says the number is *real*;
nothing said it may not *fall*.

This matters more here than for an ordinary counter. `kernel-reconstructed` is
the distinction ADR-0601 draws between evidence that reaches the trust anchor
and evidence that never leaves the CAS. It is a headline number, and the whole
argument of this gate's own docstring is that a counter which moves for the
wrong reason is worse than no counter.

## Decision

**The floor is the SET, not the number — with a number behind it.**

`scripts/check-cas-substance.ratchet` records one row per fact that reached
kernel reconstruction, carrying the two properties this gate can actually
verify:

```
<fact id>\t<derived|declared>\t<discriminating|non-discriminating>
```

The gate refuses three losses of established ground:

- **R1** a ratcheted fact that no longer classifies as `kernel-reconstructed` —
  downgraded to `cas-internal`, or the file deleted;
- **R2** a fact whose shape was **derived** from a committed certificate and is
  now self-reported, so the gate stopped checking ADR-0622 rule 3 — the half a
  lane cannot talk its way around, because the number comes from the CAS's own
  output;
- **R3** a fact whose shape was **discriminating** and is now `refl` or `empty`.

Growth is free: a new fact needs no edit here, and a row recorded as
non-discriminating that becomes discriminating is accepted. A ratchet that taxes
landing facts, or that refuses improvement, is a freeze.

**And an absolute floor**, because the per-fact rules alone have one hole worth
naming rather than hiding: deleting a fact **and** its ratchet row in one commit
satisfies every one of them. `MIN_KERNEL_RECONSTRUCTED = 14` is checked against
both the ledger and the ratchet's own length. This is the shape
`--expect-axioms 26` has elsewhere in this ledger, and the audit named that
comparison itself.

## Why 14 is the honest floor

It is not chosen. It is what the ledger established: 14 of 42 `cas-certificate`
facts reach the kernel today, 6 of them with a shape derived from a committed
certificate and 8 self-reported (ADR-0622 records that split and prints it as a
number rather than leaving it implicit). Raising it as the ledger grows is
ordinary maintenance; **lowering it is a published retreat**, and the diff says
so in review rather than being absorbed into a smaller headline.

One row is deliberately `non-discriminating`:
`F:geometry-thales-cofactor-identity-kernel-checked`, whose registering lane
found and disclosed that its obligation is refl-shaped. Registration is the
honest outcome for a weak-but-real reconstruction; the ratchet's job is that it
cannot *silently become* the only kind.

## What this does not establish

The ratchet cannot verify the 8 self-reported shapes any more than the gate
could before — that needs those producers to emit certificates, and it is the
future work ADR-0622 already names. What changed is only that a fact which
reached the kernel cannot quietly stop having done so.

## Verification

Nineteen mutants, each anchored in `scripts/tests/mutation_controls.py` under
`cas-substance`, all killed, **no survivors** — including seven new ones for the
ratchet itself. Two of the seven survived the first run (`R0`, a missing ratchet
file, and `R0c`, a ledger below the absolute floor) because the harness always
wrote a ratchet and because `R1` fired on the same fixture. Both were closed by
building the scenario that isolates them rather than by excusing the survivor: a
sentinel that writes no file at all, and a two-row ratchet against a one-fact
ledger so only the count rule can fire, asserting the floor's **own message**
rather than a nonzero exit.

The audit's own scenario, re-run end to end on the real ledger:

```
rm artifacts/facts/F-geometry-thales-cofactor-identity-kernel-checked.json
python3 scripts/check-cas-substance.py
  FAIL: 13 kernel-reconstructed cas-certificate fact(s) against an absolute
  floor of 14. A smaller headline is a retreat to publish, not a pass.
  status=1
```

Restored, the gate is green and the fact file is byte-identical to `HEAD`.
