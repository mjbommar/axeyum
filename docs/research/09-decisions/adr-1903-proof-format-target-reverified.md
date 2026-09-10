# ADR-1903: Roadmap 4.3 is already closed by ADR-1815; re-verified at `60fe8bdf2`, and its prerequisite is half-discharged — the crosscheck gate landed, the rule-parity derivation still does not run

Status: accepted (confirms ADR-1815; no new decision)
Index-summary: Roadmap item 4.3 was closed by ADR-1815 — stay Alethe-only, no Ethos/Eunoia route without a consumer — and this is the re-verification, not a second decision. Every load-bearing count reproduces at `60fe8bdf2` (180 pinned rules, 64 `Evidence` variants of which 3 carry Alethe, 8 `Evidence::Unsat(None)` construction sites, 22 trust routes with 4 `NO_CHECKER`, zero Ethos/Eunoia/CPC code). What changed: ADR-1815's commitment-3 prerequisite (roadmap 0.2) has LANDED as `scripts/check-carcara-gate.sh` — `AXEYUM_REQUIRE_CARCARA=1` by default, a build-free `--self-check` negative control, a 40-invocation floor, registered in both aggregate gates. What has NOT: `carcara_checked_rules_parity.rs:119-129` still skips green, so ADR-1815's sharpest finding — the 180-name list is a hand-written literal *as executed* — stands unchanged.
Index-status: accepted — confirms ADR-1815
Date: 2026-09-10

## Context

Roadmap item 4.3 of
[`docs/solver-comparison-2026-09/11-roadmap-and-plan.md:110`](../../solver-comparison-2026-09/11-roadmap-and-plan.md)
asks whether to stay Alethe-only or add an Ethos route, with the constraint
"do not do both without a consumer".

**It was closed on 2026-09-09 by
[ADR-1815](adr-1815-the-proof-format-target.md):** stay Alethe-only, because an
Ethos/Eunoia emitter would have zero consumers while the format we already emit
has an in-tree consumer that runs and an external consumer that does not — and
the effort a second format would take is exactly the effort that makes the
first one's external check able to fail.

As with [ADR-1901](adr-1901-z3-demotion-reverified.md), this file is **not a
second decision**. It is the independent re-measurement that a decision record
cannot carry for itself, taken a day later by a different lane, plus the one
thing that has materially moved since.

## Decision

**ADR-1815 stands unamended. No new decision is taken here.**

Three things recorded:

1. **Every load-bearing count reproduces exactly at `60fe8bdf2`.** None of
   ADR-1815's five falsifiers has fired.
2. **Its commitment 3 — "the Carcara gate is a prerequisite, not a parallel
   track" — is now half-discharged.** Roadmap item 0.2 has landed, and in a
   stronger form than the item asked for. Item 0.1's exit criterion has **not**;
   it is met in source and unmet in execution.
3. **Three of ADR-1815's counts cannot be reproduced by the obvious grep**, and
   the obvious grep is wrong by 2× to 3.6× on each. The correct method is
   recorded below so the next re-verification does not "correct" a right number
   into a wrong one.

## Evidence

All at `60fe8bdf2`, no build required.

### 1. The counts, re-taken

| ADR-1815's claim | Here | How |
|---|---|---|
| `CARCARA_CHECKED_RULES` at `alethe.rs:696`, **180** entries | `:696`, **180** | `awk 'NR>=697 && NR<=876' … \| grep -cE '^\s*"'` |
| `"minus_simplify"` present (item 0.1 done in source) | `alethe.rs:802` | `grep -n '"minus_simplify"'` |
| `Evidence` has **64** variants, **3** carry Alethe | **64**, **3** | brace-matched parse of `pub enum Evidence {` (`:371`), nested groups elided |
| **8** `Evidence::Unsat(None)` construction sites, all in `evidence.rs` | **8** | see §3 |
| `trust.rs`: **22** `EvidenceRoute`, 12 `certifies: true`, 10 false, **4** `NO_CHECKER` | 22 / 12 / 10 / **4** | see §3 |
| No Ethos/Eunoia/CPC code in `crates/` | **0** — the one hit for `ethos` is `gethostname` in `smtcomp_cli.rs:1663` | `grep -rniE 'ethos\|eunoia\|\bCPC\b' --include=*.rs crates/` |
| `bv_bitblast_step` appears zero times | **0** | `grep -rc … \| grep -v ':0'` returns nothing |
| `references/` holds one file | `README.md` only | `ls -a references/` |

The three Alethe-carrying variants are `UnsatAletheProof`,
`UnsatArithAletheProof`, `UnsatGuardedQuantAletheProof` — unchanged.

### 2. What changed: roadmap 0.2 has landed

ADR-1815's commitment 3 said no proof-format comparison is testable "until
`AXEYUM_REQUIRE_CARCARA=1` makes an absent binary a failure and a renamed rule
fail the gate". Both now exist, in `scripts/check-carcara-gate.sh`:

- **Absence is a failure by default.** The script sets
  `AXEYUM_REQUIRE_CARCARA=1`; a host that genuinely lacks Carcara must set
  `AXEYUM_ALLOW_NO_CARCARA=1` and gets a banner saying in words that zero checks
  ran. `crates/axeyum-solver/tests/carcara_crosscheck.rs:139-142` is the
  matching test-side switch.
- **It counts rather than trusting exit status**, with
  `CHECK_FLOOR` defaulting to **40** real invocations — because the script's own
  header records the measurement that makes this necessary: carcara 1.1.0
  (git `6624ea8`) returns **exit 0 for both `valid` and `holey`**, and only an
  `Err` reaches exit 1. The verdict is the stdout line, parsed exactly rather
  than by substring — "invalid" contains "valid".
- **It carries its own negative control, and it needs no build.**
  `--self-check` writes four three-line Alethe proofs and asserts the script
  classifies each as measured; flipping `verdict_of`'s `holey` arm to accept
  fails `--self-check` on the `hole` case alone. That is the
  delete-one-guard / exactly-one-test-dies rule, implemented.
- **It is registered in both aggregate gates**: `scripts/check.sh:1306-1307`
  (self-check, then gate) and `justfile:1375-1376`.

This is a stronger artifact than item 0.2 specified, and ADR-1815's commitment 3
should be read as discharged for the *crosscheck* half.

### 3. What has NOT changed, and it is the important half

`crates/axeyum-cnf/tests/carcara_checked_rules_parity.rs:119-129` still opens
with:

```rust
let Some(path) = carcara_shared_rs_path() else {
    eprintln!("[skip] references/carcara not present at {} …", …);
    return;
};
```

`references/carcara` is absent in this worktree (`ls references/` → `README.md`
only). So the derivation this test exists to perform — parse `get_rule`'s match
arms out of the clone, subtract `DELIBERATELY_EXCLUDED = ["hole",
"lia_generic", "rare_rewrite"]`, assert set equality against the pinned 180 —
**has still never run here.**

That means **ADR-1815's sharpest finding is unchanged**: the 180-name list is,
as executed evidence, a hand-written literal. Roadmap item 0.1's exit criterion
is explicit that "a test derives that set from the clone rather than a literal";
that is satisfied in *source* and unsatisfied in *execution*, and only the
second is evidence. Item 0.1 should not be marked done on the strength of
`"minus_simplify"` being present at `:802`.

**Not run here, and said plainly:** this lane did not execute
`check-carcara-gate.sh`. No `carcara` binary is on this host (`command -v
carcara` → nothing, `AXEYUM_CARCARA_BIN` unset, `references/carcara` absent),
and this lane does no heavy compute. Under the gate's own design that is a
FAILURE, not a skip — which is the gate working, not a finding about it. The
residual work is one `scripts/fetch-references.sh` run on a gate host, after
which both the parity derivation and the crosscheck have a subject.

### 4. Method caution — three counts the obvious grep gets wrong

Recorded because a re-verifier who trusts a bare `grep -c` will "find" three
discrepancies that do not exist, and may edit a correct ADR to match them. Each
number below is what the naive command prints, then what is true:

| Quantity | naive command | prints | truth | why |
|---|---|---|---|---|
| `NO_CHECKER` routes | `grep -c NO_CHECKER trust.rs` | 8 | **4** | 4 are the `pub const` at `:176`, two doc comments (`:173`, `:236`), and a comparison at `:762`. Only `checker: NO_CHECKER` at `:307`, `:318`, `:371`, `:406` are routes. |
| `Evidence::Unsat(None)` sites | `grep -c 'Evidence::Unsat(None)' evidence.rs` | 29 | **8** | 21 are doc comments and `match` arms. Construction sites only. |
| `Evidence` variants | `awk '/^pub enum Evidence/,/^}/' \| grep -cE '^\s{4}[A-Z]…'` | 67 | **64** | the range also opens at `pub enum EvidenceCheck` (`:328`), and the pattern catches attribute and doc lines. Brace-match from `pub enum Evidence {` at `:371` and elide nested groups. |

I ran each naive form first and got each wrong number. ADR-1815's figures are
right; my first three greps were not.

## Alternatives

- **Write a second substantive ADR on 4.3.** Rejected, same reason as
  ADR-1901: two accepted records deciding one question, with nothing to
  supersede.
- **Amend ADR-1815 to note that roadmap 0.2 landed.** Rejected — ADRs are
  immutable once accepted.
- **Argue that the landed Carcara gate discharges commitment 3 and therefore
  reopens the format question.** Rejected on the measurement in §3: the gate
  exists but has no subject on any host in this lane's reach, and the parity
  derivation still does not run. ADR-1815's commitment 3 says demotion of the
  question waits on the gate *being shown able to fail against a real binary*,
  not on the script existing. It has a self-check, which is a real and
  meaningful half; it does not yet have a Carcara.
- **Mark roadmap item 0.1 done.** Rejected. `"minus_simplify"` is present, but
  0.1's own exit criterion is about the *derivation*, and the derivation skips.

## Consequences

- **4.3 is closed and should be struck from the Phase 4 queue**, pointing at
  ADR-1815.
- **Roadmap 0.2 should be marked done**, pointing at
  `scripts/check-carcara-gate.sh` and its two registrations.
- **Roadmap 0.1 should stay open**, with its remaining work restated as "fetch
  `references/carcara` on a gate host so the parity derivation runs" rather than
  "add the name to the list", which is done.
- **The next unit of proof-format work is still not a format.** It is one
  `fetch-references.sh` run, and then whatever the parity derivation says.

**What is LOST by deciding this way.** Everything ADR-1815 listed as lost is
still lost: no cvc5/Ethos interoperability, a single external checker that is
still not running anywhere this lane can see, and Alethe carried by 3 of 64
`Evidence` variants rather than being the trunk. Confirming a decision is not
progress on it.

## What would falsify this ADR

It is a measurement: **any count in §1 differing on a later commit**, or the
parity test in §3 no longer skipping — the latter would be good news and would
discharge ADR-1815's commitment 3 in full.
