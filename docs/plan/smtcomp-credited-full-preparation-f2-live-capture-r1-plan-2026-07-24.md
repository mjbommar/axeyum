# SMT-COMP credited full-population F2 live-capture R1 plan

Status: preregistered correction; no host probe, thermal sample, sentinel
process, NAS preparation root, acceptance record, allocation, or solver wave
has been created

Date: 2026-07-24

Parent: [F2 live-capture plan](smtcomp-credited-full-preparation-f2-live-capture-plan-2026-07-24.md)

Repaired-P0 authority:
[combined comparison result](smtcomp-repaired-p0-combined-comparison-result-2026-07-23.md)

## Why this correction exists

The first source-first plan correctly froze the exact-main gate, immutable
population/staging contract, bounded host and sentinel capture, and
completion-last no-launch publication. A preimplementation audit found two
parent requirements that it did not make executable enough:

1. it did not require the operator to replay the frozen repaired-P0 comparison
   and its three external live roots before creating a new NAS attempt; and
2. it mentioned thermal stop conditions but did not bind fresh per-host
   thermal observations into the sealed preflight.

This R1 document adds only those two requirements. Every prohibition, time
limit, sentinel policy, and F3 boundary from the parent remains unchanged.

## R1.1: repaired-P0 authority before mutation

The operator gains a required `--repaired-p0-preparation` argument. Before
creating `<shared-root>/credited-full-preparations/<attempt-id>`, it must use
the process-free repaired-P0 comparison reader to:

- resolve and validate the named completed preparation root;
- resolve and validate all three exact Axeyum, cvc5, and Bitwuzla external
  result roots named by that preparation;
- replay every frozen result and comparison invariant; and
- require the derived comparison to equal the committed generated comparison
  byte-for-byte after canonical decoding, including
  `safe_to_publish=true`, zero contradictions, and zero disagreements.

The comparison module, generator, and generated JSON/Markdown views become
registered readiness paths. Missing roots, stale bytes, path substitution,
unsafe comparison state, or any mismatch with the committed authority rejects
before the attempt parent is created.

The separately authorized command therefore additionally names:

```sh
  --repaired-p0-preparation /nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-75e544a8-v2
```

## R1.2: thermal evidence in preflight v2

The full-preflight schema advances to v2 and gains exactly three
`thermal_observations`, ordered `s5`, `s6`, `s7`. After process-free
composition and before the first incident sentinel, the operator must use the
staged remote helper to capture one exact `sensors -j` byte stream per host.
Each sealed observation must bind:

- the Axeyum cell's exact plan SHA-256, run identity, cell ID, first-wave index,
  allocation ID, and host ID;
- `attempt_id=null`, because F2 has no allocation or solver attempt;
- an observation timestamp inside the same 30-minute capture window; and
- the exact raw sensor bytes, byte count, and SHA-256 embedded by the existing
  thermal-observation contract.

Every observation must replay and report a maximum temperature strictly below
the existing 90,000 mC stop threshold. The host order must exactly match the
Axeyum first-wave schedule and the registered `s5`, `s6`, `s7` order. The
preflight validator rebuilds these bindings from the published composition; a
missing, reordered, stale, overheated, malformed, or identity-drifted sample
rejects. Embedded exact bytes are authoritative, so no additional mutable
thermal sidecar is introduced.

The capture order becomes:

1. host observations;
2. environment and registrations;
3. process-free plans, schedules, and command manifests;
4. three ordered thermal observations; and
5. the eight ordered incident sentinels.

## R1.3: additional gates

Focused tests must additionally prove:

- repaired-P0 missing-root, external-root drift, unsafe comparison, and
  committed-authority mismatch reject before any attempt directory exists;
- the operator invokes no allocation or admission route while replaying that
  authority;
- the preflight rejects a missing or reordered thermal row, host/plan/run/cell/
  wave/allocation/attempt drift, raw sensor-byte drift, an out-of-window
  timestamp, and a temperature at or above 90,000 mC; and
- the end-to-end fixture publishes only after all three thermal rows and all
  eight sentinels replay successfully.

The parent plan's focused commands and final `just check` remain required.
Neither this correction nor its implementation authorizes live capture from a
topic branch.
