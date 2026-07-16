# ADR-0203: Defer Glaurung direct-delta default after dual-control gate

Status: accepted
Date: 2026-07-16

## Context

ADR-0201 supplies Axeyum's first-class retained solver contract, and ADR-0202
makes direct-delta entry cost attributable. Glaurung can translate only a
confirmed persistent suffix and keep probe roots temporary. The first real
SurfacePen run also proved that an absolute depth is not a sufficient sibling
identity: combining direct markers with snapshot-era serial sibling leasing
retained the opposite branch's equal-depth root and produced 497 verdict
disagreements.

Glaurung fixed that soundness error by making direct entry use exclusive owner
transfer and distinct siblings. That changes topology as well as entry cost, so
production admission requires two controls: an exclusive-transfer snapshot
control isolates the value of removing whole-snapshot reconstruction, while
the current serial-snapshot policy is the actual default direct entry would
replace.

## Decision

Accept direct-delta sessions as correct, useful opt-in infrastructure, but do
not make them the Glaurung production default. Keep serial snapshot reuse as
the current automatic policy.

The next GQ7 structural candidate must preserve source prefix identity rather
than depth alone and retain exclusive mutable solver ownership. A
copy-on-write/shared-ancestor representation is admissible only if it has an
explicit lifecycle and replay argument. It must repeat both the causal
exclusive-transfer control and the production serial-snapshot control before
default admission.

## Evidence

Glaurung `f4da0eb` disables the incompatible serial lease in direct mode. The
same SurfacePen stream then decides and agrees 2,551/2,551 checks with zero
unknowns or replay failures. Glaurung `8bf213e` makes direct policy identity
fail closed in the lineage gate, and `12925e9` commits the three clean repeated
artifacts and downstream ADR-012.

Each artifact contains three SurfacePen and three NETwtw10 processes, 92,721
checks, exact source/environment/work/traffic identity, 100% Z3 agreement,
identical findings, zero unknown splits and replay failures, terminal-zero
session/cache gauges, and a 4 GiB child limit.

Against exclusive-transfer snapshot, direct improves:

- SurfacePen Axeyum time 438.600 to 390.433 ms (-10.98%), normalized ratio
  11.61%, and median RSS 0.05%; and
- NETwtw10 Axeyum time 11.148 to 10.582 seconds (-5.08%) and ratio 4.84%, with
  median RSS +1.21%.

Every causal alarm passes. Against same-current serial snapshot, however,
direct regresses SurfacePen time 7.83%, normalized ratio 9.54%, and RSS 4.88%.
NETwtw10 time improves 2.64%, but median RSS rises 224,860 to 262,484 KiB
(+16.73%). The production comparator rejects SurfacePen time/ratio and
NETwtw10 RSS.

The candidate, transfer baseline, and serial baseline SHA-256 values are:

- `798c5dd2a6426592c84f255844b1cd7ceaf1d7fc488d3ff18c26d8ee1c832ceb`;
- `b7585adf8d4caf62dd2989ac352018bcf64bbf145a7a63affc4bdd9293b55713`;
  and
- `c9502152efa155a8d3f32c8a947ce7e75b45c2538b37d01a4bd95c6c8243ef47`.

## Alternatives

- Enable direct because it beats equivalent topology: rejected because it
  does not beat the policy users currently receive.
- Preserve serial sibling leasing with a depth marker: rejected by the
  measured wrong-verdict failure.
- Waive the NETwtw10 RSS alarm for its time win: rejected because the bounded
  production policy requires time, ratio, and memory to clear independently.

## Consequences

ADR-0201 and ADR-0202 remain accepted API and evidence infrastructure. Direct
entry remains executable for causal profiling and future topology work, but no
Axeyum or Glaurung default changes. GQ7's next implementation question is sound
source-identity/COW sibling-prefix sharing; cold GQ5 work and the accepted
serial-snapshot path remain available independently.
