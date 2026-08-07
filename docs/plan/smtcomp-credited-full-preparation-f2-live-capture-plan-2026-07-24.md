# SMT-COMP credited full-population F2 live-capture plan

Status: preregistered; no host probe, sentinel process, NAS preparation root,
acceptance record, allocation, or solver wave has been created

Date: 2026-07-24

Parent: [credited full-population execution plan](smtcomp-credited-full-population-plan-2026-07-23.md)

Durability contract: [accepted ADR-0344](../research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md)

Preparation contract: [F2 implementation result](smtcomp-credited-full-preparation-f2-implementation-2026-07-23.md)

## Objective and boundary

Add the missing operator that captures and publishes one real F2 preparation
through the already-integrated process-free contracts. The operator may build
readiness evidence, rehash the accepted population, stage exact bytes, probe the
three registered hosts, execute the eight incident sentinels, and publish one
completion-last preparation. It must remain structurally incapable of starting
an allocation or admitting a solver cell.

The terminal state remains:

```text
status=prepared-no-launch
launch_authorized=false
```

This milestone does not create the canonical mainline acceptance required by
F3. A successful F2 root must be independently replayed, documented, and
integrated byte-for-byte before a separate acceptance commit can be reviewed.

## C0: source and gate authority

The live operator must reject before creating an attempt directory unless all
of the following hold in the invoking worktree:

1. `git status --porcelain=v1 -z --untracked-files=all` is empty;
2. local `HEAD`, the local `origin/main` tracking ref, and the current
   `git ls-remote origin refs/heads/main` value are the same 40-hex commit;
3. every registered readiness path is byte-identical to that commit;
4. fresh, exact invocations of `just check` and
   `./scripts/check-smtcomp-resume.sh` both exit zero; and
5. the resulting sealed readiness record reports
   `ready_for_live_preparation=true`.

Network, ref, command, output, or worktree-state uncertainty is a rejection,
not permission to continue. Gate stdout and stderr remain represented by their
exact byte counts and SHA-256 identities in the existing observation schema.
The expensive gates run before any NAS mutation or 30-minute capture window.

The new operator and this plan become registered readiness paths. Consequently,
the operator cannot satisfy C0 from an unintegrated topic branch, even if its
focused tests are green.

## C1: immutable pre-capture materialization

Only after C0 passes, create a fresh attempt beneath:

```text
<shared-root>/credited-full-preparations/<attempt-id>/
```

Attempt IDs use the existing safe identifier alphabet and default to the exact
source commit plus a nanosecond nonce. An existing attempt path rejects; the
operator never resumes, deletes, overwrites, or silently reuses an incomplete
capture.

Before the first live observation, the operator must:

- stream and physically rehash the accepted 45,905-file population;
- reproduce the frozen absolute list and v2 input-manifest identities;
- stage the content-addressed SMT-COMP source bundle and source identity;
- copy and rehash the exact corpus audit plus Axeyum, cvc5 1.3.4, and Bitwuzla
  0.9.1 executables beneath the attempt;
- require the two oracle binary hashes frozen by the parent plan;
- copy and rehash the exact QF_ABVFP, QF_BVFP, and QF_AUFLIA sentinel inputs;
  and
- retain empty cell namespaces with no attempt, terminal, resource-session, or
  result record.

The Axeyum release binary is built immediately before the operator with:

```sh
CARGO_BUILD_JOBS=2 CARGO_TARGET_DIR=target-codex \
  cargo build --release --locked -p axeyum-bench --example smtcomp_cli
```

The operator records the staged binary bytes and clean source revision through
the existing preparation and run identities. It does not infer provenance from
a filename or an earlier build.

## C2: bounded host and sentinel capture

The 30-minute interval starts immediately before the first remote observation.
Within that interval, in this exact order, the operator must:

1. capture sealed `s5`, `s6`, and `s7` host observations through the staged
   helper;
2. reconstruct one exact environment manifest and the three cell
   registrations from those observations;
3. compose and replay all three process-free cell plans, schedules, and 432
   command manifests; and
4. execute the registered sentinel rows in the existing
   `SENTINEL_ROWS` order:
   QF_ABVFP on Axeyum/cvc5/Bitwuzla, QF_BVFP on
   Axeyum/cvc5/Bitwuzla, then QF_AUFLIA on Axeyum/cvc5.

Every sentinel uses the staged binary and staged input beneath the attempt,
`AYU_THREADS=1`, `OMP_NUM_THREADS=1`, `RAYON_NUM_THREADS=1`, an 8-GiB memory
limit, and a 20-second runner limit. Axeyum additionally receives its frozen
19-second internal timeout. Each stdout and stderr stream is installed as an
immutable exact-byte sidecar before its sealed record is accepted.

The existing semantic policy remains authoritative: all six FP observations
must be completed exit-zero `unsat`; cvc5 QF_AUFLIA must be completed exit-zero
`sat`; Axeyum QF_AUFLIA may only be completed `sat`/`unknown` or a verdict-free
wall timeout. Any other status, termination, ordering, timestamp, input,
binary, command, environment, or sidecar identity rejects publication.

## C3: completion-last publication and failure state

After the final sentinel, build and replay the sealed preflight, then call the
existing publisher before `started_at_ns + 30 minutes`. `complete.json` is the
last installed artifact. A fresh-process verifier must reconstruct the full
artifact ledger, source bundle, selection, composition, readiness, preflight,
binaries, sidecars, and empty execution namespaces.

Failure handling is append-only and explicit:

- a failure before attempt creation leaves no NAS path;
- a failure after attempt creation leaves the incomplete attempt without
  `complete.json`;
- no automatic cleanup, retry, or promotion occurs; and
- a retry uses a new attempt ID and fresh gates, probes, and sentinels.

The operator imports no F3 admission/execution module and contains no call to
`start_allocation`, `execute_host_command`, `systemd-run`, `systemctl stop`,
blanket process matching, or a solver-wave coordinator. The only solver
processes it may execute are the eight bounded local sentinel commands.

## C4: implementation and mutation gates

Before integration, focused tests must prove:

- stale local tracking refs, remote-main drift, local descendants, dirty trees,
  missing remote state, and either failed registered gate reject before the
  attempt directory exists;
- unsafe attempt IDs and existing attempt roots reject without overwrite;
- population, corpus, source, binary, and sentinel-input drift reject;
- host observations and sentinel records are captured and replayed in the
  exact registered order;
- a sentinel failure leaves no completion and triggers no allocation path;
- the publication deadline is enforced at both preflight and completion;
- `complete.json` is installed last and every execution-evidence directory is
  empty;
- an independent verify mode is read-only and rejects artifact mutation; and
- a static source test rejects allocation/admission imports or calls in the
  live-capture module.

Required focused gates:

```sh
PYTHONWARNINGS=error python3 -m unittest \
  scripts.tests.test_smtcomp_full_population
./scripts/check-smtcomp-resume.sh
python3 scripts/gen-smtcomp-resume-contract.py --check
just foundational-resources
./scripts/check-links.sh
```

The final topic must then pass `just check` before the integration owner merges
it. Live capture remains forbidden until the exact implementation and this plan
are ancestors of current, green `origin/main`.

## C5: separately authorized live procedure

After integration, the operator command must name the accepted selection,
verified corpus acquisition, exact release binaries, and committed sentinels:

```sh
python3 scripts/prepare-smtcomp-credited-full.py \
  --shared-root /nas3/data/axeyum/harness/official-selection-2026-sq \
  --accepted-selection /nas3/data/axeyum/harness/official-selection-2026-sq/accepted-322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698 \
  --corpus-root /nas3/data/axeyum/harness/official-selection-2026-sq/corpus-acquisition-1784745749642951377-d48fb0dc/corpus \
  --corpus-manifest /nas3/data/axeyum/harness/official-selection-2026-sq/corpus-acquisition-1784745749642951377-d48fb0dc/corpus-audit.json \
  --axeyum-binary target-codex/release/examples/smtcomp_cli \
  --cvc5-binary /nas3/data/axeyum/harness/bin/cvc5 \
  --bitwuzla-binary /nas3/data/axeyum/harness/bin/bitwuzla \
  --qf-abvfp-sentinel bench-results/smtcomp-full-library-20260722/soundness-fp-wrong-sat/qf_abvfp_query.26.smt2 \
  --qf-bvfp-sentinel bench-results/smtcomp-full-library-20260722/soundness-fp-wrong-sat/qf_bvfp_query.26.smt2 \
  --qf-auflia-sentinel corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/smtlib2024__array_benchmarks__misc__pipeline-invalid.smt2
```

The printed completion is review input only. A second process must run the
operator's read-only verify mode against the exact root, after which a result
document records the identities and bounded claim. No F3 acceptance or
allocation is part of C5.

## Stop conditions

Stop without widening the contract on any wrong sentinel, gate failure, remote
or local ref drift, host/environment mismatch, thermal or resource concern,
selection/hash drift, expired capture, incomplete artifact, or unexpected
execution evidence. Preserve the failed attempt and diagnose it under a new
source-first amendment. Do not weaken validation, raise resource limits, reuse
stale observations, or launch around the failure.
