//! **The constructed-real carrier, with no reachability filter, handed to the
//! real Lean kernel** — and the boundary of what that can mean, measured.
//!
//! # The coverage hole this closes
//!
//! Every other real-Lean cross-check in this repository is *reachability
//! driven*: it renders the closure of one refutation and hands Lean that. So
//! Lean only ever saw the declarations some query happened to cite. Measured on
//! 2026-08-18 by the lane that split the module (ADR-0511), a refutation over
//! the constructed reals reached 343 of the carrier's 465 declarations —
//! **122 had never been handed to any Lean**, and the first time anything
//! pointed Lean at them two of them were refused.
//!
//! This suite removes the reachability filter: the population is the
//! **complete checked environment**, read out of the kernel at run time and
//! never transcribed.
//!
//! # The correction of 2026-08-30, and what it does not concede
//!
//! Until 2026-08-30 this suite claimed pinned Lean's kernel accepts *every*
//! declaration of the carrier, and `F:lean-kernel-accepts-the-whole-
//! constructed-real-carrier` said so. **That claim is false, and the same
//! binary refutes it** — `the_superseded_whole_carrier_claim_is_refuted_by_the_
//! same_binary` below is the previous statement kept as an executable negative
//! control rather than deleted.
//!
//! It went unseen because this suite could not reach a verdict: `creal` needs
//! 16 MiB of stack in debug and a `#[test]` thread has 2 MiB, so
//! `build_creal_prelude` aborted with `SIGABRT` here before a single Lean process ran. A
//! crash read as absence. L0/S4 wrapped it in `on_a_deep_stack`; it then
//! reached Lean and failed.
//!
//! What Lean refuses is a *kind* mismatch, not a proof: `addDeclCore` will not
//! admit a `theorem` whose type does not live in `Prop`, and this kernel admits
//! 48 of them because `CReal.UniformConvergesOn` is deliberately `Type`-valued
//! (`Exists.rec` cannot eliminate into `Type`, so a convergence *rate* must be
//! data). 25 more declarations depend on one. **No proof was rejected and this
//! is not a demonstrated soundness hole** — nor is it nothing: 73 declarations
//! held no independent-replay grade and nothing recorded that. ADR-0775.
//!
//! So the corrected claim is narrower and still the strongest carrier-wide one
//! available: every **representable** declaration replays, the residue is
//! typed, counted and named, and the exclusion is *earned* — Lean itself
//! refuses the unfiltered stream, naming a declaration this kernel
//! independently classified as non-representable.
//!
//! # Why the kernel route and not a `.lean` module
//!
//! The two routes are not equivalent, and that is the finding ADR-0517 records:
//! `lean Module.lean` runs Lean's **elaborator**, whose reducer treats a
//! `theorem` as opaque, so it cannot check any declaration whose type-checking
//! must reduce one — which includes `Nat.gcd`'s recursive step (justified by
//! the theorem `Nat.mod_lt`), hence every closed `Rat` normalization, hence
//! `CReal.Equiv.not_zero_one` and `CReal.not_le_one_zero`.
//! `scripts/lean/replay-lean4export.lean` drives
//! `Lean.Environment.addDeclCore` from our official `lean4export` NDJSON, which
//! is Lean's **kernel**, and the kernel does unfold it. No elaborator, no
//! implicit-argument insertion, no coercion, no code generator, starting from
//! `mkEmptyEnvironment` so nothing can be satisfied by Lean's own `Init`.
//!
//! # What the exit status depends on
//!
//! 1. Lean's kernel accepts the representable stream and reports a final
//!    constant count **equal to** the size of the representable population;
//! 2. that population still carries the two declarations the source route
//!    cannot — by name, because a suite that silently stopped covering them
//!    would look exactly like a suite that passed;
//! 3. the same Lean **rejects** that stream with `CReal.Equiv.not_zero_one`'s
//!    proof swapped for another closed proof, naming that theorem's own type.
//!    Without (3), (1) is consistent with a replay that checked nothing;
//! 4. the same Lean **rejects the unfiltered stream**, naming a declaration
//!    this kernel classified `TheoremTypeNotProp`. Without (4) the narrowing
//!    would be a choice we made rather than a rule Lean enforces;
//! 5. every non-representable declaration carries one of exactly two typed
//!    reasons, and every `blocked-by-dependency` blocker is itself a
//!    not-a-proposition theorem. An untyped residue is a failure.
//!
//! # Cost
//!
//! `build_creal_prelude` is the expensive prelude (~45 s in a debug test
//! binary; `prelude_cache` makes it once per process). The Lean half is a few
//! seconds for ~2,000 declarations, which is why the whole carrier is
//! affordable here and a 7 MB elaborated module is not.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_lean_kernel::{
    Kernel, Lean4ExportMetadata, NameId, build_creal_prelude, on_a_deep_stack,
};

#[path = "support/lean_probe.rs"]
mod lean_probe;

#[path = "support/creal_representability.rs"]
mod creal_representability;

use creal_representability::{Census, Representability, classify, refused_theorem_name};

const TAG: &str = "creal-carrier-kernel-replay";

/// Printed with every count, so a fact pins the run by value instead of a
/// document transcribing it.
const CARRIER_MARKER: &str = "AXEYUM-CREAL-CARRIER";

/// The two theorems Lean's elaborator refuses and its kernel accepts, by full
/// display name. Named here so the suite fails if the carrier stops carrying
/// them or they stop being representable.
const ELABORATOR_RESIDUE: [&str; 2] = ["CReal.Equiv.not_zero_one", "CReal.not_le_one_zero"];

/// A declaration this kernel calls a `Theorem` whose type is not a `Prop`.
///
/// The classifier must DISCRIMINATE: without a subject on each side, one that
/// had started saying `Representable` to everything — or nothing — would pass
/// this suite silently. `CReal.weierstrassMTest` concludes in
/// `CReal.UniformConvergesOn`, which `creal/uniform_convergence.rs`
/// deliberately makes `Type`-valued.
const NOT_A_PROPOSITION_PIN: &str = "CReal.weierstrassMTest";

/// The monotone floor on how many carrier declarations pinned Lean's kernel
/// must independently admit. It may only RISE; lowering it needs a reason in
/// the commit message.
///
/// Measured 2026-08-30: population 2,045, representable 1,972. Set 72 below,
/// so ordinary churn does not trip it. It is a ratchet against silent
/// shrinkage, not the check — the count equality below is the check.
const REPLAY_FLOOR: usize = 1_900;

/// A scratch directory for the artefacts this suite hands to `lean`.
///
/// **Not** `std::env::temp_dir()`. `/tmp` on the development host is a 62 GB
/// **tmpfs** — RAM — which CLAUDE.md records as a standing contributor to the
/// OOM kills that have ended sessions on this box. A suite that exports the
/// whole checked environment is precisely the one that grows, so it writes
/// where the rest of the repository's scratch goes (`/data0`, as
/// `scripts/lane-snapshot.sh` does). `AXEYUM_SCRATCH_DIR` overrides it, and a
/// host without `/data0` falls back to the temporary directory rather than
/// failing — the fallback is the old behaviour, not a new hazard.
fn scratch_directory(tag: &str) -> PathBuf {
    let name = format!("axeyum_{tag}_{}", std::process::id());
    let roots = [
        std::env::var_os("AXEYUM_SCRATCH_DIR").map(PathBuf::from),
        Some(PathBuf::from("/data0")),
        Some(std::env::temp_dir()),
    ];
    for root in roots.into_iter().flatten() {
        let directory = root.join(&name);
        if std::fs::create_dir_all(&directory).is_ok() {
            return directory;
        }
    }
    panic!("no writable scratch root for {tag}");
}

/// Replay one NDJSON stream through Lean's own kernel.
fn replay(lean: &Path, stream: &str, stem: &str) -> (bool, String) {
    let script = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../scripts/lean/replay-lean4export.lean")
        .canonicalize()
        .expect("the replay script must exist");
    let directory = scratch_directory("creal_replay");
    let file = directory.join(format!("{stem}.ndjson"));
    std::fs::write(&file, stream).expect("write replay stream");
    let output = Command::new(lean)
        .arg("--run")
        .arg(&script)
        .arg(&file)
        .output()
        .expect("run the Lean replay script");
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (output.status.success(), combined)
}

/// The `"in":<n>` index of the name record whose final component is
/// `component`. Names are interned as `(prefix, component)` pairs, so this is
/// how a suite refers to a declaration in the wire format without
/// re-implementing the interner.
fn name_index(stream: &str, component: &str) -> Option<u64> {
    let needle = format!("\"str\":\"{component}\"}}}}");
    let line = stream
        .lines()
        .find(|line| line.starts_with("{\"in\":") && line.ends_with(&needle))?;
    let digits: String = line
        .trim_start_matches("{\"in\":")
        .chars()
        .take_while(char::is_ascii_digit)
        .collect();
    digits.parse().ok()
}

/// The `"value":<n>` of the theorem record declaring name index `name`.
fn theorem_record(stream: &str, name: u64) -> Option<(String, u64)> {
    let marker = format!("\"name\":{name},");
    let line = stream
        .lines()
        .find(|line| line.starts_with("{\"thm\":") && line.contains(&marker))?;
    let tail = line.split_once("\"value\":")?.1;
    let digits: String = tail.chars().take_while(char::is_ascii_digit).collect();
    Some((line.to_owned(), digits.parse().ok()?))
}

/// The `"value":<n>` of the first universe-monomorphic theorem in the stream —
/// a closed proof of *something else*, early enough in the expression index to
/// be in scope wherever it is substituted.
fn first_monomorphic_theorem_value(stream: &str) -> Option<u64> {
    let line = stream
        .lines()
        .find(|line| line.starts_with("{\"thm\":") && line.contains("\"levelParams\":[],"))?;
    let tail = line.split_once("\"value\":")?.1;
    let digits: String = tail.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

/// The constant count the replay script reports it ended with.
fn reported_constants(report: &str) -> Option<usize> {
    let tail = report.split_once("environment now holds ")?.1;
    let digits: String = tail.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

/// Build the carrier and census it.
///
/// `creal` needs 16 MiB of stack in debug (`artifacts/kernel-stack-envelope.tsv`
/// row `debug creal 16777216`) and a `#[test]` thread has 2 MiB, so
/// `build_creal_prelude` aborted here with a SIGABRT before a single Lean ran
/// — for twelve days, while this suite was registered in
/// `scripts/check-lean-gate.sh`. Every entry point below therefore runs inside
/// `on_a_deep_stack`, carried explicitly rather than inherited from an ambient
/// `RUST_MIN_STACK`, which is a gate on one shell.
fn carrier() -> (Kernel, Census) {
    let mut kernel = Kernel::new();
    build_creal_prelude(&mut kernel).expect("the CReal development must build");
    let census = classify(&mut kernel);
    assert!(
        census.population() > REPLAY_FLOOR,
        "the census population is the whole carrier, not a slice: {}",
        census.population()
    );
    (kernel, census)
}

/// The `NameId`s of the representable declarations, for a rooted export.
fn representable_roots(kernel: &Kernel, representable: &BTreeSet<String>) -> Vec<NameId> {
    kernel
        .environment()
        .iter()
        .filter(|(name, _)| representable.contains(&kernel.display_name(**name).to_string()))
        .map(|(name, _)| *name)
        .collect()
}

// ---------------------------------------------------------------------------
// 1. The corrected positive claim.
// ---------------------------------------------------------------------------

#[test]
fn the_real_lean_kernel_accepts_every_representable_declaration_of_the_constructed_real_carrier() {
    on_a_deep_stack(|| {
        let (kernel, census) = carrier();
        let representable = census.representable();

        // Coverage, asserted before any Lean runs: an empty answer from a tool
        // that was never pointed at the subject is indistinguishable from a
        // strong negative result. These two are the reason the carrier-wide
        // replay exists at all.
        for pin in ELABORATOR_RESIDUE {
            assert_eq!(
                census.verdicts.get(pin),
                Some(&Representability::Representable),
                "`{pin}` is one of the two declarations Lean's ELABORATOR refuses and \
                 its kernel accepts. If it is no longer in the representable \
                 population this suite has stopped covering the case it exists for"
            );
        }

        let roots = representable_roots(&kernel, &representable);
        assert_eq!(
            roots.len(),
            representable.len(),
            "every representable name must resolve to exactly one declaration"
        );

        let stream = kernel
            .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &roots)
            .expect("the representable slice must export");

        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 1) else {
            return;
        };

        let (accepted, report) = replay(&lean, &stream, "creal_carrier_representable");
        assert!(
            accepted,
            "the REAL LEAN KERNEL rejected a declaration this census classified as \
             REPRESENTABLE. That is either a non-representability class the classifier \
             does not know or a genuine disagreement between the two kernels; either \
             way it must fail here rather than be narrowed away:\n{report}"
        );
        let held = reported_constants(&report).unwrap_or_else(|| {
            panic!("the replay must report its final constant count:\n{report}")
        });
        assert_eq!(
            held,
            representable.len(),
            "Lean's kernel ended with {held} constants where the representable \
             population is {}. A replay that admits a SUBSET is exactly the \
             reachability hole this suite exists to close:\n{report}",
            representable.len()
        );
        assert!(
            held >= REPLAY_FLOOR,
            "independent-replay floor: {held} < {REPLAY_FLOOR}. This ratchet may only \
             RISE; lowering it needs a reason in the commit message."
        );

        // Printed AFTER the equality, so the line itself is the finding: the two
        // counts are read out of the kernel and out of Lean at run time, never
        // transcribed. `artifacts/facts/` pins this line's SHAPE rather than its
        // numbers, because the carrier grows daily and a pinned population would
        // be red every day for a reason that is not the claim.
        println!(
            "{CARRIER_MARKER} counts_agree population={} representable={} \
             lean_kernel_constants={held} non_representable={}",
            census.population(),
            representable.len(),
            census.residue().len()
        );

        lean_probe::report_checked(TAG, 1);
    });
}

// ---------------------------------------------------------------------------
// 2. The superseded claim, kept as an executable negative control.
// ---------------------------------------------------------------------------

/// **The statement this fact carried until 2026-08-30, refuted by the binary it
/// named.**
///
/// The previous claim was that pinned Lean's kernel accepts the carrier with
/// *no* filter at all. Preserving a corrected statement as prose is what the
/// safety roadmap's S1 asks for; preserving it as a test is stronger, because
/// prose cannot go red the day the correction stops being true in either
/// direction. If Lean ever accepts the unfiltered stream, this test fails and
/// the narrowing must be revisited — which is the outcome ADR-0775's follow-on
/// work is aiming at.
#[test]
fn the_superseded_whole_carrier_claim_is_refuted_by_the_same_binary() {
    on_a_deep_stack(|| {
        let (kernel, census) = carrier();
        let not_prop = census.theorem_type_not_prop();
        assert!(
            !not_prop.is_empty(),
            "this control is aimed at the declarations Lean refuses as theorems; with \
             none, it would pass by refuting nothing"
        );

        let stream = kernel
            .render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("4.30.0"))
            .expect("the whole checked carrier must export");

        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 1) else {
            return;
        };

        let (accepted, report) = replay(&lean, &stream, "creal_carrier_unfiltered");
        assert!(
            !accepted,
            "pinned Lean's kernel accepted the UNFILTERED carrier. That is the \
             superseded claim coming true, not a failure of the development: the \
             correction of 2026-08-30 must then be revisited and this fact widened \
             again:\n{report}"
        );
        let refused = refused_theorem_name(&report).unwrap_or_else(|| {
            panic!(
                "Lean refused the unfiltered carrier for a reason this suite does not \
                 recognise. The narrowing is only honest if the rejection is the \
                 not-a-proposition rule; anything else is an unexamined \
                 finding:\n{report}"
            )
        });
        assert!(
            not_prop.contains(&refused),
            "Lean refused `{refused}`, which THIS kernel classified as \
             {:?}. The typed reason must be earned: the declaration Lean names has to \
             be one the classifier independently excluded, or the census is excluding \
             the wrong things and passing anyway:\n{report}",
            census.verdicts.get(&refused)
        );

        println!(
            "{CARRIER_MARKER} superseded-claim-refuted rejected_by_lean={refused} \
             reason=theorem-type-not-prop theorem_type_not_prop={}",
            not_prop.len()
        );

        lean_probe::report_checked(TAG, 1);
    });
}

// ---------------------------------------------------------------------------
// 3. The negative control on a proof, not a kind.
// ---------------------------------------------------------------------------

/// Lean's kernel must reject the representable stream when
/// `CReal.Equiv.not_zero_one`'s proof is swapped for another closed proof, and
/// name that theorem's own type when it does.
///
/// Without this, "Lean accepted the representable carrier" is consistent with
/// Lean having checked nothing in particular about any declaration in it.
#[test]
fn pinned_lean_rejects_a_substituted_proof_for_the_declaration_the_source_route_cannot_take() {
    on_a_deep_stack(|| {
        let (kernel, census) = carrier();
        let representable = census.representable();
        let roots = representable_roots(&kernel, &representable);
        let stream = kernel
            .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &roots)
            .expect("the representable slice must export");

        let component = "not_zero_one";
        let name = name_index(&stream, component).unwrap_or_else(|| {
            panic!(
                "the export no longer carries `{component}`, so this suite covers \
                 neither declaration the source route cannot take"
            )
        });
        let (record, value) =
            theorem_record(&stream, name).expect("`not_zero_one` must be a theorem record");
        let substitute = first_monomorphic_theorem_value(&stream)
            .expect("the carrier must hold a universe-monomorphic theorem");
        assert_ne!(
            value, substitute,
            "the negative control must substitute a DIFFERENT proof"
        );
        let tampered = stream.replace(
            &record,
            &record.replace(
                &format!("\"value\":{value}"),
                &format!("\"value\":{substitute}"),
            ),
        );
        assert_ne!(tampered, stream, "the negative control must change bytes");

        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 1) else {
            return;
        };

        let (accepted, report) = replay(&lean, &tampered, "creal_carrier_tampered");
        assert!(
            !accepted,
            "the real Lean kernel accepted a mismatched proof for `{component}`; every \
             positive result in this suite is worthless:\n{report}"
        );
        assert!(
            report.contains("REAL LEAN KERNEL REJECTED"),
            "the rejection must come from the kernel: {report}"
        );
        assert!(
            report.contains("CReal.Equiv"),
            "the rejection must name the TYPE it was checking, or it could be any \
             unrelated failure downstream:\n{report}"
        );
        // Added after mutation testing, and it did NOT change that mutation's
        // outcome — recorded as a survivor rather than dressed up as a kill. With
        // `is_a_proposition` forced to `true` the "representable" slice carries all
        // 48 non-proposition theorems, and this test still passed: the tampered
        // `not_zero_one` is refused before Lean reaches any of them, so the pass is
        // honest but says nothing about the classifier. The assertion below states
        // what the control assumes rather than leaving it to stream order — if the
        // export order ever changes, a kind refusal must not be read as a proof
        // refusal.
        assert!(
            refused_theorem_name(&report).is_none(),
            "the rejection is the not-a-proposition rule firing, not the substituted \
             proof being caught. This control is only meaningful when the stream is \
             otherwise acceptable to Lean:\n{report}"
        );

        println!("{CARRIER_MARKER} tampered-proof-rejected subject=CReal.Equiv.not_zero_one");

        lean_probe::report_checked(TAG, 1);
    });
}

// ---------------------------------------------------------------------------
// 4. The residue is typed, counted and named — no Lean required.
// ---------------------------------------------------------------------------

/// **Every declaration outside the replayed population carries one of exactly
/// two typed reasons, and the blocked ones name a real blocker.**
///
/// A narrowed claim is only honest if the thing it excludes is enumerable. This
/// prints all 73, so a reader who never saw the correction can find them in the
/// run rather than in a brief.
#[test]
fn every_non_representable_declaration_carries_a_typed_reason() {
    on_a_deep_stack(|| {
        let (_kernel, census) = carrier();

        // The classifier must discriminate in BOTH directions, or a version that
        // had started answering the same thing to everything would pass silently.
        assert_eq!(
            census.verdicts.get(NOT_A_PROPOSITION_PIN),
            Some(&Representability::TheoremTypeNotProp),
            "`{NOT_A_PROPOSITION_PIN}` concludes in `CReal.UniformConvergesOn`, which \
             `creal/uniform_convergence.rs` deliberately makes `Type`-valued. If this \
             now classifies as representable, either the declaration changed or \
             `is_a_proposition` stopped discriminating"
        );
        assert_eq!(
            census.verdicts.get(ELABORATOR_RESIDUE[0]),
            Some(&Representability::Representable),
            "`{}` is an ordinary `Prop`-valued theorem; if it classifies as \
             non-representable the classifier is over-rejecting",
            ELABORATOR_RESIDUE[0]
        );

        let not_prop = census.theorem_type_not_prop();
        let blocked = census.blocked();
        let residue = census.residue();
        assert!(
            !residue.is_empty(),
            "an empty residue means this suite is guarding a boundary that no longer \
             exists; the superseded whole-carrier claim would then be TRUE and must be \
             restored rather than left narrowed"
        );
        assert_eq!(
            not_prop.len() + blocked.len(),
            residue.len(),
            "the residue must be exactly the two typed classes: {} not-a-proposition + \
             {} blocked against {} non-representable. An untyped exclusion is a \
             declaration nobody has a reason for.",
            not_prop.len(),
            blocked.len(),
            residue.len()
        );

        // Every blocker must itself be a not-a-proposition theorem. Otherwise
        // `BlockedBy` is a second, unexamined exclusion route wearing the first
        // one's name.
        for (name, blocker) in &blocked {
            assert!(
                not_prop.contains(blocker),
                "`{name}` is excluded as blocked by `{blocker}`, which is not itself a \
                 not-a-proposition theorem. The blocked class must bottom out in the \
                 class Lean actually refuses"
            );
        }

        for name in &not_prop {
            println!("{CARRIER_MARKER} residue reason=theorem-type-not-prop name={name}");
        }
        for (name, blocker) in &blocked {
            println!(
                "{CARRIER_MARKER} residue reason=blocked-by-dependency name={name} \
                 blocker={blocker}"
            );
        }
        println!(
            "{CARRIER_MARKER} residue-typed population={} representable={} \
             theorem_type_not_prop={} blocked_by_dependency={} untyped=0",
            census.population(),
            census.representable().len(),
            not_prop.len(),
            blocked.len()
        );
    });
}
