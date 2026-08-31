//! **S4 — independent proof replay, graded per declaration by name.**
//!
//! # What this adds that `real_lean_creal_carrier_kernel_replay` does not
//!
//! That suite proves pinned Lean's kernel accepts the whole constructed-real
//! carrier and ends with **the same NUMBER of constants** this kernel holds.
//! That is a strong statement about the carrier and a weak one about any
//! particular theorem in it. `environment now holds 470 constants` is
//! consistent with a stream in which the declaration a reader cares about was
//! renamed, substituted, or absent while some other declaration made up the
//! total. So no individual fact could honestly cite it: doing so would grade a
//! theorem from its family's aggregate, which is exactly the inheritance
//! ADR-0717's S4 exit forbids.
//!
//! This suite closes that by reading back **the set of constant names Lean's
//! own kernel ended holding** (`replay-lean4export.lean --emit-names`, which
//! dumps `env.constants` — Lean's environment, not our stream) and grading
//! each subject by membership of *its own name*.
//!
//! # The census
//!
//! The subject population is derived from the authority, never from a literal:
//! every declaration in `build_creal_prelude`'s environment. An "every X" test
//! that iterates its own list measures the maintainer's memory, so the only
//! hand-written names here are a small coverage pin (`FLAGSHIP`) whose job is
//! to fail if the census stops covering the theorems it was built for.
//!
//! Reported as `checked / expected / missing / extra`, and **zero executed
//! subjects is a failure**, not a pass.
//!
//! # Why the IVT/EVT family
//!
//! S0's safety matrix reports `independent_replay` at 8/2117 overall and
//! **0/20** across the IVT/EVT rows — the flagship constructive-analysis
//! results. That 0 is what those facts *claim*: `gen-safety-matrix.py` matches
//! `checker_command` text and executes nothing. This suite measures instead.
//!
//! # The three controls
//!
//! 1. **wrong proof** — `CReal.ivt_approx`'s theorem record keeps its type and
//!    gets another closed proof. Lean must reject.
//! 2. **wrong goal** — the same record keeps its proof and gets another
//!    theorem's type. Lean must reject.
//! 3. **no inheritance** — a stream exported from the root `CReal.ivt_step`
//!    alone is replayed; `ivt_step` grades `Replayed` and `ivt_approx`, its
//!    own family member in the same module, grades `NotReplayed`. Lean itself
//!    attests that a sampled sibling confers nothing.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_lean_kernel::{
    Declaration, ExprId, ExprNode, Kernel, Lean4ExportMetadata, LevelNode, NameId,
    build_creal_prelude, on_a_deep_stack,
};

#[path = "support/lean_probe.rs"]
mod lean_probe;

const TAG: &str = "creal-replay-census";

/// Printed with every count, so a fact pins the census by value rather than a
/// document transcribing it.
const CENSUS_MARKER: &str = "AXEYUM-REPLAY-CENSUS";

/// The monotone floor: how many constructed-real declarations pinned Lean's
/// kernel must independently admit **by name**.
///
/// Set below the measured value with headroom, and it may only RISE. It is a
/// ratchet against silent shrinkage of the census, not a target: the suite
/// separately requires `missing == 0` over the representable set, which is the
/// check that cannot be satisfied by admitting fewer things.
///
/// Measured 2026-08-30 on pinned Lean 4.30.0 (`d024af09`), whole `creal`
/// carrier: population 2,045, representable 1,972, `checked=1972 expected=1972
/// missing=0 extra=0`. Floor set at 1,900 -- 72 below the measurement, so
/// ordinary churn does not trip it. RAISING it as the carrier grows is the
/// ratchet working; LOWERING it needs a reason in the commit message.
const REPLAY_FLOOR: usize = 1_900;

/// Coverage pin. These are the theorems this suite was built to grade; if the
/// census stops carrying one, that must fail loudly rather than read as a
/// clean run over a smaller population.
///
/// This is **not** the census population — that is read out of
/// `kernel.environment()`. It is the guard against the census quietly
/// narrowing, which a count-only assertion cannot see.
const FLAGSHIP: [&str; 6] = [
    "CReal.ivt_approx",
    "CReal.ivt_exact_root_decides_sign",
    "CReal.evt_attained_max_decides_sign",
    "CReal.fermat_interiorExtremum",
    "CReal.rolle_interiorExtremum",
    "CReal.mvt_interiorExtremum",
];

/// The independent-replay grade of one declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Grade {
    /// Pinned Lean's kernel admitted a constant of exactly this name.
    Replayed,
    /// It did not. Axeyum acceptance is unaffected and stays a separate grade.
    NotReplayed,
}

/// Grade `subject` from the names **Lean's own kernel** ended holding.
///
/// The S4 exit clause lives in this function, so it is deliberately the
/// dullest one in the file: an exact membership test on `subject` itself. It
/// consults no family, no module, no prefix and no sibling, because every one
/// of those would be a route by which an unchecked theorem inherits a grade
/// from a checked one. `grade_family_by_sampling` does not exist and must not
/// be added.
fn grade(subject: &str, lean_admitted: &BTreeSet<String>) -> Grade {
    if lean_admitted.contains(subject) {
        Grade::Replayed
    } else {
        Grade::NotReplayed
    }
}

/// A scratch root that is not `/tmp` — `/tmp` here is a 62 GB tmpfs (RAM) and a
/// standing contributor to OOM kills on this host.
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

/// Replay one stream through Lean's kernel, returning `(accepted, report,
/// names Lean ended holding)`.
///
/// The name set comes out of a file Lean wrote from `env.constants`, so a name
/// in it was admitted by Lean's kernel rather than merely transmitted by us.
fn replay(lean: &Path, stream: &str, stem: &str) -> (bool, String, BTreeSet<String>) {
    let script = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../scripts/lean/replay-lean4export.lean")
        .canonicalize()
        .expect("the replay script must exist");
    let directory = scratch_directory("replay_census");
    let file = directory.join(format!("{stem}.ndjson"));
    let names_file = directory.join(format!("{stem}.names"));
    std::fs::write(&file, stream).expect("write replay stream");
    // A stale file from an earlier stem would be read as this run's answer.
    let _ = std::fs::remove_file(&names_file);
    let output = Command::new(lean)
        .arg("--run")
        .arg(&script)
        .arg(&file)
        .arg("--emit-names")
        .arg(&names_file)
        .output()
        .expect("run the Lean replay script");
    let report = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let names = std::fs::read_to_string(&names_file)
        .map(|text| {
            text.lines()
                .map(str::trim)
                .filter(|line| !line.is_empty())
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default();
    (output.status.success(), report, names)
}

/// The `"in":<n>` index of the name record whose final component is
/// `component`.
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

/// The whole `{"thm":…}` record declaring name index `name`, with its
/// `"type"` and `"value"` expression indices.
fn theorem_record(stream: &str, name: u64) -> Option<(String, u64, u64)> {
    let marker = format!("\"name\":{name},");
    let line = stream
        .lines()
        .find(|line| line.starts_with("{\"thm\":") && line.contains(&marker))?;
    let field = |key: &str| -> Option<u64> {
        let tail = line.split_once(&format!("\"{key}\":"))?.1;
        let digits: String = tail.chars().take_while(char::is_ascii_digit).collect();
        digits.parse().ok()
    };
    Some((line.to_owned(), field("type")?, field("value")?))
}

/// The `(type, value)` of the first universe-monomorphic theorem in the
/// stream: a closed proof of *something else*, early enough in the expression
/// index to be in scope wherever it is substituted.
fn first_monomorphic_theorem(stream: &str) -> Option<(u64, u64)> {
    let line = stream
        .lines()
        .find(|line| line.starts_with("{\"thm\":") && line.contains("\"levelParams\":[],"))?;
    let field = |key: &str| -> Option<u64> {
        let tail = line.split_once(&format!("\"{key}\":"))?.1;
        let digits: String = tail.chars().take_while(char::is_ascii_digit).collect();
        digits.parse().ok()
    };
    Some((field("type")?, field("value")?))
}

/// Resolve a display name to its `NameId` in the checked environment.
fn name_of(kernel: &Kernel, display: &str) -> Option<NameId> {
    kernel
        .environment()
        .iter()
        .find(|(name, _)| kernel.display_name(**name).to_string() == display)
        .map(|(name, _)| *name)
}

// ---------------------------------------------------------------------------
// The inheritance guard, in the form that needs no Lean.
// ---------------------------------------------------------------------------

/// A family member Lean never saw must not be graded from one it did.
///
/// This is the pure half of the S4 exit clause: the guard on `grade` itself.
/// The half Lean attests to is in
/// `a_family_sibling_lean_never_saw_is_graded_notreplayed`, which runs the same
/// argument end to end against the real kernel.
#[test]
fn grading_consults_only_the_subject_and_never_its_family() {
    let admitted: BTreeSet<String> = ["CReal.ivt_step", "CReal.ivt_iter"]
        .into_iter()
        .map(str::to_owned)
        .collect();

    // Positive control: an admitted name grades, or the negatives below are
    // vacuous — a `grade` that always said `NotReplayed` would pass them all.
    assert_eq!(grade("CReal.ivt_step", &admitted), Grade::Replayed);

    // A sibling in the same family and module, absent from Lean's environment.
    assert_eq!(
        grade("CReal.ivt_approx", &admitted),
        Grade::NotReplayed,
        "a family member Lean never admitted must not inherit its sibling's grade"
    );
    // A PREFIX of an admitted name. Prefix matching is the specific
    // convenience that would silently reintroduce inheritance.
    assert_eq!(grade("CReal.ivt", &admitted), Grade::NotReplayed);
    // A name EXTENDING an admitted one, the same trap in the other direction.
    assert_eq!(grade("CReal.ivt_step_of_le", &admitted), Grade::NotReplayed);
    // The family root itself.
    assert_eq!(grade("CReal", &admitted), Grade::NotReplayed);
}

// ---------------------------------------------------------------------------
// Representability: the typed reasons, decided in THIS kernel, then earned
// against Lean's.
// ---------------------------------------------------------------------------

/// Why a declaration this kernel admitted cannot be handed to Lean's kernel as
/// what this kernel calls it.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Representability {
    /// The wire format carries it and Lean's kernel will accept its kind.
    Representable,
    /// **This kernel admits `Theorem`s whose type is not a proposition; Lean's
    /// kernel does not.** `Lean.Environment.addDeclCore` refuses a `theorem`
    /// whose type does not live in `Prop` — such a thing must be a `def`.
    ///
    /// This is not a wire-format limitation and not a bug in the export. It is
    /// a measured disagreement between two kernels about what may be called a
    /// theorem, and the affected declarations are deliberate: see
    /// `creal/uniform_convergence.rs`'s module documentation, which explains
    /// why `CReal.UniformConvergesOn` is `Type`-valued (`Exists.rec` cannot
    /// eliminate into `Type`, so the convergence *rate* must be data).
    TheoremTypeNotProp,
    /// Its dependency closure contains a non-representable declaration, so it
    /// cannot be exported either — naming the blocker rather than repeating
    /// the reason, because the two are different findings.
    BlockedBy(String),
}

/// Does `ty` live in `Prop`?
///
/// Read from the kernel by inference, never from a name or a doc comment.
fn is_a_proposition(kernel: &mut Kernel, ty: ExprId) -> bool {
    let Ok(sort) = kernel.infer(ty) else {
        return false;
    };
    let sort = kernel.whnf(sort);
    let level = match kernel.expr_node(sort) {
        ExprNode::Sort(level) => *level,
        _ => return false,
    };
    matches!(kernel.level_node(level), LevelNode::Zero)
}

/// Classify every declaration in the checked environment.
///
/// The population is `kernel.environment()`, so this is a complete census and
/// not a sample; nothing here reads a list.
fn classify(kernel: &mut Kernel) -> BTreeMap<String, Representability> {
    let declarations: Vec<(NameId, String, Option<ExprId>)> = kernel
        .environment()
        .iter()
        .map(|(name, decl)| {
            let theorem_type = match decl {
                Declaration::Theorem { ty, .. } => Some(*ty),
                _ => None,
            };
            (*name, kernel.display_name(*name).to_string(), theorem_type)
        })
        .collect();

    // Pass 1: the declarations that are themselves non-representable.
    let mut verdicts: BTreeMap<String, Representability> = BTreeMap::new();
    let mut bad_ids: Vec<NameId> = Vec::new();
    for (id, display, theorem_type) in &declarations {
        if let Some(ty) = *theorem_type
            && !is_a_proposition(kernel, ty)
        {
            verdicts.insert(display.clone(), Representability::TheoremTypeNotProp);
            bad_ids.push(*id);
        }
    }

    // Pass 2: everything whose closure reaches one of those.
    let bad_names: BTreeSet<String> = bad_ids
        .iter()
        .map(|id| kernel.display_name(*id).to_string())
        .collect();
    for (id, display, _) in &declarations {
        if verdicts.contains_key(display) {
            continue;
        }
        let blocker = kernel
            .declaration_dependency_closure(*id)
            .into_iter()
            .map(|dep| kernel.display_name(dep).to_string())
            .find(|dep| bad_names.contains(dep));
        verdicts.insert(
            display.clone(),
            match blocker {
                Some(name) => Representability::BlockedBy(name),
                None => Representability::Representable,
            },
        );
    }
    verdicts
}

// ---------------------------------------------------------------------------
// The census.
// ---------------------------------------------------------------------------

#[test]
#[allow(clippy::too_many_lines)]
// ^ A census test: it enumerates the whole constructed-real surface and
// reports per-declaration verdicts. Splitting it would separate the
// enumeration from the assertions that give it meaning.
fn pinned_lean_independently_admits_every_representable_constructed_real_declaration_by_name() {
    // `creal` needs 16 MiB in debug (`artifacts/kernel-stack-envelope.tsv`) and
    // a `#[test]` thread has 2 MiB, so the prelude build aborts with a SIGABRT
    // that looks exactly like a broken tool. The stack is carried explicitly
    // rather than inherited from an ambient `RUST_MIN_STACK`, which is a gate
    // on one shell.
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        build_creal_prelude(&mut kernel).expect("the CReal development must build");

        let verdicts = classify(&mut kernel);
        assert!(
            verdicts.len() > REPLAY_FLOOR,
            "the census population is the whole carrier, not a slice: {}",
            verdicts.len()
        );

        // Coverage, asserted BEFORE any Lean runs: an empty answer from a tool
        // that was never pointed at the subject is indistinguishable from a
        // strong negative result.
        for pin in FLAGSHIP {
            assert!(
                verdicts.contains_key(pin),
                "the census no longer covers `{pin}`, so a green run here would \
                 say nothing about the theorems it exists to grade"
            );
        }

        // The classifier must DISCRIMINATE. Without both halves, a classifier
        // that had started saying `Representable` to everything -- or nothing
        // -- would pass this suite silently.
        assert_eq!(
            verdicts.get("CReal.weierstrassMTest"),
            Some(&Representability::TheoremTypeNotProp),
            "`CReal.weierstrassMTest` concludes in `CReal.UniformConvergesOn`, \
             which `creal/uniform_convergence.rs` deliberately makes \
             `Type`-valued. If this now classifies as representable, either the \
             declaration changed or `is_a_proposition` stopped discriminating"
        );
        assert_eq!(
            verdicts.get("CReal.ivt_approx"),
            Some(&Representability::Representable),
            "`CReal.ivt_approx` is an ordinary `Prop`-valued theorem; if it \
             classifies as non-representable the classifier is over-rejecting"
        );

        let representable: BTreeSet<String> = verdicts
            .iter()
            .filter(|(_, verdict)| **verdict == Representability::Representable)
            .map(|(name, _)| name.clone())
            .collect();
        let not_prop: Vec<&String> = verdicts
            .iter()
            .filter(|(_, v)| **v == Representability::TheoremTypeNotProp)
            .map(|(name, _)| name)
            .collect();
        let blocked: Vec<&String> = verdicts
            .iter()
            .filter(|(_, v)| matches!(v, Representability::BlockedBy(_)))
            .map(|(name, _)| name)
            .collect();

        println!(
            "{CENSUS_MARKER} population={} representable={} theorem_type_not_prop={} \
             blocked_by_dependency={}",
            verdicts.len(),
            representable.len(),
            not_prop.len(),
            blocked.len()
        );
        for name in &not_prop {
            println!("{CENSUS_MARKER} non-representable reason=theorem-type-not-prop name={name}");
        }
        for name in &blocked {
            let Some(Representability::BlockedBy(blocking_dep)) = verdicts.get(*name) else {
                unreachable!("filtered above")
            };
            println!(
                "{CENSUS_MARKER} non-representable reason=blocked-by-dependency \
                 name={name} blocker={blocking_dep}"
            );
        }

        let roots: Vec<NameId> = kernel
            .environment()
            .iter()
            .filter(|(name, _)| representable.contains(&kernel.display_name(**name).to_string()))
            .map(|(name, _)| *name)
            .collect();
        assert!(!roots.is_empty(), "zero representable roots is a failure");

        let stream = kernel
            .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &roots)
            .expect("the representable slice must export");

        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 2) else {
            return;
        };

        let (accepted, report, admitted) = replay(&lean, &stream, "census_representable");
        assert!(
            accepted,
            "pinned Lean's kernel rejected a declaration this census classified as \
             REPRESENTABLE. That is either a new non-representability class the \
             classifier does not know, or a genuine disagreement between the two \
             kernels; either way it must fail here rather than be skipped:\n{report}"
        );

        // Zero executed subjects is always a failure, never a pass.
        assert!(
            !admitted.is_empty(),
            "pinned Lean reported no constant names, so nothing was graded:\n{report}"
        );

        let missing: Vec<&String> = representable.difference(&admitted).collect();
        let extra: Vec<&String> = admitted.difference(&representable).collect();
        let checked = representable.intersection(&admitted).count();
        println!(
            "{CENSUS_MARKER} checked={checked} expected={} missing={} extra={}",
            representable.len(),
            missing.len(),
            extra.len()
        );
        assert!(
            missing.is_empty(),
            "missing={} -- pinned Lean's kernel never admitted a constant of these \
             names, so they hold NO independent-replay grade however many siblings \
             did: {:?}\n{report}",
            missing.len(),
            &missing[..missing.len().min(20)]
        );
        assert!(
            extra.is_empty(),
            "extra={} -- Lean holds constants this slice did not name: {:?}\n{report}",
            extra.len(),
            &extra[..extra.len().min(20)]
        );

        // Grade each pinned subject INDIVIDUALLY, by its own name.
        for pin in FLAGSHIP {
            let verdict = verdicts.get(pin).expect("pinned above");
            match verdict {
                Representability::Representable => {
                    assert_eq!(
                        grade(pin, &admitted),
                        Grade::Replayed,
                        "`{pin}` is representable but pinned Lean did not admit it \
                         under its own name"
                    );
                    println!("{CENSUS_MARKER} grade subject={pin} axeyum=accepted lean=replayed");
                }
                other => println!(
                    "{CENSUS_MARKER} grade subject={pin} axeyum=accepted \
                     lean=not-representable reason={other:?}"
                ),
            }
        }

        assert!(
            checked >= REPLAY_FLOOR,
            "independent-replay floor: {checked} < {REPLAY_FLOOR}. This ratchet may \
             only RISE; lowering it needs a reason in the commit message."
        );

        lean_probe::report_checked(TAG, 1);
    });
}

/// **The typed reason, earned rather than asserted.**
///
/// `Representability::TheoremTypeNotProp` is a claim about what Lean's kernel
/// will refuse. This checks it: hand Lean the same carrier slice with one
/// not-a-proposition theorem added back, and require the rejection to name that
/// declaration. Without this, the classifier could exclude anything it liked
/// and the census would still be green.
#[test]
fn lean_really_does_refuse_a_theorem_whose_type_is_not_a_proposition() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        build_creal_prelude(&mut kernel).expect("the CReal development must build");
        let verdicts = classify(&mut kernel);

        let subject = "CReal.weierstrassMTest";
        assert_eq!(
            verdicts.get(subject),
            Some(&Representability::TheoremTypeNotProp),
            "this control is aimed at a declaration the classifier excludes for \
             THIS reason; if it no longer does, re-aim it"
        );
        let root = name_of(&kernel, subject).expect("the subject must be declared");

        let stream = kernel
            .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[root])
            .expect("the wire format carries it -- the refusal is Lean's, not ours");

        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 1) else {
            return;
        };

        let (accepted, report, _) = replay(&lean, &stream, "census_not_prop");
        assert!(
            !accepted,
            "pinned Lean ACCEPTED `{subject}` as a theorem. The census excludes it \
             on the stated ground that Lean refuses it, so if Lean does not, the \
             exclusion is unjustified and the census is understating what \
             replays:\n{report}"
        );
        assert!(
            report.contains("REAL LEAN KERNEL REJECTED"),
            "the refusal must come from Lean's kernel, not a parse error:\n{report}"
        );
        assert!(
            report.contains("is not a proposition"),
            "the refusal must be for the REASON the census records, not some other \
             failure that happens to also reject:\n{report}"
        );
        assert!(
            report.contains(subject),
            "the refusal must name `{subject}`:\n{report}"
        );
        println!(
            "{CENSUS_MARKER} typed-reason-earned subject={subject} \
             reason=theorem-type-not-prop lean=rejected"
        );

        lean_probe::report_checked(TAG, 1);
    });
}

// ---------------------------------------------------------------------------
// Controls: wrong proof, wrong goal, no inheritance.
// ---------------------------------------------------------------------------

#[test]
fn pinned_lean_rejects_a_wrong_proof_and_a_wrong_goal_for_the_flagship_theorem() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        build_creal_prelude(&mut kernel).expect("the CReal development must build");
        let root = name_of(&kernel, "CReal.ivt_approx").expect("`CReal.ivt_approx` must exist");
        let stream = kernel
            .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[root])
            .expect("the flagship closure must export");

        // Resolved before any Lean runs, so a stream that stopped carrying the
        // subject fails here rather than passing as "nothing to check".
        let subject = name_index(&stream, "ivt_approx")
            .expect("the export must carry `ivt_approx`, or these controls check nothing");
        let (record, goal, proof) =
            theorem_record(&stream, subject).expect("`ivt_approx` must be a theorem record");
        let (other_goal, other_proof) = first_monomorphic_theorem(&stream)
            .expect("the closure must hold a universe-monomorphic theorem");
        assert_ne!(
            proof, other_proof,
            "the control must substitute a DIFFERENT proof"
        );
        assert_ne!(
            goal, other_goal,
            "the control must substitute a DIFFERENT goal"
        );

        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 3) else {
            return;
        };

        // Positive control first: the UNMODIFIED closure must be accepted, or
        // the two rejections below are consistent with a stream Lean refuses
        // for some unrelated reason.
        let (accepted, report, admitted) = replay(&lean, &stream, "census_flagship_clean");
        assert!(
            accepted,
            "pinned Lean must accept the unmodified flagship closure:\n{report}"
        );
        assert_eq!(
            grade("CReal.ivt_approx", &admitted),
            Grade::Replayed,
            "the flagship must be admitted under its own name:\n{report}"
        );

        // (1) wrong proof: the flagship's own statement, someone else's proof.
        let wrong_proof = stream.replace(
            &record,
            &record.replace(
                &format!("\"value\":{proof}"),
                &format!("\"value\":{other_proof}"),
            ),
        );
        assert_ne!(
            wrong_proof, stream,
            "the wrong-proof control must change bytes"
        );
        let (accepted, report, _) = replay(&lean, &wrong_proof, "census_wrong_proof");
        assert!(
            !accepted,
            "pinned Lean's kernel ACCEPTED a wrong proof for `CReal.ivt_approx`; \
             every positive verdict in this file is worthless:\n{report}"
        );
        assert!(
            report.contains("REAL LEAN KERNEL REJECTED"),
            "the rejection must come from the kernel, not a parse error:\n{report}"
        );

        // (2) wrong goal: the flagship's own proof, someone else's statement.
        let wrong_goal = stream.replace(
            &record,
            &record.replace(
                &format!("\"type\":{goal}"),
                &format!("\"type\":{other_goal}"),
            ),
        );
        assert_ne!(
            wrong_goal, stream,
            "the wrong-goal control must change bytes"
        );
        assert_ne!(
            wrong_goal, wrong_proof,
            "the two controls must be different streams, or only one was tested"
        );
        let (accepted, report, _) = replay(&lean, &wrong_goal, "census_wrong_goal");
        assert!(
            !accepted,
            "pinned Lean's kernel ACCEPTED `CReal.ivt_approx`'s proof against a \
             DIFFERENT goal, so the replay does not check what the theorem \
             says:\n{report}"
        );
        assert!(
            report.contains("REAL LEAN KERNEL REJECTED"),
            "the rejection must come from the kernel, not a parse error:\n{report}"
        );

        lean_probe::report_checked(TAG, 3);
    });
}

/// **The S4 exit clause, attested by Lean rather than by a unit test.**
///
/// Export the closure of `CReal.ivt_step` alone and replay it. `ivt_step` is
/// `ivt_approx`'s own ancestor in the same family and the same module, so if a
/// sampled family conferred a grade, this run would confer one. It does not:
/// Lean's environment simply does not contain `CReal.ivt_approx`.
#[test]
fn a_family_sibling_lean_never_saw_is_graded_notreplayed() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        build_creal_prelude(&mut kernel).expect("the CReal development must build");

        let sampled =
            name_of(&kernel, "CReal.ivt_step").expect("`CReal.ivt_step` must be declared");
        let sibling = "CReal.ivt_approx";
        assert!(
            name_of(&kernel, sibling).is_some(),
            "the sibling must be a real declaration THIS kernel accepted, or the \
             guard compares against nothing: the point is that Axeyum acceptance \
             and Lean acceptance are separate grades"
        );

        let stream = kernel
            .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[sampled])
            .expect("the sampled root must export");

        let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 1) else {
            return;
        };

        let (accepted, report, admitted) = replay(&lean, &stream, "census_sampled_family");
        assert!(
            accepted,
            "pinned Lean must accept the sampled closure, or this guard proves \
             nothing about grading:\n{report}"
        );

        // Positive half: the sampled member really was checked. Without this the
        // negative half is satisfied by a replay that checked nothing.
        assert_eq!(
            grade("CReal.ivt_step", &admitted),
            Grade::Replayed,
            "the sampled root itself must be admitted:\n{report}"
        );

        // Negative half: its family member is NOT graded, though every heuristic
        // a convenience might use -- same prefix, same module, same family, same
        // source file, reachable in one step -- would say it should be.
        assert_eq!(
            grade(sibling, &admitted),
            Grade::NotReplayed,
            "`{sibling}` inherited a replay grade from a sampled sibling. Lean's \
             environment holds {} constants and this is not one of them:\n{report}",
            admitted.len()
        );
        println!(
            "{CENSUS_MARKER} inheritance-guard sampled=CReal.ivt_step admitted={} \
             sibling={sibling} grade=not-replayed",
            admitted.len()
        );

        lean_probe::report_checked(TAG, 1);
    });
}
