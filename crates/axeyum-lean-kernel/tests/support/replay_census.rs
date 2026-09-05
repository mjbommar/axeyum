//! The **independent-replay census**, shared by every carrier.
//!
//! # What this is
//!
//! ADR-0760 built a census over the constructed reals: take every declaration
//! this kernel admitted, decide which of them pinned Lean's kernel *can* be
//! asked to admit, hand it those, and read back the constant names **Lean's own
//! kernel** ended holding (`replay-lean4export.lean --emit-names`, which dumps
//! `env.constants`). A subject is graded by membership of its own name and by
//! nothing else, so a theorem cannot inherit a grade from a sampled sibling.
//!
//! ADR-1661 generalizes that from one carrier to every carrier the kernel
//! builds. The grading discipline is unchanged and lives here, once, so the two
//! suites cannot drift: `real_lean_replay_census` (the `creal` carrier and its
//! mutation controls) and `real_lean_replay_census_all` (every other carrier).
//!
//! # The typed classes
//!
//! A declaration this kernel admitted is either
//!
//! * **representable** — the wire format carries it and Lean's kernel will
//!   accept its kind, so it must be admitted BY NAME or the census fails;
//! * **`theorem_type_not_prop`** — this kernel admits `Theorem`s whose type is
//!   not a proposition; `Lean.Environment.addDeclCore` refuses a `theorem`
//!   whose type does not live in `Prop`. This is a measured disagreement about
//!   what may be *called* a theorem, not a wire-format limitation and not a
//!   demonstrated soundness hole — but it is a real gap in independent
//!   checkability, so it is a NAMED class and every member is printed;
//! * **`blocked_by_dependency`** — its dependency closure reaches one of those,
//!   so it cannot be exported either. The blocker is named, because "why can
//!   this not go" and "what is it waiting on" are different findings.
//!
//! Nothing here reads a list: the population is `kernel.environment()` and the
//! `Prop`-ness of a type is read from the kernel by inference.
#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use axeyum_lean_kernel::{
    Declaration, ExprId, ExprNode, Kernel, Lean4ExportMetadata, LevelNode, NameId,
};

/// Printed with every count, so a fact or a measurement artifact pins the
/// census by value rather than by a document transcribing it.
pub const CENSUS_MARKER: &str = "AXEYUM-REPLAY-CENSUS";

/// The `lean_version` label written into the export header.
///
/// It is a statement about the **wire format** the stream targets, not about
/// which binary replays it: `Lean4ExportMetadata::axeyum` sets `lean_githash`
/// to `axeyum-lean-kernel` precisely because nothing in the stream came from a
/// Lean binary. Which Lean actually ran is resolved by `lean_probe` from
/// `lean-toolchain` and printed on every `AXEYUM-LEAN-TOOLCHAIN` line.
pub const EXPORT_LEAN_VERSION: &str = "4.30.0";

/// The independent-replay grade of one declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Grade {
    /// Pinned Lean's kernel admitted a constant of exactly this name.
    Replayed,
    /// It did not. Axeyum acceptance is unaffected and stays a separate grade.
    NotReplayed,
}

/// Grade `subject` from the names **Lean's own kernel** ended holding.
///
/// The exit clause lives in this function, so it is deliberately the dullest
/// one here: an exact membership test on `subject` itself. It consults no
/// family, no module, no prefix and no sibling, because every one of those
/// would be a route by which an unchecked theorem inherits a grade from a
/// checked one. `grade_family_by_sampling` does not exist and must not be
/// added.
#[must_use]
pub fn grade(subject: &str, lean_admitted: &BTreeSet<String>) -> Grade {
    if lean_admitted.contains(subject) {
        Grade::Replayed
    } else {
        Grade::NotReplayed
    }
}

/// Why a declaration this kernel admitted cannot be handed to Lean's kernel as
/// what this kernel calls it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Representability {
    /// The wire format carries it and Lean's kernel will accept its kind.
    Representable,
    /// **This kernel admits `Theorem`s whose type is not a proposition; Lean's
    /// kernel does not.** `Lean.Environment.addDeclCore` refuses a `theorem`
    /// whose type does not live in `Prop` — such a thing must be a `def`.
    ///
    /// The affected declarations are deliberate: see
    /// `creal/uniform_convergence.rs`'s module documentation, which explains
    /// why `CReal.UniformConvergesOn` is `Type`-valued (`Exists.rec` cannot
    /// eliminate into `Type`, so the convergence *rate* must be data).
    TheoremTypeNotProp,
    /// Its dependency closure contains a non-representable declaration, so it
    /// cannot be exported either — naming the blocker rather than repeating the
    /// reason, because the two are different findings.
    BlockedBy(String),
}

/// Does `ty` live in `Prop`?
///
/// Read from the kernel by inference, never from a name or a doc comment.
pub fn is_a_proposition(kernel: &mut Kernel, ty: ExprId) -> bool {
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
#[must_use]
pub fn classify(kernel: &mut Kernel) -> BTreeMap<String, Representability> {
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
        let blocker = if bad_names.is_empty() {
            // The closure walk is the expensive half of classification and it
            // can only ever find a member of `bad_names`; with no such member
            // there is nothing to find. This is not a shortcut past a check --
            // `blocked_by_dependency` is empty by construction whenever
            // `theorem_type_not_prop` is.
            None
        } else {
            kernel
                .declaration_dependency_closure(*id)
                .into_iter()
                .map(|dep| kernel.display_name(dep).to_string())
                .find(|dep| bad_names.contains(dep))
        };
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

/// Resolve a display name to its `NameId` in the checked environment.
#[must_use]
pub fn name_of(kernel: &Kernel, display: &str) -> Option<NameId> {
    kernel
        .environment()
        .iter()
        .find(|(name, _)| kernel.display_name(**name).to_string() == display)
        .map(|(name, _)| *name)
}

/// A scratch root that is not `/tmp` — `/tmp` here is a 62 GB tmpfs (RAM) and a
/// standing contributor to OOM kills on this host.
#[must_use]
pub fn scratch_directory(tag: &str) -> PathBuf {
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
#[must_use]
pub fn replay(lean: &Path, stream: &str, stem: &str) -> (bool, String, BTreeSet<String>) {
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

// ---------------------------------------------------------------------------
// The per-carrier census.
// ---------------------------------------------------------------------------

/// One carrier's census result, in the shape the measurement artifact and the
/// per-carrier floor table both read.
#[derive(Debug, Clone)]
pub struct CarrierCensus {
    /// The carrier label, e.g. `nat`.
    pub carrier: String,
    /// Every declaration this kernel admitted.
    pub population: usize,
    /// Those the wire format and Lean's kernel can both take.
    pub representable: usize,
    /// `Theorem`s whose type is not a `Prop`, by name.
    pub theorem_type_not_prop: Vec<String>,
    /// `(declaration, the non-representable declaration it reaches)`.
    pub blocked_by_dependency: Vec<(String, String)>,
    /// Representable declarations pinned Lean admitted under their own name.
    pub replayed: usize,
    /// Representable declarations Lean did NOT admit. Must be empty.
    pub missing: Vec<String>,
    /// Constants Lean holds that this slice did not name. Must be empty.
    pub extra: Vec<String>,
    /// Wall-clock seconds for classification, export and the Lean run.
    pub seconds: f64,
}

impl CarrierCensus {
    /// The one-line summary every run prints, and the artifact quotes.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "{CENSUS_MARKER} carrier={} population={} representable={} \
             theorem_type_not_prop={} blocked_by_dependency={} replayed={} \
             missing={} extra={} seconds={:.1}",
            self.carrier,
            self.population,
            self.representable,
            self.theorem_type_not_prop.len(),
            self.blocked_by_dependency.len(),
            self.replayed,
            self.missing.len(),
            self.extra.len(),
            self.seconds,
        )
    }
}

/// Classify, export and replay one carrier, enforcing `missing == 0`,
/// `extra == 0` and the carrier's monotone replay floor.
///
/// `kernel` must already carry the carrier's build. `floor` is the ratchet: it
/// may only RISE, and lowering one needs a reason in the commit message.
///
/// # Panics
///
/// If Lean rejects a declaration the classifier called representable, if Lean
/// reports no names at all, if anything representable is missing, or if the
/// replayed count is below `floor`. Each of those is a finding, never a skip.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn census_carrier(
    carrier: &str,
    kernel: &mut Kernel,
    lean: &Path,
    floor: usize,
) -> CarrierCensus {
    let started = Instant::now();
    let verdicts = classify(kernel);
    assert!(
        !verdicts.is_empty(),
        "{carrier}: the census population is empty, so a green run here would say \
         nothing -- zero executed subjects is a failure, never a pass"
    );

    let representable: BTreeSet<String> = verdicts
        .iter()
        .filter(|(_, verdict)| **verdict == Representability::Representable)
        .map(|(name, _)| name.clone())
        .collect();
    let theorem_type_not_prop: Vec<String> = verdicts
        .iter()
        .filter(|(_, v)| **v == Representability::TheoremTypeNotProp)
        .map(|(name, _)| name.clone())
        .collect();
    let blocked_by_dependency: Vec<(String, String)> = verdicts
        .iter()
        .filter_map(|(name, v)| match v {
            Representability::BlockedBy(blocker) => Some((name.clone(), blocker.clone())),
            _ => None,
        })
        .collect();

    // The classifier must have a POSITIVE side, or a classifier that had
    // started rejecting everything would satisfy `missing == 0` trivially by
    // exporting nothing.
    assert!(
        !representable.is_empty(),
        "{carrier}: zero representable declarations out of a population of {} -- \
         the classifier is over-rejecting, and a census that exports nothing \
         cannot fail",
        verdicts.len()
    );

    for name in &theorem_type_not_prop {
        println!(
            "{CENSUS_MARKER} carrier={carrier} non-representable \
             reason=theorem-type-not-prop name={name}"
        );
    }
    for (name, blocker) in &blocked_by_dependency {
        println!(
            "{CENSUS_MARKER} carrier={carrier} non-representable \
             reason=blocked-by-dependency name={name} blocker={blocker}"
        );
    }

    let roots: Vec<NameId> = kernel
        .environment()
        .iter()
        .filter(|(name, _)| representable.contains(&kernel.display_name(**name).to_string()))
        .map(|(name, _)| *name)
        .collect();
    assert!(
        !roots.is_empty(),
        "{carrier}: zero representable roots is a failure"
    );

    let stream = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum(EXPORT_LEAN_VERSION), &roots)
        .unwrap_or_else(|error| {
            panic!("{carrier}: the representable slice must export: {error:?}")
        });

    let stem = format!("census_{carrier}");
    let (accepted, report, admitted) = replay(lean, &stream, &stem);
    assert!(
        accepted,
        "{carrier}: pinned Lean's kernel rejected a declaration this census \
         classified as REPRESENTABLE. That is either a new non-representability \
         class the classifier does not know, or a genuine disagreement between \
         the two kernels; either way it must fail here rather than be \
         skipped:\n{report}"
    );
    assert!(
        !admitted.is_empty(),
        "{carrier}: pinned Lean reported no constant names, so nothing was \
         graded:\n{report}"
    );

    let missing: Vec<String> = representable.difference(&admitted).cloned().collect();
    let extra: Vec<String> = admitted.difference(&representable).cloned().collect();
    let replayed = representable
        .iter()
        .filter(|name| grade(name, &admitted) == Grade::Replayed)
        .count();

    let census = CarrierCensus {
        carrier: carrier.to_owned(),
        population: verdicts.len(),
        representable: representable.len(),
        theorem_type_not_prop,
        blocked_by_dependency,
        replayed,
        missing,
        extra,
        seconds: started.elapsed().as_secs_f64(),
    };
    println!("{}", census.summary());

    assert!(
        census.missing.is_empty(),
        "{carrier}: missing={} -- pinned Lean's kernel never admitted a constant \
         of these names, so they hold NO independent-replay grade however many \
         siblings did: {:?}\n{report}",
        census.missing.len(),
        &census.missing[..census.missing.len().min(20)]
    );
    assert!(
        census.extra.is_empty(),
        "{carrier}: extra={} -- Lean holds constants this slice did not name: \
         {:?}\n{report}",
        census.extra.len(),
        &census.extra[..census.extra.len().min(20)]
    );
    assert!(
        census.replayed >= floor,
        "{carrier}: independent-replay floor: {} < {floor}. This ratchet may only \
         RISE; lowering it needs a reason in the commit message.",
        census.replayed
    );
    census
}
