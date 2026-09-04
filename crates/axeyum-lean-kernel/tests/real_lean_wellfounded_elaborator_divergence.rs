//! The **named, bounded incompatibility** between the two routes by which real
//! Lean reads our exported bytes: Lean's *kernel* unfolds a `theorem` while
//! reducing, and Lean's *elaborator* does not.
//!
//! # What this suite pins, and why it is not an alarm
//!
//! On 2026-08-18 a lane rooting the shared prelude module at the whole
//! constructed-real carrier found that Lean 4.30.0 REFUSED the emitted file at
//! `CReal.Equiv.not_zero_one` and `CReal.not_le_one_zero`, with
//! `Application type mismatch` followed by `internal exception #3`, while the
//! in-tree kernel admits both. Three explanations were possible and they are
//! distinguishable:
//!
//! 1. our kernel is more permissive than Lean's — a soundness defect;
//! 2. the renderer emits bytes that do not say what the checked term says;
//! 3. a genuine incompatibility, which then has to be named and bounded.
//!
//! It is (3), and this suite is the naming. Lean has **two** entry points and
//! only one of them is its kernel:
//!
//! * `lean Module.lean` runs the **elaborator** over surface syntax. Its
//!   reducer (`Meta.whnf`, default transparency) treats a `theorem` as opaque:
//!   proofs are not unfolded, because proof irrelevance normally makes it
//!   unnecessary.
//! * `Lean.Environment.addDeclCore`, which
//!   `scripts/lean/replay-lean4export.lean` drives from our official
//!   `lean4export` NDJSON, runs the **kernel**, which unfolds anything holding
//!   a value.
//!
//! That difference is invisible until a proof has to *compute* through another
//! proof. `Nat.gcd` is `WellFounded.fix` over the definition
//! `Nat.lt_well_founded`, and its Euclidean descent is justified by the
//! **theorem** `Nat.mod_lt`; to take one recursive step the reducer must put
//! that theorem's proof in constructor form. `CReal.Equiv.not_zero_one` closes
//! by computing a closed `Rat.le` down to `Nat.le 1 0`, every closed `Rat` is
//! normalized, and `Rat.normalize` calls `Nat.gcd` — so the refusal reaches the
//! reals from the ℕ prelude, and this suite reproduces it there, with no
//! `CReal` in sight.
//!
//! # The four checks
//!
//! | module | route | verdict |
//! | --- | --- | --- |
//! | `Nat.mod 4 2 = 0` (structural recursion) | elaborator | accepted |
//! | `Nat.gcd 2 4 = 2` (well-founded recursion) | elaborator | **REJECTED** |
//! | the same gcd module, every `theorem` re-spelled `def` | elaborator | **REJECTED** (same mismatch) |
//! | the development as NDJSON | **kernel** | accepted |
//!
//! Row 3 was WRITTEN on 2026-08-18 as "accepted", isolating the mechanism to a
//! single token per line. Measured on 2026-09-03 against both Lean 4.30.0 and
//! 4.34.0-rc1, it is refused with the same type mismatch: the keyword is not
//! the mechanism. The elaborator's reducer does not take the `WellFounded.fix`
//! step through `Acc.rec` at default transparency at all, and the kernel does
//! (row 4). The residue is therefore keyword-independent -- any declaration
//! whose type-checking must reduce through `Acc.rec` -- which is a stronger
//! statement of the same boundary, and ADR-0517 records the correction. Row 1 rules out "closed arithmetic is too
//! expensive" — `Nat.mod` is the recursive step of the very Euclidean descent
//! `gcd` runs. Measured the same way on 2026-08-18: `Nat.gcd 0 3 = 3` (the base
//! case, no recursive step) is *accepted*, every `gcd` needing at least one
//! recursive step is refused, and so is
//! `Rat.num (Rat.natDivSucc 1 1) = Int.ofNat 1`.
//!
//! # What would make this suite fail, and what that would mean
//!
//! * The elaborator ACCEPTS the `theorem` spelling — a newer Lean closed the
//!   gap, or the prelude stopped defining `gcd` this way. The residue recorded
//!   in ADR-0517 shrank and the ADR is stale.
//! * The elaborator ACCEPTS the `def` spelling — a newer Lean reduces through
//!   `Acc.rec` at default transparency; re-measure the residue.
//! * The kernel REJECTS either probe — that is explanation (1) or (2) after
//!   all, and it is a soundness-relevant defect rather than a routing note.
//!
//! Lean is optional locally and mandatory under `AXEYUM_REQUIRE_LEAN=1`, like
//! the other cross-checks in this crate.

use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_lean_kernel::{
    Declaration, ExprId, Kernel, Lean4ExportMetadata, LogicPrelude, NatPrelude,
    build_logic_prelude, build_nat_prelude,
};

#[path = "support/lean_probe.rs"]
mod lean_probe;

const TAG: &str = "wellfounded-elaborator-divergence";

/// The well-founded probe's theorem name, carried by both routes so a failure
/// names the same thing twice.
const GCD_THEOREM: &str = "axeyum_gcd_reduces";

/// The structural-recursion control's theorem name.
const MOD_THEOREM: &str = "axeyum_mod_reduces";

/// A ℕ development plus the two probe theorems, and the goal/proof pair for
/// each so the source route can render them.
struct Probes {
    kernel: Kernel,
    gcd: (ExprId, ExprId),
    control: (ExprId, ExprId),
}

/// `Nat.succ^n Nat.zero`.
fn numeral(kernel: &mut Kernel, nat: &NatPrelude, n: usize) -> ExprId {
    let mut e = kernel.const_(nat.zero, vec![]);
    for _ in 0..n {
        let succ = kernel.const_(nat.succ, vec![]);
        e = kernel.app(succ, e);
    }
    e
}

/// `Eq.{1} Nat lhs rhs` together with `@Eq.refl.{1} Nat lhs`.
///
/// The proof is reflexivity **on the left-hand side**, so admitting the
/// declaration is exactly the claim that `lhs` and `rhs` are definitionally
/// equal — which is the property the two routes disagree about, stated as a
/// declaration rather than as a tactic.
fn refl_claim(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    nat: &NatPrelude,
    lhs: ExprId,
    rhs: ExprId,
) -> (ExprId, ExprId) {
    let one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let nat_ty = kernel.const_(nat.nat, vec![]);
    let eq = kernel.const_(logic.eq, vec![one]);
    let goal = kernel.app(eq, nat_ty);
    let goal = kernel.app(goal, lhs);
    let goal = kernel.app(goal, rhs);
    let refl = kernel.const_(logic.eq_refl, vec![one]);
    let proof = kernel.app(refl, nat_ty);
    let proof = kernel.app(proof, lhs);
    (goal, proof)
}

fn probes() -> Probes {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let nat = build_nat_prelude(&mut kernel).expect("nat prelude must build");
    let anonymous = kernel.anon();

    // `Nat.gcd 2 4 = 2` -- gcd is `WellFounded.fix` whose descent is justified
    // by the THEOREM `Nat.mod_lt`.
    let two = numeral(&mut kernel, &nat, 2);
    let four = numeral(&mut kernel, &nat, 4);
    let gcd = kernel.const_(nat.gcd, vec![]);
    let gcd_applied = kernel.app(gcd, two);
    let gcd_applied = kernel.app(gcd_applied, four);
    let gcd_pair = refl_claim(&mut kernel, &logic, &nat, gcd_applied, two);
    let gcd_name = kernel.name_str(anonymous, GCD_THEOREM);
    kernel
        .add_declaration(Declaration::Theorem {
            name: gcd_name,
            uparams: Vec::new(),
            ty: gcd_pair.0,
            value: gcd_pair.1,
        })
        .expect("this kernel must reduce Nat.gcd 2 4 to 2");

    // `Nat.mod 4 2 = 0` -- the structural-recursion control, and the step
    // `Nat.gcd`'s own Euclidean descent takes.
    let zero = kernel.const_(nat.zero, vec![]);
    let modulo = kernel.const_(nat.mod_, vec![]);
    let mod_applied = kernel.app(modulo, four);
    let mod_applied = kernel.app(mod_applied, two);
    let mod_pair = refl_claim(&mut kernel, &logic, &nat, mod_applied, zero);
    let mod_name = kernel.name_str(anonymous, MOD_THEOREM);
    kernel
        .add_declaration(Declaration::Theorem {
            name: mod_name,
            uparams: Vec::new(),
            ty: mod_pair.0,
            value: mod_pair.1,
        })
        .expect("this kernel must reduce Nat.mod 4 2 to 0");

    Probes {
        kernel,
        gcd: gcd_pair,
        control: mod_pair,
    }
}

/// The same module with every `theorem` command re-spelled as `def`.
///
/// Nothing else changes — not one character of any term — so a verdict that
/// moves under this rewrite is a verdict about the KEYWORD, which is to say
/// about whether Lean's reducer is allowed to unfold a proof.
fn theorems_as_defs(source: &str) -> String {
    let rewritten: String = source
        .lines()
        .map(|line| match line.strip_prefix("theorem ") {
            Some(rest) => format!("def {rest}\n"),
            None => format!("{line}\n"),
        })
        .collect();
    assert_ne!(rewritten, source, "the rewrite must change bytes");
    rewritten
}

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

/// Run `lean` over one rendered module and return `(accepted, output)`.
fn elaborate(lean: &Path, source: &str, stem: &str) -> (bool, String) {
    let directory = scratch_directory("wf_divergence");
    let file = directory.join(format!("{stem}.lean"));
    std::fs::write(&file, source).expect("write module");
    let output = Command::new(lean)
        .arg("--root")
        .arg(&directory)
        .arg(&file)
        .output()
        .expect("run lean over the module");
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (output.status.success(), combined)
}

/// Replay one NDJSON stream through Lean's own kernel.
fn replay(lean: &Path, stream: &str, stem: &str) -> (bool, String) {
    let script = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../scripts/lean/replay-lean4export.lean")
        .canonicalize()
        .expect("the replay script must exist");
    let directory = scratch_directory("wf_divergence");
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

#[test]
fn leans_kernel_unfolds_a_theorem_while_reducing_and_leans_elaborator_does_not() {
    let probes = probes();
    let gcd_module =
        probes
            .kernel
            .render_lean_module_compact(GCD_THEOREM, probes.gcd.0, probes.gcd.1);
    let control_module =
        probes
            .kernel
            .render_lean_module_compact(MOD_THEOREM, probes.control.0, probes.control.1);
    // The two modules must actually differ in the recursion they exercise, or
    // the table below compares a module with itself.
    assert!(
        gcd_module.contains("WellFounded.fix"),
        "the gcd module must exercise well-founded recursion"
    );
    assert!(
        !control_module.contains("WellFounded.fix"),
        "the `mod` control must NOT exercise well-founded recursion, or it is not a control"
    );
    let gcd_as_defs = theorems_as_defs(&gcd_module);

    let stream = probes
        .kernel
        .render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("4.30.0"))
        .expect("the checked development must export");
    assert!(
        stream.contains(GCD_THEOREM) && stream.contains(MOD_THEOREM),
        "the replay stream must carry BOTH probes, or the kernel half covers nothing"
    );

    let Some(lean) = lean_probe::lean_bin_or_skip(TAG, 4) else {
        return;
    };

    // 1. The elaborator, structural recursion: accepted.
    let (accepted, report) = elaborate(&lean, &control_module, "AxeyumModControl");
    assert!(
        accepted,
        "Lean's elaborator rejected the STRUCTURAL-recursion control, so the \
         gcd rejection below is not about well-founded recursion:\n{report}"
    );

    // 2. The elaborator, well-founded recursion: rejected, and rejected for the
    //    documented reason. A bare `!accepted` would also be satisfied by a
    //    parse error or a missing constant.
    let (accepted, report) = elaborate(&lean, &gcd_module, "AxeyumGcdProbe");
    assert!(
        !accepted,
        "Lean's ELABORATOR now accepts a reduction through a `theorem` that this \
         repository records it as refusing (ADR-0517). That is good news and this \
         suite is stale: re-measure the residue and update the ADR.\n{report}"
    );
    assert!(
        report.contains("Type mismatch") || report.contains("type mismatch"),
        "the elaborator must refuse with a TYPE MISMATCH -- any other refusal is \
         a different defect and must not be read as this one:\n{report}"
    );
    assert!(
        report.contains("gcd"),
        "the refusal must name the well-founded definition:\n{report}"
    );

    // 3. The SAME module, every `theorem` re-spelled `def`: accepted. One token
    //    per line is the entire difference, which is what makes the mechanism a
    //    measurement rather than a story.
    let (accepted, report) = elaborate(&lean, &gcd_as_defs, "AxeyumGcdProbeAsDefs");
    // MEASURED 2026-09-03, on BOTH Lean 4.30.0 (d024af09) and 4.34.0-rc1
    // (3447a668): the elaborator refuses this module too, with the SAME type
    // mismatch at the same `Eq.refl`. So the mechanism is NOT the opacity of
    // `theorem`: `Meta.whnf` does not take the `WellFounded.fix` step through
    // `Acc.rec` at default transparency whatever keyword the proofs carry,
    // while the kernel (step 4) does. ADR-0517's "one token per line" story
    // was written from the CReal-carrier measurement and never had this row
    // run against a real binary: this suite was not in any gate until
    // 2026-09-03 and had asserted `accepted` here since 2026-08-18. The ADR
    // carries the correction. What the row now pins is that the refusal is
    // keyword-independent, which is the stronger statement of the residue.
    assert!(
        !accepted,
        "Lean's elaborator now ACCEPTS the well-founded reduction with every proof \
         spelled `def`, so a newer Lean unfolds through `Acc.rec` at default \
         transparency and ADR-0517's residue has shrunk. Re-measure the `theorem` \
         spelling and the CReal carrier, then update the ADR:\n{report}"
    );
    assert!(
        report.contains("Type mismatch") || report.contains("type mismatch"),
        "the `def` spelling must be refused with the SAME type mismatch as the \
         `theorem` spelling -- any other refusal is a different defect:\n{report}"
    );

    // 4. Lean's KERNEL, over the same two theorems: accepted. This is the half
    //    that says our kernel is not more permissive than Lean's.
    let (accepted, report) = replay(&lean, &stream, "probes");
    assert!(
        accepted,
        "the REAL LEAN KERNEL rejected a development this kernel admitted. That is \
         not a routing note, it is a soundness-relevant divergence:\n{report}"
    );
    assert!(
        report.contains("the real Lean kernel accepted"),
        "the replay must report what it admitted: {report}"
    );

    lean_probe::report_checked(TAG, 4);
}
