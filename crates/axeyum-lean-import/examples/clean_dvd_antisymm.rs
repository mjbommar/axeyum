//! Reconstruct clean divisor-bound and divisibility-antisymmetry supports in r091.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, checked_reused_declaration_compatibility,
    compose_checked_theorem_slice, import_ndjson, verify_checked_theorem_composition,
};
use axeyum_lean_kernel::{
    Declaration, ExprId, Kernel, NameId, NatOps, NatPrelude, NatState, build_nat_prelude,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const TARGET_SHA256: &str = "fc1117679c743009e8548a25d1f73f71f6cd42555ea77b3efce07844673670b2";
const OFFICIAL_SHA256: &str = "ff9916e0d74f1a69f7fee33c3b973cd771e6786715b8ea86699da0a8124ae65b";
const OFFICIAL_ROOTS: [&str; 4] = [
    "Eq.symm",
    "Nat.eq_zero_of_zero_dvd",
    "Nat.le_antisymm",
    "Nat.succ_pos",
];
const CLEAN_LE_OF_DVD: &str = "Axeyum.Autogenesis.leOfDvdCleanV1";
const CLEAN_DVD_ANTISYMM: &str = "Axeyum.Autogenesis.dvdAntisymmCleanV1";
const CLEAN_LE_DEPENDENCIES: [&str; 3] = [
    "Nat.mul_le_mul_left",
    "Nat.mul_one",
    "Nat.one_le_right_of_mul",
];
const CLEAN_ANTISYMM_DEPENDENCIES: [&str; 5] = [
    CLEAN_LE_OF_DVD,
    "Eq.symm",
    "Nat.eq_zero_of_zero_dvd",
    "Nat.le_antisymm",
    "Nat.succ_pos",
];
const USAGE: &str = "usage: clean_dvd_antisymm <r091.ndjson> <gcd-roots.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("clean-dvd-antisymm: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let target_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let official_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    if arguments.next().is_some() {
        return Err(USAGE.to_owned());
    }
    let target = import_bound(&target_path, "target", TARGET_SHA256)?;
    let official = import_bound(&official_path, "official-leaves", OFFICIAL_SHA256)?;
    if !target.report().axioms.is_empty() {
        return Err("the exact r091 target stream reaches assumptions".to_owned());
    }
    for root in OFFICIAL_ROOTS {
        let name = find_name(official.kernel(), root)?;
        if !official.kernel().axiom_footprint(name).is_empty() {
            return Err(format!(
                "selected official leaf reaches assumptions: {root}"
            ));
        }
    }

    let (with_official, official_receipt) = compose_or_reuse_official(&official, &target)?;

    let mut native = Kernel::new();
    let native_prelude = build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat prelude build failed: {error:?}"))?;
    duplicate_native_le_of_dvd(&mut native, &native_prelude)?;
    let clean_le_evidence = theorem_evidence(&native, CLEAN_LE_OF_DVD)?;
    require_evidence(&clean_le_evidence, CLEAN_LE_OF_DVD, &CLEAN_LE_DEPENDENCIES)?;

    let with_clean_le = compose_checked_theorem_slice(&native, &with_official, &[CLEAN_LE_OF_DVD])
        .map_err(|error| format!("clean le_of_dvd composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        &native,
        &with_official,
        with_clean_le.kernel(),
        with_clean_le.receipt(),
    )
    .map_err(|error| format!("clean le_of_dvd composition did not replay: {error:?}"))?;

    let mut completed = with_clean_le.kernel().clone();
    let clean_antisymm = declare_clean_dvd_antisymm(&mut completed, &native_prelude)?;
    let clean_antisymm_evidence = theorem_evidence(&completed, CLEAN_DVD_ANTISYMM)?;
    require_evidence(
        &clean_antisymm_evidence,
        CLEAN_DVD_ANTISYMM,
        &CLEAN_ANTISYMM_DEPENDENCIES,
    )?;

    let output = json!({
        "schema_version": 1,
        "kind": "axeyum-clean-dvd-antisymm-r091-support",
        "state": "clean-le-of-dvd-and-divisibility-antisymmetry-reconstructed-empty-footprint",
        "input_streams": {"target_sha256": TARGET_SHA256, "official_leaves_sha256": OFFICIAL_SHA256},
        "official_leaf_transfer": official_receipt,
        "clean_le_of_dvd_composition_receipt_sha256": with_clean_le.receipt().receipt_sha256,
        "theorems": [clean_le_evidence, clean_antisymm_evidence],
        "clean_dvd_antisymm_type_sha256": hex_sha256_expression(&completed, clean_antisymm)?,
        "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
        "exact_target_submissions": 0,
        "target_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&output).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn compose_or_reuse_official(
    official: &axeyum_lean_import::CompletedImport,
    target: &axeyum_lean_import::CompletedImport,
) -> Result<(Kernel, Value), String> {
    let all_present = OFFICIAL_ROOTS
        .iter()
        .all(|root| find_name(target.kernel(), root).is_ok());
    if all_present {
        let mut rows = Vec::new();
        for root in OFFICIAL_ROOTS {
            let receipt =
                checked_reused_declaration_compatibility(official.kernel(), target.kernel(), root)
                    .map_err(|error| {
                        format!("official leaf checked reuse declined for {root}: {error:?}")
                    })?;
            let name = find_name(target.kernel(), root)?;
            if !target.kernel().axiom_footprint(name).is_empty() {
                return Err(format!("reused target leaf reaches assumptions: {root}"));
            }
            rows.push(json!({
                "name": root,
                "source_declaration_sha256": receipt.source_declaration_sha256,
                "target_declaration_sha256": receipt.target_declaration_sha256,
                "compatibility": receipt.compatibility.as_str(),
            }));
        }
        return Ok((
            target.kernel().clone(),
            json!({"mode": "checked-reuse", "rows": rows}),
        ));
    }
    let completed =
        compose_checked_theorem_slice(official.kernel(), target.kernel(), &OFFICIAL_ROOTS)
            .map_err(|error| format!("official clean-leaf composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        official.kernel(),
        target.kernel(),
        completed.kernel(),
        completed.receipt(),
    )
    .map_err(|error| format!("official clean-leaf composition did not replay: {error:?}"))?;
    for theorem in &completed.receipt().added_theorems {
        if !theorem.axiom_footprint.is_empty() {
            return Err(format!(
                "official composition added an assumption-bearing theorem: {}",
                theorem.name
            ));
        }
    }
    Ok((
        completed.kernel().clone(),
        json!({"mode": "composition", "receipt_sha256": completed.receipt().receipt_sha256}),
    ))
}

fn duplicate_native_le_of_dvd(kernel: &mut Kernel, prelude: &NatPrelude) -> Result<(), String> {
    let source = kernel
        .environment()
        .get(prelude.le_of_dvd)
        .cloned()
        .ok_or("native Nat.le_of_dvd disappeared")?;
    let Declaration::Theorem {
        uparams, ty, value, ..
    } = source
    else {
        return Err("native Nat.le_of_dvd is not a theorem".to_owned());
    };
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "leOfDvdCleanV1"]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams,
            ty,
            value,
        })
        .map_err(|error| format!("clean le_of_dvd duplication rejected: {error:?}"))
}

struct Dev<'k> {
    kernel: &'k mut Kernel,
    state: NatState,
}

impl Dev<'_> {
    fn exact(&mut self, expected: &str) -> Result<NameId, String> {
        find_name(self.kernel, expected)
    }

    fn eq_symm_lemma(
        &mut self,
        left: ExprId,
        right: ExprId,
        proof: ExprId,
    ) -> Result<ExprId, String> {
        let name = self.exact("Eq.symm")?;
        let zero = self.kernel.level_zero();
        let theorem = self.kernel.const_(name, vec![zero]);
        let nat = self.nat_ty();
        Ok(self.apply(theorem, &[nat, left, right, proof]))
    }

    fn arrow2_lambdas(
        &mut self,
        first_ty: ExprId,
        second_ty: ExprId,
        body: &dyn Fn(&mut Self, ExprId, ExprId) -> Result<ExprId, String>,
    ) -> Result<ExprId, String> {
        let first_fv = self.fresh_fvar();
        let first = self.kernel.fvar(first_fv);
        let second_fv = self.fresh_fvar();
        let second = self.kernel.fvar(second_fv);
        let result = body(self, first, second)?;
        let with_second = self.lam_fv(second_fv, second_ty, result);
        Ok(self.lam_fv(first_fv, first_ty, with_second))
    }

    fn antisymm_statement(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let forward = self.dvd(a, b);
        let reverse = self.dvd(b, a);
        let equality = self.eq(a, b);
        let with_reverse = self.arrow(reverse, equality);
        self.arrow(forward, with_reverse)
    }

    fn prove_antisymm(&mut self, a: ExprId, b: ExprId) -> Result<ExprId, String> {
        let zero = self.zero();
        let eq_zero = self.exact("Nat.eq_zero_of_zero_dvd")?;
        let le_antisymm = self.exact("Nat.le_antisymm")?;
        let succ_pos = self.exact("Nat.succ_pos")?;
        let clean_le = self.exact(CLEAN_LE_OF_DVD)?;
        Ok(self.induct(
            &|d, candidate_b| d.antisymm_statement(a, candidate_b),
            &|d| {
                let forward_ty = d.dvd(a, zero);
                let reverse_ty = d.dvd(zero, a);
                d.arrow2_lambdas(forward_ty, reverse_ty, &|d, _forward, reverse| {
                    Ok(d.lemma(eq_zero, &[a, reverse]))
                })
                .expect("zero divisibility branch is structurally complete")
            },
            &|d, b_pred, _ih| {
                let b_succ = d.succ(b_pred);
                let forward_ty = d.dvd(a, b_succ);
                let reverse_ty = d.dvd(b_succ, a);
                d.arrow2_lambdas(forward_ty, reverse_ty, &|d, forward, reverse| {
                    let result = d.induct(
                        &|d, candidate_a| d.eq(candidate_a, b_succ),
                        &|d| {
                            let b_to_zero = d.lemma(eq_zero, &[b_succ, forward]);
                            d.eq_symm_lemma(b_succ, zero, b_to_zero)
                                .expect("Eq.symm is present")
                        },
                        &|d, a_pred, _a_ih| {
                            let a_succ = d.succ(a_pred);
                            let b_positive = d.lemma(succ_pos, &[b_pred]);
                            let a_positive = d.lemma(succ_pos, &[a_pred]);
                            let a_le_b = d.lemma(clean_le, &[a_succ, b_succ, b_positive, forward]);
                            let b_le_a = d.lemma(clean_le, &[b_succ, a_succ, a_positive, reverse]);
                            d.lemma(le_antisymm, &[a_succ, b_succ, a_le_b, b_le_a])
                        },
                        a,
                    );
                    Ok(result)
                })
                .expect("successor divisibility branch is structurally complete")
            },
            b,
        ))
    }
}

impl NatOps for Dev<'_> {
    fn kernel(&mut self) -> &mut Kernel {
        self.kernel
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.state
    }
}

fn declare_clean_dvd_antisymm(kernel: &mut Kernel, prelude: &NatPrelude) -> Result<ExprId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "dvdAntisymmCleanV1"]);
    let state = NatState::new(kernel, *prelude);
    let mut d = Dev { kernel, state };
    d.theorem(target, 2, &|d, values| {
        let a = values[0];
        let b = values[1];
        let statement = d.antisymm_statement(a, b);
        let proof = d
            .prove_antisymm(a, b)
            .expect("the preregistered antisymmetry construction is complete");
        (statement, proof)
    })
    .map_err(|error| {
        format!(
            "clean divisibility antisymmetry rejected: {}",
            d.explain(&error)
        )
    })
}

fn theorem_evidence(kernel: &Kernel, expected: &str) -> Result<Value, String> {
    let name = find_name(kernel, expected)?;
    if !matches!(
        kernel.environment().get(name),
        Some(Declaration::Theorem { .. })
    ) {
        return Err(format!("{expected} is not a theorem"));
    }
    let mut footprint = rendered_names(kernel, &kernel.axiom_footprint(name));
    let mut dependencies = rendered_names(kernel, &kernel.theorem_dependencies(name));
    footprint.sort();
    dependencies.sort();
    Ok(json!({
        "name": expected,
        "declaration_sha256": canonical_declaration_sha256(kernel, name)?,
        "axiom_footprint": footprint,
        "direct_theorem_dependencies": dependencies,
    }))
}

fn require_evidence(evidence: &Value, name: &str, dependencies: &[&str]) -> Result<(), String> {
    if evidence["axiom_footprint"] != json!([]) {
        return Err(format!(
            "{name} reaches assumptions: {}",
            evidence["axiom_footprint"]
        ));
    }
    if evidence["direct_theorem_dependencies"] != json!(dependencies) {
        return Err(format!(
            "{name} dependencies changed: {}",
            evidence["direct_theorem_dependencies"]
        ));
    }
    Ok(())
}

fn import_bound(
    path: &Path,
    label: &str,
    expected_sha256: &str,
) -> Result<axeyum_lean_import::CompletedImport, String> {
    let bytes = fs::read(path).map_err(|error| format!("{label} stream read failed: {error}"))?;
    let actual = hex_sha256(&bytes);
    if actual != expected_sha256 {
        return Err(format!(
            "{label} stream identity changed: expected {expected_sha256}, got {actual}"
        ));
    }
    import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("{label} stream import failed: {error:?}"))
}

fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    let matches = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [name] => Ok(*name),
        [] => Err(format!("declaration is absent: {expected}")),
        _ => Err(format!("declaration is ambiguous: {expected}")),
    }
}

fn nested_name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    parts
        .iter()
        .fold(kernel.anon(), |prefix, part| kernel.name_str(prefix, *part))
}

fn rendered_names(kernel: &Kernel, names: &[NameId]) -> Vec<String> {
    names
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect()
}

fn hex_sha256(bytes: &[u8]) -> String {
    let mut digest = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut digest, "{byte:02x}").expect("writing a digest into a String cannot fail");
    }
    digest
}

fn hex_sha256_expression(kernel: &Kernel, expression: ExprId) -> Result<String, String> {
    axeyum_lean_import::canonical_expression_sha256(kernel, expression)
}
