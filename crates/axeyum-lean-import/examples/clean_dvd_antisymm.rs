//! Reconstruct clean divisor-bound and divisibility-antisymmetry supports in r091.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice, import_ndjson,
    verify_checked_theorem_composition,
};
use axeyum_lean_kernel::{
    Declaration, ExprId, Kernel, NameId, NatOps, NatPrelude, NatState, build_nat_prelude,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const TARGET_SHA256: &str = "fc1117679c743009e8548a25d1f73f71f6cd42555ea77b3efce07844673670b2";
const CLEAN_EQ_ZERO_OF_ZERO_DVD: &str = "Axeyum.Autogenesis.eqZeroOfZeroDvdCleanV1";
const CLEAN_LE_OF_DVD: &str = "Axeyum.Autogenesis.leOfDvdCleanV1";
const CLEAN_DVD_ANTISYMM: &str = "Axeyum.Autogenesis.dvdAntisymmCleanV5";
const CLEAN_ZERO_DVD_DEPENDENCIES: [&str; 1] = ["Nat.zero_mul"];
const CLEAN_LE_DEPENDENCIES: [&str; 3] = [
    "Nat.mul_le_mul_left",
    "Nat.mul_one",
    "Nat.one_le_right_of_mul",
];
const CLEAN_ANTISYMM_DEPENDENCIES: [&str; 5] = [
    CLEAN_EQ_ZERO_OF_ZERO_DVD,
    CLEAN_LE_OF_DVD,
    "Nat.le_antisymm",
    "Nat.le_succ_succ",
    "Nat.zero_le",
];
const USAGE: &str = "usage: clean_dvd_antisymm <r091.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("clean-dvd-antisymm: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let target_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    if arguments.next().is_some() {
        return Err(USAGE.to_owned());
    }
    let target = import_bound(&target_path, "target", TARGET_SHA256)?;
    if !target.report().axioms.is_empty() {
        return Err("the exact r091 target stream reaches assumptions".to_owned());
    }

    let mut native = Kernel::new();
    let native_prelude = build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat prelude build failed: {error:?}"))?;
    declare_clean_eq_zero_of_zero_dvd(&mut native, &native_prelude)?;
    let clean_zero_dvd_evidence = theorem_evidence(&native, CLEAN_EQ_ZERO_OF_ZERO_DVD)?;
    require_evidence(
        &clean_zero_dvd_evidence,
        CLEAN_EQ_ZERO_OF_ZERO_DVD,
        &CLEAN_ZERO_DVD_DEPENDENCIES,
    )?;
    duplicate_native_le_of_dvd(&mut native, &native_prelude)?;
    let clean_le_evidence = theorem_evidence(&native, CLEAN_LE_OF_DVD)?;
    require_evidence(&clean_le_evidence, CLEAN_LE_OF_DVD, &CLEAN_LE_DEPENDENCIES)?;
    let clean_antisymm = declare_clean_dvd_antisymm(&mut native, &native_prelude)?;
    let clean_antisymm_evidence = theorem_evidence(&native, CLEAN_DVD_ANTISYMM)?;
    require_evidence(
        &clean_antisymm_evidence,
        CLEAN_DVD_ANTISYMM,
        &CLEAN_ANTISYMM_DEPENDENCIES,
    )?;

    let transported = compose_checked_theorem_slice(
        &native,
        target.kernel(),
        &[
            CLEAN_EQ_ZERO_OF_ZERO_DVD,
            CLEAN_LE_OF_DVD,
            CLEAN_DVD_ANTISYMM,
        ],
    )
    .map_err(|error| format!("clean support transport declined: {error:?}"))?;
    verify_checked_theorem_composition(
        &native,
        target.kernel(),
        transported.kernel(),
        transported.receipt(),
    )
    .map_err(|error| format!("clean support transport did not replay: {error:?}"))?;
    let target_clean_zero_dvd_evidence =
        theorem_evidence(transported.kernel(), CLEAN_EQ_ZERO_OF_ZERO_DVD)?;
    let target_clean_le_evidence = theorem_evidence(transported.kernel(), CLEAN_LE_OF_DVD)?;
    let target_clean_antisymm_evidence =
        theorem_evidence(transported.kernel(), CLEAN_DVD_ANTISYMM)?;
    if target_clean_zero_dvd_evidence != clean_zero_dvd_evidence
        || target_clean_le_evidence != clean_le_evidence
        || target_clean_antisymm_evidence != clean_antisymm_evidence
    {
        return Err("source and r091 support theorem evidence differ".to_owned());
    }

    let output = json!({
        "schema_version": 1,
        "kind": "axeyum-clean-dvd-antisymm-r091-support",
        "state": "single-kernel-clean-supports-transported-to-r091-empty-footprint",
        "input_streams": {"target_sha256": TARGET_SHA256},
        "transport_receipt_sha256": transported.receipt().receipt_sha256,
        "source_theorems": [clean_zero_dvd_evidence, clean_le_evidence, clean_antisymm_evidence],
        "target_theorems": [target_clean_zero_dvd_evidence, target_clean_le_evidence, target_clean_antisymm_evidence],
        "clean_dvd_antisymm_type_sha256": hex_sha256_expression(&native, clean_antisymm)?,
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

fn declare_clean_eq_zero_of_zero_dvd(
    kernel: &mut Kernel,
    prelude: &NatPrelude,
) -> Result<(), String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "eqZeroOfZeroDvdCleanV1"]);
    let state = NatState::new(kernel, *prelude);
    let mut d = Dev { kernel, state };
    d.theorem(target, 1, &|d, values| {
        let n = values[0];
        let zero = d.zero();
        let hypothesis_ty = d.dvd(zero, n);
        let hypothesis_fv = d.fresh_fvar();
        let hypothesis = d.kernel().fvar(hypothesis_fv);
        let goal = d.eq(n, zero);
        let predicate = d.dvd_predicate(zero, n);
        let anon = d.anon_name();
        let motive = d.kernel().lam(
            anon,
            hypothesis_ty,
            goal,
            axeyum_lean_kernel::BinderInfo::Default,
        );
        let minor = {
            let nat = d.nat_ty();
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let product = d.mul(zero, q);
            let witness_ty = d.eq(n, product);
            let witness_fv = d.fresh_fvar();
            let witness = d.kernel().fvar(witness_fv);
            let zero_mul = d.prelude().zero_mul;
            let collapse = d.lemma(zero_mul, &[q]);
            let proof = d.trans(n, product, zero, witness, collapse);
            let with_witness = d.lam_fv(witness_fv, witness_ty, proof);
            d.lam_fv(q_fv, nat, with_witness)
        };
        let one = d.level_one();
        let exists_rec_name = d.prelude().logic.exists_rec;
        let exists_rec = d.kernel().const_(exists_rec_name, vec![one]);
        let nat = d.nat_ty();
        let proof = d.apply(exists_rec, &[nat, predicate, motive, minor, hypothesis]);
        (
            d.arrow(hypothesis_ty, goal),
            d.lam_fv(hypothesis_fv, hypothesis_ty, proof),
        )
    })
    .map(|_| ())
    .map_err(|error| {
        format!(
            "clean zero-divisibility equality rejected: {}",
            d.explain(&error)
        )
    })
}

struct Dev<'k> {
    kernel: &'k mut Kernel,
    state: NatState,
}

impl Dev<'_> {
    fn exact(&mut self, expected: &str) -> Result<NameId, String> {
        find_name(self.kernel, expected)
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
        let eq_zero = self.exact(CLEAN_EQ_ZERO_OF_ZERO_DVD)?;
        let le_antisymm = self.exact("Nat.le_antisymm")?;
        let clean_le = self.exact(CLEAN_LE_OF_DVD)?;
        let zero_le = self.prelude().zero_le;
        let le_succ_succ = self.prelude().le_succ_succ;
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
                d.induct(
                    &|d, candidate_a| d.antisymm_statement(candidate_a, b_succ),
                    &|d| {
                        let forward_ty = d.dvd(zero, b_succ);
                        let reverse_ty = d.dvd(b_succ, zero);
                        d.arrow2_lambdas(forward_ty, reverse_ty, &|d, forward, _reverse| {
                            let b_to_zero = d.lemma(eq_zero, &[b_succ, forward]);
                            Ok(d.symm(b_succ, zero, b_to_zero))
                        })
                        .expect("zero dividend branch is structurally complete")
                    },
                    &|d, a_pred, _a_ih| {
                        let a_succ = d.succ(a_pred);
                        let forward_ty = d.dvd(a_succ, b_succ);
                        let reverse_ty = d.dvd(b_succ, a_succ);
                        d.arrow2_lambdas(forward_ty, reverse_ty, &|d, forward, reverse| {
                            let zero = d.zero();
                            let zero_le_b = d.lemma(zero_le, &[b_pred]);
                            let b_positive = d.lemma(le_succ_succ, &[zero, b_pred, zero_le_b]);
                            let zero_le_a = d.lemma(zero_le, &[a_pred]);
                            let a_positive = d.lemma(le_succ_succ, &[zero, a_pred, zero_le_a]);
                            let a_le_b = d.lemma(clean_le, &[a_succ, b_succ, b_positive, forward]);
                            let b_le_a = d.lemma(clean_le, &[b_succ, a_succ, a_positive, reverse]);
                            Ok(d.lemma(le_antisymm, &[a_succ, b_succ, a_le_b, b_le_a]))
                        })
                        .expect("successor dividend branch is structurally complete")
                    },
                    a,
                )
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
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "dvdAntisymmCleanV5"]);
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
