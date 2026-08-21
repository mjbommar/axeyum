//! Reconstruct exact `Nat.gcd_fib_add_self` from four sealed proof capsules.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, canonical_expression_sha256,
    compose_checked_theorem_slice, import_ndjson, verify_checked_theorem_composition,
};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, Lean4ExportMetadata, LevelId, NameId,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const R091_SHA256: &str = "fc1117679c743009e8548a25d1f73f71f6cd42555ea77b3efce07844673670b2";
const GOAL_DEFINITION: &str = "Axeyum.Autogenesis.Coverage.r091";
const GOAL_SHA256: &str = "297c9f4af4d63eff354223f9548ab1d4dd3d7e52aa701e88802d58b7929a1451";
const TARGET: &str = "Nat.gcd_fib_add_self";
const CLEAN_ANTISYMM: &str = "Axeyum.Autogenesis.dvdAntisymmCleanV5";
const CLEAN_ANTISYMM_CAPSULE: &str =
    "d3b881ce30488b188bb4f557afc125418fdc21f5707b233a00934c9c97faa434";
const CANCELLATION: &str = "Axeyum.Autogenesis.officialCoprimeFactorDivisibilityCancellationV1";
const CANCELLATION_BOOTSTRAP: &str = "Nat.mod_lt";
const CANCELLATION_CAPSULE: &str =
    "6f9a3983ba4b0e7b2c872615d796ceb5414d3bd2cf51843ecb496b3ba83a52b0";
const ADDITION: &str = "Axeyum.Autogenesis.NatFibSuccessorAddition";
const ADDITION_CAPSULE: &str = "f46e3dd4053c930984b3232ff98320021daa2fcdb3451e84bfbf011945a18621";
const COPRIME: &str = "Nat.fib_coprime_fib_succ";
const COPRIME_CAPSULE: &str = "9106a3442d75a5fdaf51e35436e6fdbea78714d743e666bec27ffd9641160b11";
const CLEAN_GCD_COMM: &str = "Axeyum.Autogenesis.gcdCommCleanV1";
const OFFICIAL_EQ_ZERO: &str = "Axeyum.Autogenesis.eqZeroOfZeroDvdOfficialV1";
const OFFICIAL_LE_OF_DVD: &str = "Axeyum.Autogenesis.leOfDvdOfficialV1";
const OFFICIAL_ANTISYMM: &str = "Axeyum.Autogenesis.dvdAntisymmOfficialV1";
const USAGE: &str = "usage: nat_gcd_fib_add_self_exact <r091> <clean-order> <cancellation> <addition> <coprimality>";

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-gcd-fib-add-self-exact: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() == Some(std::ffi::OsStr::new("--official-clean-order-capsule")) {
        return run_official_clean_order_capsule(args);
    }
    let mut args = std::env::args_os().skip(1);
    let r091_path = path(&mut args)?;
    let capsules = [
        (CLEAN_ANTISYMM, path(&mut args)?, CLEAN_ANTISYMM_CAPSULE),
        (CANCELLATION, path(&mut args)?, CANCELLATION_CAPSULE),
        (ADDITION, path(&mut args)?, ADDITION_CAPSULE),
        (COPRIME, path(&mut args)?, COPRIME_CAPSULE),
    ];
    if args.next().is_some() {
        return Err(USAGE.to_owned());
    }
    let imported = import_bound(&r091_path, R091_SHA256, "r091")?;
    if !imported.report().axioms.is_empty() {
        return Err("r091 is not proof-isolated".to_owned());
    }
    let mut kernel = imported.kernel().clone();
    let mut receipts = Vec::new();
    for (root, source_path, expected_sha256) in capsules {
        let source = import_bound(&source_path, expected_sha256, root)?;
        if !source.report().axioms.is_empty() {
            return Err(format!("{root} capsule is not proof-isolated"));
        }
        let completed = compose_checked_theorem_slice(source.kernel(), &kernel, &[root])
            .map_err(|error| format!("{root} composition declined: {error:?}"))?;
        verify_checked_theorem_composition(
            source.kernel(),
            &kernel,
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("{root} composition did not replay: {error:?}"))?;
        if completed
            .receipt()
            .added_theorems
            .iter()
            .any(|row| !row.axiom_footprint.is_empty())
        {
            return Err(format!(
                "{root} composition added an assumption-bearing theorem"
            ));
        }
        receipts.push(json!({
            "root": root,
            "receipt_sha256": completed.receipt().receipt_sha256,
            "source_closure": completed.receipt().source_closure.len(),
            "added_theorems": completed.receipt().added_theorems.len(),
            "added_definitions": completed.receipt().added_definitions.len(),
            "added_singleton_inductives": completed.receipt().added_singleton_inductives.len(),
        }));
        kernel = completed.kernel().clone();
    }
    let goal_name = find_name(&kernel, GOAL_DEFINITION)?;
    let goal = match kernel.environment().get(goal_name) {
        Some(Declaration::Definition { value, .. }) => *value,
        _ => return Err("r091 goal carrier is not a definition".to_owned()),
    };
    let goal_sha256 = canonical_expression_sha256(&kernel, goal)?;
    if goal_sha256 != GOAL_SHA256 {
        return Err(format!("r091 goal identity changed: {goal_sha256}"));
    }
    let comm = declare_clean_gcd_comm(&mut kernel)?;
    require_empty(&kernel, comm, CLEAN_GCD_COMM)?;
    let theorem = declare_target(&mut kernel, goal)?;
    require_empty(&kernel, theorem, TARGET)?;
    let proof = match kernel.environment().get(theorem) {
        Some(Declaration::Theorem { value, .. }) => *value,
        _ => return Err("exact target is not a theorem".to_owned()),
    };
    let transitive = transitive_dependencies(&kernel, theorem);
    for root in [CLEAN_ANTISYMM, CANCELLATION, ADDITION, COPRIME] {
        if !transitive.iter().any(|name| name == root) {
            return Err(format!(
                "exact target is independent of required root {root}"
            ));
        }
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-autogenesis-nat-gcd-fib-add-self-exact-candidate",
            "state": "exact-target-reconstructed-empty-footprint",
            "target_stream_sha256": R091_SHA256,
            "capsule_compositions": receipts,
            "local_gcd_comm": evidence(&kernel, comm)?,
            "target": {
                "name": TARGET,
                "target_goal_sha256": goal_sha256,
                "proof_sha256": canonical_expression_sha256(&kernel, proof)?,
                "declaration_sha256": canonical_declaration_sha256(&kernel, theorem)?,
                "axiom_footprint": [],
                "direct_theorem_dependencies": names(&kernel, &kernel.theorem_dependencies(theorem)),
                "transitive_theorem_dependencies": transitive,
            },
            "execution": {"capsule_compositions": 4, "local_gcd_comm_submissions": 1, "exact_target_submissions": 1, "retries": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn run_official_clean_order_capsule(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let r091_path = path(&mut args)?;
    let cancellation_path = path(&mut args)?;
    let output_path = path(&mut args)?;
    if args.next().is_some() || output_path.exists() {
        return Err("usage: nat_gcd_fib_add_self_exact --official-clean-order-capsule <r091> <official-cancellation> <output>".to_owned());
    }
    let imported = import_bound(&r091_path, R091_SHA256, "r091")?;
    if !imported.report().axioms.is_empty() {
        return Err("r091 is not proof-isolated".to_owned());
    }
    let mut kernel = imported.kernel().clone();
    let cancellation = import_bound(&cancellation_path, CANCELLATION_CAPSULE, CANCELLATION)?;
    let bootstrap =
        compose_checked_theorem_slice(cancellation.kernel(), &kernel, &[CANCELLATION_BOOTSTRAP])
            .map_err(|error| format!("official cancellation bootstrap declined: {error:?}"))?;
    verify_checked_theorem_composition(
        cancellation.kernel(),
        &kernel,
        bootstrap.kernel(),
        bootstrap.receipt(),
    )
    .map_err(|error| format!("official cancellation bootstrap did not replay: {error:?}"))?;
    if bootstrap
        .receipt()
        .added_theorems
        .iter()
        .any(|row| !row.axiom_footprint.is_empty())
    {
        return Err("official cancellation bootstrap added assumptions".to_owned());
    }
    let bootstrap_receipt = bootstrap.receipt().receipt_sha256.clone();
    kernel = bootstrap.kernel().clone();
    let compatible = compose_checked_theorem_slice(cancellation.kernel(), &kernel, &[CANCELLATION])
        .map_err(|error| format!("official cancellation compatibility declined: {error:?}"))?;
    verify_checked_theorem_composition(
        cancellation.kernel(),
        &kernel,
        compatible.kernel(),
        compatible.receipt(),
    )
    .map_err(|error| format!("official cancellation compatibility did not replay: {error:?}"))?;
    if compatible
        .receipt()
        .added_theorems
        .iter()
        .any(|row| !row.axiom_footprint.is_empty())
    {
        return Err("official cancellation compatibility added assumptions".to_owned());
    }
    let compatibility_receipt = compatible.receipt().receipt_sha256.clone();
    kernel = compatible.kernel().clone();
    let eq_zero = declare_official_eq_zero(&mut kernel)?;
    require_empty(&kernel, eq_zero, OFFICIAL_EQ_ZERO)?;
    let le_of_dvd = declare_official_le_of_dvd(&mut kernel)?;
    require_empty(&kernel, le_of_dvd, OFFICIAL_LE_OF_DVD)?;
    let antisymm = declare_official_antisymm(&mut kernel)?;
    require_empty(&kernel, antisymm, OFFICIAL_ANTISYMM)?;

    let root = find_name(&kernel, OFFICIAL_ANTISYMM)?;
    let expected = evidence(&kernel, root)?;
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[root])
        .map_err(|error| format!("official clean-order capsule export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| {
                format!("official clean-order capsule import {pass} failed: {error:?}")
            })?;
        let replay_root = find_name(replay.kernel(), OFFICIAL_ANTISYMM)?;
        if evidence(replay.kernel(), replay_root)? != expected {
            return Err(format!(
                "official clean-order capsule import {pass} changed evidence"
            ));
        }
    }
    fs::write(&output_path, &bytes)
        .map_err(|error| format!("official clean-order capsule write failed: {error}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-autogenesis-official-r091-clean-dvd-antisymm-capsule",
            "state": "official-clean-order-compatible-with-cancellation-and-roundtrip-checked",
            "supports": [evidence(&kernel, eq_zero)?, evidence(&kernel, le_of_dvd)?, expected],
            "official_cancellation_compatibility": {
                "bootstrap_root": CANCELLATION_BOOTSTRAP,
                "bootstrap_receipt_sha256": bootstrap_receipt,
                "root": CANCELLATION,
                "receipt_sha256": compatibility_receipt,
                "replayed": true,
            },
            "portable_capsule": {
                "root": OFFICIAL_ANTISYMM,
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 2,
                "theorem": evidence(&kernel, root)?,
                "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
            },
            "exact_target_submissions": 0,
            "target_credit": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

struct Dev<'a> {
    kernel: &'a mut Kernel,
    anon: NameId,
    nat: NameId,
    zero: NameId,
    succ: NameId,
    rec: NameId,
    add: NameId,
    mul: NameId,
    gcd: NameId,
    dvd: NameId,
    le: NameId,
    fib: NameId,
    eq: NameId,
    eq_refl: NameId,
    eq_rec: NameId,
    iff: NameId,
    iff_rec: NameId,
    exists_rec: NameId,
    next_fvar: u64,
}

impl<'a> Dev<'a> {
    fn new(kernel: &'a mut Kernel) -> Result<Self, String> {
        Ok(Self {
            anon: kernel.anon(),
            nat: find_name(kernel, "Nat")?,
            zero: find_name(kernel, "Nat.zero")?,
            succ: find_name(kernel, "Nat.succ")?,
            rec: find_name(kernel, "Nat.rec")?,
            add: find_name(kernel, "Nat.add")?,
            mul: find_name(kernel, "Nat.mul")?,
            gcd: find_name(kernel, "Nat.gcd")?,
            dvd: find_name(kernel, "Nat.dvd")?,
            le: find_name(kernel, "Nat.le")?,
            fib: find_name(kernel, "Nat.fib")?,
            eq: find_name(kernel, "Eq")?,
            eq_refl: find_name(kernel, "Eq.refl")?,
            eq_rec: find_name(kernel, "Eq.rec")?,
            iff: find_name(kernel, "Iff")?,
            iff_rec: find_name(kernel, "Iff.rec")?,
            exists_rec: find_name(kernel, "Exists.rec")?,
            kernel,
            next_fvar: 10_000,
        })
    }
    fn exact(&self, expected: &str) -> Result<NameId, String> {
        find_name(self.kernel, expected)
    }
    fn fresh(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }
    fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        args.iter()
            .fold(head, |term, &arg| self.kernel.app(term, arg))
    }
    fn lemma(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        let head = self.kernel.const_(name, vec![]);
        self.apply(head, args)
    }
    fn nat_ty(&mut self) -> ExprId {
        self.kernel.const_(self.nat, vec![])
    }
    fn zero(&mut self) -> ExprId {
        self.kernel.const_(self.zero, vec![])
    }
    fn succ(&mut self, value: ExprId) -> ExprId {
        let head = self.kernel.const_(self.succ, vec![]);
        self.kernel.app(head, value)
    }
    fn num(&mut self, value: u32) -> ExprId {
        let mut result = self.zero();
        for _ in 0..value {
            result = self.succ(result);
        }
        result
    }
    fn add(&mut self, left: ExprId, right: ExprId) -> ExprId {
        self.lemma(self.add, &[left, right])
    }
    fn mul(&mut self, left: ExprId, right: ExprId) -> ExprId {
        self.lemma(self.mul, &[left, right])
    }
    fn gcd(&mut self, left: ExprId, right: ExprId) -> ExprId {
        self.lemma(self.gcd, &[left, right])
    }
    fn dvd(&mut self, divisor: ExprId, value: ExprId) -> ExprId {
        self.lemma(self.dvd, &[divisor, value])
    }
    fn le(&mut self, left: ExprId, right: ExprId) -> ExprId {
        self.lemma(self.le, &[left, right])
    }
    fn fib(&mut self, value: ExprId) -> ExprId {
        self.lemma(self.fib, &[value])
    }
    fn one_level(&mut self) -> LevelId {
        let zero = self.kernel.level_zero();
        self.kernel.level_succ(zero)
    }
    fn eq(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let one = self.one_level();
        let head = self.kernel.const_(self.eq, vec![one]);
        let nat = self.nat_ty();
        self.apply(head, &[nat, left, right])
    }
    fn refl(&mut self, value: ExprId) -> ExprId {
        let one = self.one_level();
        let head = self.kernel.const_(self.eq_refl, vec![one]);
        let nat = self.nat_ty();
        self.apply(head, &[nat, value])
    }
    fn lam(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let body = self.kernel.abstract_fvars(body, &[fv]);
        self.kernel.lam(self.anon, ty, body, BinderInfo::Default)
    }
    fn pi(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let body = self.kernel.abstract_fvars(body, &[fv]);
        self.kernel.pi(self.anon, ty, body, BinderInfo::Default)
    }
    fn arrow(&mut self, domain: ExprId, codomain: ExprId) -> ExprId {
        self.kernel
            .pi(self.anon, domain, codomain, BinderInfo::Default)
    }
    fn eq_motive(&mut self, source: ExprId, body: &dyn Fn(&mut Self, ExprId) -> ExprId) -> ExprId {
        let value_fv = self.fresh();
        let value = self.kernel.fvar(value_fv);
        let conclusion = body(self, value);
        let equality = self.eq(source, value);
        let inner = self
            .kernel
            .lam(self.anon, equality, conclusion, BinderInfo::Default);
        let nat = self.nat_ty();
        self.lam(value_fv, nat, inner)
    }
    fn transport(
        &mut self,
        source: ExprId,
        motive: ExprId,
        source_proof: ExprId,
        target: ExprId,
        equality: ExprId,
    ) -> ExprId {
        let zero = self.kernel.level_zero();
        let one = self.one_level();
        let rec = self.kernel.const_(self.eq_rec, vec![zero, one]);
        let nat = self.nat_ty();
        self.apply(rec, &[nat, source, motive, source_proof, target, equality])
    }
    fn symm(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let motive = self.eq_motive(left, &|d, value| d.eq(value, left));
        let base = self.refl(left);
        self.transport(left, motive, base, right, proof)
    }
    fn trans(
        &mut self,
        left: ExprId,
        middle: ExprId,
        right: ExprId,
        first: ExprId,
        second: ExprId,
    ) -> ExprId {
        let motive = self.eq_motive(middle, &|d, value| d.eq(left, value));
        self.transport(middle, motive, first, right, second)
    }
    fn dvd_predicate(&mut self, divisor: ExprId, value: ExprId) -> ExprId {
        let witness_fv = self.fresh();
        let witness = self.kernel.fvar(witness_fv);
        let product = self.mul(divisor, witness);
        let body = self.eq(value, product);
        let nat = self.nat_ty();
        self.lam(witness_fv, nat, body)
    }
    fn transport_dvd(
        &mut self,
        divisor: ExprId,
        source: ExprId,
        target: ExprId,
        proof: ExprId,
        equality: ExprId,
    ) -> ExprId {
        let motive = self.eq_motive(source, &|d, value| d.dvd(divisor, value));
        self.transport(source, motive, proof, target, equality)
    }
    fn iff_reverse(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let iff_ty = self.lemma(self.iff, &[left, right]);
        let target = self.arrow(right, left);
        let proof_fv = self.fresh();
        let motive = self.lam(proof_fv, iff_ty, target);
        let forward_ty = self.arrow(left, right);
        let forward_fv = self.fresh();
        let reverse_fv = self.fresh();
        let reverse = self.kernel.fvar(reverse_fv);
        let minor = self.lam(reverse_fv, target, reverse);
        let minor = self.lam(forward_fv, forward_ty, minor);
        let zero = self.kernel.level_zero();
        let rec = self.kernel.const_(self.iff_rec, vec![zero]);
        self.apply(rec, &[left, right, motive, minor, proof])
    }
    fn induct(
        &mut self,
        motive: &dyn Fn(&mut Self, ExprId) -> ExprId,
        base: &dyn Fn(&mut Self) -> ExprId,
        step: &dyn Fn(&mut Self, ExprId, ExprId) -> ExprId,
        target: ExprId,
    ) -> ExprId {
        let nat = self.nat_ty();
        let value_fv = self.fresh();
        let value = self.kernel.fvar(value_fv);
        let motive_body = motive(self, value);
        let motive_term = self.lam(value_fv, nat, motive_body);
        let base_term = base(self);
        let pred_fv = self.fresh();
        let pred = self.kernel.fvar(pred_fv);
        let ih_fv = self.fresh();
        let ih = self.kernel.fvar(ih_fv);
        let ih_ty = motive(self, pred);
        let step_body = step(self, pred, ih);
        let step_term = self.lam(ih_fv, ih_ty, step_body);
        let step_term = self.lam(pred_fv, nat, step_term);
        let zero = self.kernel.level_zero();
        let rec = self.kernel.const_(self.rec, vec![zero]);
        self.apply(rec, &[motive_term, base_term, step_term, target])
    }
    fn two_lambdas(
        &mut self,
        first_ty: ExprId,
        second_ty: ExprId,
        body: &dyn Fn(&mut Self, ExprId, ExprId) -> ExprId,
    ) -> ExprId {
        let first_fv = self.fresh();
        let first = self.kernel.fvar(first_fv);
        let second_fv = self.fresh();
        let second = self.kernel.fvar(second_fv);
        let result = body(self, first, second);
        let result = self.lam(second_fv, second_ty, result);
        self.lam(first_fv, first_ty, result)
    }
}

fn declare_official_eq_zero(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(
        kernel,
        &["Axeyum", "Autogenesis", "eqZeroOfZeroDvdOfficialV1"],
    );
    let mut d = Dev::new(kernel)?;
    let zero_mul = d.exact("Nat.zero_mul")?;
    let nat = d.nat_ty();
    let n_fv = d.fresh();
    let n = d.kernel.fvar(n_fv);
    let zero = d.zero();
    let hypothesis_ty = d.dvd(zero, n);
    let hypothesis_fv = d.fresh();
    let hypothesis = d.kernel.fvar(hypothesis_fv);
    let goal = d.eq(n, zero);
    let predicate = d.dvd_predicate(zero, n);
    let motive = d
        .kernel
        .lam(d.anon, hypothesis_ty, goal, BinderInfo::Default);
    let witness_fv = d.fresh();
    let witness = d.kernel.fvar(witness_fv);
    let product = d.mul(zero, witness);
    let equation_ty = d.eq(n, product);
    let equation_fv = d.fresh();
    let equation = d.kernel.fvar(equation_fv);
    let collapse = d.lemma(zero_mul, &[witness]);
    let proof = d.trans(n, product, zero, equation, collapse);
    let minor = d.lam(equation_fv, equation_ty, proof);
    let minor = d.lam(witness_fv, nat, minor);
    let one = d.one_level();
    let rec = d.kernel.const_(d.exists_rec, vec![one]);
    let proof = d.apply(rec, &[nat, predicate, motive, minor, hypothesis]);
    let proof = d.lam(hypothesis_fv, hypothesis_ty, proof);
    let proof = d.lam(n_fv, nat, proof);
    let ty = d.arrow(hypothesis_ty, goal);
    let ty = d.pi(n_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("official zero-divisibility equality rejected: {error:?}"))?;
    Ok(target)
}

#[allow(clippy::too_many_lines)]
fn declare_official_le_of_dvd(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "leOfDvdOfficialV1"]);
    let mut d = Dev::new(kernel)?;
    let one_le_right = d.exact("Nat.one_le_right_of_mul")?;
    let mul_le_left = d.exact("Nat.mul_le_mul_left")?;
    let mul_one = d.exact("Nat.mul_one")?;
    let nat = d.nat_ty();
    let a_fv = d.fresh();
    let a = d.kernel.fvar(a_fv);
    let n_fv = d.fresh();
    let n = d.kernel.fvar(n_fv);
    let one = d.num(1);
    let positive_ty = d.le(one, n);
    let divides_ty = d.dvd(a, n);
    let conclusion = d.le(a, n);
    let positive_fv = d.fresh();
    let positive = d.kernel.fvar(positive_fv);
    let divides_fv = d.fresh();
    let divides = d.kernel.fvar(divides_fv);
    let predicate = d.dvd_predicate(a, n);
    let motive = d
        .kernel
        .lam(d.anon, divides_ty, conclusion, BinderInfo::Default);
    let witness_fv = d.fresh();
    let witness = d.kernel.fvar(witness_fv);
    let product = d.mul(a, witness);
    let equation_ty = d.eq(n, product);
    let equation_fv = d.fresh();
    let equation = d.kernel.fvar(equation_fv);
    let product_positive = {
        let motive = d.eq_motive(n, &|d, value| {
            let one = d.num(1);
            d.le(one, value)
        });
        d.transport(n, motive, positive, product, equation)
    };
    let witness_positive = d.lemma(one_le_right, &[a, witness, product_positive]);
    let scaled = d.lemma(mul_le_left, &[a, one, witness, witness_positive]);
    let a_one = d.mul(a, one);
    let collapse = d.lemma(mul_one, &[a]);
    let bounded_product = {
        let motive = d.eq_motive(a_one, &|d, value| d.le(value, product));
        d.transport(a_one, motive, scaled, a, collapse)
    };
    let reverse_equation = d.symm(n, product, equation);
    let body = {
        let motive = d.eq_motive(product, &|d, value| d.le(a, value));
        d.transport(product, motive, bounded_product, n, reverse_equation)
    };
    let minor = d.lam(equation_fv, equation_ty, body);
    let minor = d.lam(witness_fv, nat, minor);
    let one_level = d.one_level();
    let rec = d.kernel.const_(d.exists_rec, vec![one_level]);
    let proof = d.apply(rec, &[nat, predicate, motive, minor, divides]);
    let proof = d.lam(divides_fv, divides_ty, proof);
    let proof = d.lam(positive_fv, positive_ty, proof);
    let proof = d.lam(n_fv, nat, proof);
    let proof = d.lam(a_fv, nat, proof);
    let ty = d.arrow(divides_ty, conclusion);
    let ty = d.arrow(positive_ty, ty);
    let ty = d.pi(n_fv, nat, ty);
    let ty = d.pi(a_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("official divisor bound rejected: {error:?}"))?;
    Ok(target)
}

fn antisymm_statement(d: &mut Dev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let forward = d.dvd(a, b);
    let reverse = d.dvd(b, a);
    let equality = d.eq(a, b);
    let rest = d.arrow(reverse, equality);
    d.arrow(forward, rest)
}

#[allow(clippy::too_many_lines)]
fn declare_official_antisymm(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "dvdAntisymmOfficialV1"]);
    let mut d = Dev::new(kernel)?;
    let eq_zero = d.exact(OFFICIAL_EQ_ZERO)?;
    let clean_le = d.exact(OFFICIAL_LE_OF_DVD)?;
    let le_antisymm = d.exact("Nat.le_antisymm")?;
    let zero_le = d.exact("Nat.zero_le")?;
    let le_succ = d.exact("Nat.le_succ_succ")?;
    let nat = d.nat_ty();
    let a_fv = d.fresh();
    let a = d.kernel.fvar(a_fv);
    let b_fv = d.fresh();
    let b = d.kernel.fvar(b_fv);
    let proof = d.induct(
        &|d, candidate_b| antisymm_statement(d, a, candidate_b),
        &|d| {
            let zero = d.zero();
            let forward_ty = d.dvd(a, zero);
            let reverse_ty = d.dvd(zero, a);
            d.two_lambdas(forward_ty, reverse_ty, &|d, _forward, reverse| {
                d.lemma(eq_zero, &[a, reverse])
            })
        },
        &|d, b_pred, _ih| {
            let b_succ = d.succ(b_pred);
            d.induct(
                &|d, candidate_a| antisymm_statement(d, candidate_a, b_succ),
                &|d| {
                    let zero = d.zero();
                    let forward_ty = d.dvd(zero, b_succ);
                    let reverse_ty = d.dvd(b_succ, zero);
                    d.two_lambdas(forward_ty, reverse_ty, &|d, forward, _reverse| {
                        let collapse = d.lemma(eq_zero, &[b_succ, forward]);
                        d.symm(b_succ, zero, collapse)
                    })
                },
                &|d, a_pred, _a_ih| {
                    let a_succ = d.succ(a_pred);
                    let forward_ty = d.dvd(a_succ, b_succ);
                    let reverse_ty = d.dvd(b_succ, a_succ);
                    d.two_lambdas(forward_ty, reverse_ty, &|d, forward, reverse| {
                        let zero = d.zero();
                        let zero_b = d.lemma(zero_le, &[b_pred]);
                        let b_positive = d.lemma(le_succ, &[zero, b_pred, zero_b]);
                        let zero_a = d.lemma(zero_le, &[a_pred]);
                        let a_positive = d.lemma(le_succ, &[zero, a_pred, zero_a]);
                        let a_le_b = d.lemma(clean_le, &[a_succ, b_succ, b_positive, forward]);
                        let b_le_a = d.lemma(clean_le, &[b_succ, a_succ, a_positive, reverse]);
                        d.lemma(le_antisymm, &[a_succ, b_succ, a_le_b, b_le_a])
                    })
                },
                a,
            )
        },
        b,
    );
    let ty = antisymm_statement(&mut d, a, b);
    let proof = d.lam(b_fv, nat, proof);
    let proof = d.lam(a_fv, nat, proof);
    let ty = d.pi(b_fv, nat, ty);
    let ty = d.pi(a_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("official divisibility antisymmetry rejected: {error:?}"))?;
    Ok(target)
}

#[allow(clippy::similar_names)]
fn declare_clean_gcd_comm(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "gcdCommCleanV1"]);
    let mut d = Dev::new(kernel)?;
    let antisymm = d.exact(CLEAN_ANTISYMM)?;
    let gcd_left = d.exact("Nat.gcd_dvd_left")?;
    let gcd_right = d.exact("Nat.gcd_dvd_right")?;
    let dvd_gcd = d.exact("Nat.dvd_gcd")?;
    let nat = d.nat_ty();
    let a_fv = d.fresh();
    let a = d.kernel.fvar(a_fv);
    let b_fv = d.fresh();
    let b = d.kernel.fvar(b_fv);
    let ab = d.gcd(a, b);
    let ba = d.gcd(b, a);
    let ab_to_b = d.lemma(gcd_right, &[a, b]);
    let ab_to_a = d.lemma(gcd_left, &[a, b]);
    let forward = d.lemma(dvd_gcd, &[ab, b, a, ab_to_b, ab_to_a]);
    let ba_to_a = d.lemma(gcd_right, &[b, a]);
    let ba_to_b = d.lemma(gcd_left, &[b, a]);
    let reverse = d.lemma(dvd_gcd, &[ba, a, b, ba_to_a, ba_to_b]);
    let proof = d.lemma(antisymm, &[ab, ba, forward, reverse]);
    let ty = d.eq(ab, ba);
    let proof = d.lam(b_fv, nat, proof);
    let proof = d.lam(a_fv, nat, proof);
    let ty = d.pi(b_fv, nat, ty);
    let ty = d.pi(a_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("clean gcd commutativity rejected: {error:?}"))?;
    Ok(target)
}

fn declare_target(kernel: &mut Kernel, goal: ExprId) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Nat", "gcd_fib_add_self"]);
    let mut d = Dev::new(kernel)?;
    let addition = d.exact(ADDITION)?;
    let coprime = d.exact(COPRIME)?;
    let cancellation = d.exact(CANCELLATION)?;
    let antisymm = d.exact(CLEAN_ANTISYMM)?;
    let gcd_comm = d.exact(CLEAN_GCD_COMM)?;
    let gcd_left = d.exact("Nat.gcd_dvd_left")?;
    let gcd_right = d.exact("Nat.gcd_dvd_right")?;
    let dvd_gcd = d.exact("Nat.dvd_gcd")?;
    let dvd_mul = d.exact("Nat.dvd_mul_right_of_dvd")?;
    let dvd_add = d.exact("Nat.dvd_add")?;
    let dvd_add_iff = d.exact("Nat.dvd_add_iff_right")?;
    let mul_comm = d.exact("Nat.mul_comm")?;
    let nat = d.nat_ty();
    let m_fv = d.fresh();
    let m = d.kernel.fvar(m_fv);
    let n_fv = d.fresh();
    let n = d.kernel.fvar(n_fv);
    let proof = d.induct(
        &|d, candidate| statement(d, candidate, n),
        &|d| {
            let zero = d.zero();
            let fib_zero = d.fib(zero);
            let fib_n = d.fib(n);
            let common = d.gcd(fib_zero, fib_n);
            d.refl(common)
        },
        &|d, k, _ih| {
            prove_successor(
                d,
                k,
                n,
                addition,
                coprime,
                cancellation,
                antisymm,
                gcd_comm,
                gcd_left,
                gcd_right,
                dvd_gcd,
                dvd_mul,
                dvd_add,
                dvd_add_iff,
                mul_comm,
            )
        },
        m,
    );
    let proof = d.lam(n_fv, nat, proof);
    let proof = d.lam(m_fv, nat, proof);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty: goal,
            value: proof,
        })
        .map_err(|error| format!("exact Fibonacci GCD-shift rejected: {error:?}"))?;
    Ok(target)
}

fn statement(d: &mut Dev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let fib_m = d.fib(m);
    let n_plus_m = d.add(n, m);
    let fib_shift = d.fib(n_plus_m);
    let fib_n = d.fib(n);
    let left = d.gcd(fib_m, fib_shift);
    let right = d.gcd(fib_m, fib_n);
    d.eq(left, right)
}

#[allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments
)]
fn prove_successor(
    d: &mut Dev<'_>,
    k: ExprId,
    n: ExprId,
    addition: NameId,
    coprime: NameId,
    cancellation: NameId,
    antisymm: NameId,
    gcd_comm: NameId,
    gcd_left: NameId,
    gcd_right: NameId,
    dvd_gcd: NameId,
    dvd_mul: NameId,
    dvd_add: NameId,
    dvd_add_iff: NameId,
    mul_comm: NameId,
) -> ExprId {
    let sk = d.succ(k);
    let sn = d.succ(n);
    let a = d.fib(sk);
    let b = d.fib(n);
    let f = d.fib(k);
    let x = d.fib(sn);
    let shifted = d.add(n, sk);
    let c = d.fib(shifted);
    let ax = d.mul(a, x);
    let fb = d.mul(f, b);
    let sum = d.add(ax, fb);
    let left = d.gcd(a, c);
    let right = d.gcd(a, b);
    let c_eq_sum = d.lemma(addition, &[n, k]);

    let right_a = d.lemma(gcd_left, &[a, b]);
    let right_b = d.lemma(gcd_right, &[a, b]);
    let right_ax = d.lemma(dvd_mul, &[right, a, x, right_a]);
    let bf = d.mul(b, f);
    let right_bf = d.lemma(dvd_mul, &[right, b, f, right_b]);
    let bf_eq_fb = d.lemma(mul_comm, &[b, f]);
    let right_fb = d.transport_dvd(right, bf, fb, right_bf, bf_eq_fb);
    let right_sum = d.lemma(dvd_add, &[right, ax, fb, right_ax, right_fb]);
    let sum_eq_c = d.symm(c, sum, c_eq_sum);
    let right_c = d.transport_dvd(right, sum, c, right_sum, sum_eq_c);
    let right_left = d.lemma(dvd_gcd, &[right, a, c, right_a, right_c]);

    let left_a = d.lemma(gcd_left, &[a, c]);
    let left_c = d.lemma(gcd_right, &[a, c]);
    let left_sum = d.transport_dvd(left, c, sum, left_c, c_eq_sum);
    let left_ax = d.lemma(dvd_mul, &[left, a, x, left_a]);
    let left_fb_ty = d.dvd(left, fb);
    let left_sum_ty = d.dvd(left, sum);
    let iff = d.lemma(dvd_add_iff, &[left, ax, fb, left_ax]);
    let reverse = d.iff_reverse(left_fb_ty, left_sum_ty, iff);
    let left_fb = d.apply(reverse, &[left_sum]);

    let coprime_f_a = d.lemma(coprime, &[k]);
    let f_a = d.gcd(f, a);
    let a_f = d.gcd(a, f);
    let comm = d.lemma(gcd_comm, &[f, a]);
    let zero = d.zero();
    let one = d.succ(zero);
    let motive = d.eq_motive(f_a, &|d, value| d.eq(value, one));
    let coprime_a_f = d.transport(f_a, motive, coprime_f_a, a_f, comm);
    let left_b = d.lemma(cancellation, &[a, f, b, left, coprime_a_f, left_a, left_fb]);
    let left_right = d.lemma(dvd_gcd, &[left, a, b, left_a, left_b]);
    d.lemma(antisymm, &[left, right, left_right, right_left])
}

fn path(args: &mut impl Iterator<Item = std::ffi::OsString>) -> Result<PathBuf, String> {
    args.next()
        .map(PathBuf::from)
        .ok_or_else(|| USAGE.to_owned())
}
fn import_bound(
    path: &Path,
    expected: &str,
    label: &str,
) -> Result<axeyum_lean_import::CompletedImport, String> {
    let bytes = fs::read(path).map_err(|error| format!("{label} read failed: {error}"))?;
    let actual = hex_sha256(&bytes);
    if actual != expected {
        return Err(format!(
            "{label} identity changed: expected {expected}, got {actual}"
        ));
    }
    import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("{label} import failed: {error:?}"))
}
fn require_empty(kernel: &Kernel, theorem: NameId, label: &str) -> Result<(), String> {
    let footprint = names(kernel, &kernel.axiom_footprint(theorem));
    if footprint.is_empty() {
        Ok(())
    } else {
        Err(format!("{label} reaches assumptions: {footprint:?}"))
    }
}
fn evidence(kernel: &Kernel, theorem: NameId) -> Result<Value, String> {
    Ok(
        json!({"name": kernel.display_name(theorem).to_string(), "declaration_sha256": canonical_declaration_sha256(kernel, theorem)?, "axiom_footprint": names(kernel, &kernel.axiom_footprint(theorem)), "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(theorem))}),
    )
}
fn transitive_dependencies(kernel: &Kernel, theorem: NameId) -> Vec<String> {
    let mut seen = std::collections::BTreeSet::new();
    let mut pending = vec![theorem];
    while let Some(current) = pending.pop() {
        for dependency in kernel.theorem_dependencies(current) {
            if seen.insert(kernel.display_name(dependency).to_string()) {
                pending.push(dependency);
            }
        }
    }
    seen.into_iter().collect()
}
fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    let found = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match found.as_slice() {
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
fn names(kernel: &Kernel, values: &[NameId]) -> Vec<String> {
    values
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect()
}
fn hex_sha256(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut out, "{byte:02x}").expect("String writes cannot fail");
    }
    out
}
