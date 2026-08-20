//! Measure whether the axiom-free native Nat library composes with an import.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    ImportLimits, canonical_alpha_expression_sha256, canonical_declaration_sha256,
    canonical_expression_sha256, canonical_kernel_type_shape_sha256, import_ndjson,
};
use axeyum_lean_kernel::{
    Declaration, ExprId, ExprNode, Kernel, KernelError, LevelId, LevelNode, NameId, NameNode,
    build_nat_prelude,
};
use serde_json::json;
use sha2::{Digest, Sha256};

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-prelude-composition-probe: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: nat_prelude_composition_probe <stream.ndjson> [output.json]")?;
    let output_path = arguments.next().map(PathBuf::from);
    if arguments.next().is_some() {
        return Err("unexpected trailing argument".to_owned());
    }
    let stream = fs::read(path).map_err(|error| error.to_string())?;
    let completed = import_ndjson(Cursor::new(&stream), ImportLimits::default())
        .map_err(|error| format!("source import failed: {error:?}"))?;
    let (mut kernel, report) = completed.into_parts();
    if !report.axioms.is_empty() {
        return Err("source stream unexpectedly contains axioms".to_owned());
    }
    let declarations_before = kernel.environment().len();
    let theorems_before = kernel
        .environment()
        .iter()
        .filter(|(_, declaration)| matches!(declaration, Declaration::Theorem { .. }))
        .count();
    let required_names = [
        "Nat.rec",
        "Nat.add_comm",
        "Nat.gcd_zero_left",
        "Nat.gcd_dvd_left",
        "Nat.gcd_dvd_right",
        "Nat.dvd_add_iff_right",
        "Nat.dvd_gcd",
        "Nat.eq_one_of_dvd_one",
    ];
    let required = required_names
        .into_iter()
        .map(|required| {
            let present = kernel
                .environment()
                .iter()
                .any(|(&name, _)| kernel.display_name(name).to_string() == required);
            (required.to_owned(), json!(present))
        })
        .collect::<serde_json::Map<_, _>>();
    let overlaps = compare_native_overlaps(&kernel)?;
    let (composition, structural_mismatch_control) = exercise_composition_controls(&mut kernel)?;
    let result = match build_nat_prelude(&mut kernel) {
        Ok(_) => json!({"outcome": "composed"}),
        Err(error) => {
            let conflicting_name = match &error {
                KernelError::DeclarationExists { name } => {
                    Some(kernel.display_name(*name).to_string())
                }
                _ => None,
            };
            json!({
                "outcome": "rejected",
                "error": format!("{error:?}"),
                "conflicting_name": conflicting_name,
            })
        }
    };
    let rendered = serde_json::to_string(&json!({
        "schema_version": 1,
        "kind": "axeyum-native-nat-prelude-import-composition-probe",
        "source": {
            "stream_sha256": hex_sha256(&stream),
            "lean_version": report.lean_version,
            "lean_githash": report.lean_githash,
            "axioms": report.axioms,
            "declarations_before": declarations_before,
            "theorems_before": theorems_before,
            "required_declarations_present": required,
            "native_declarations": overlaps.native_declarations,
            "exact_overlap_names": overlaps.exact,
            "alpha_type_compatible_content_mismatched_names": overlaps.alpha_type_compatible_content_mismatched,
            "kernel_type_shape_compatible_content_mismatched_names": overlaps.kernel_type_shape_compatible_content_mismatched,
            "type_mismatched_overlaps": overlaps.type_mismatched,
            "required_native_theorem_dependency_closures": overlaps.required_theorem_dependency_closures,
            "composition_control": composition,
            "structural_mismatch_control": structural_mismatch_control,
        },
        "result": result,
        "authority": {
            "proof_bodies_displayed": false,
            "proof_search_invocations": 0,
            "kernel_submissions": 3,
            "ledger_writes": 0,
        },
    }))
    .map_err(|error| error.to_string())?;
    if let Some(output_path) = output_path {
        fs::write(output_path, format!("{rendered}\n")).map_err(|error| error.to_string())?;
    }
    println!("{rendered}");
    Ok(())
}

fn exercise_composition_controls(
    kernel: &mut Kernel,
) -> Result<(serde_json::Value, serde_json::Value), String> {
    let negative_before = environment_sha256(kernel)?;
    let mut negative_kernel = kernel.clone();
    let negative_error =
        compose_native_theorem_slice(&mut negative_kernel, &["Nat.eq_one_of_dvd_one"])
            .expect_err("the structurally mismatched control must decline");
    let negative_after = environment_sha256(&negative_kernel)?;
    if negative_before != negative_after {
        return Err("failed composition changed the caller kernel".to_owned());
    }
    let positive = compose_native_theorem_slice(kernel, &["Nat.add_comm"])?;
    let negative = json!({
        "root": "Nat.eq_one_of_dvd_one",
        "outcome": "declined",
        "error": negative_error,
        "environment_sha256_before": negative_before,
        "environment_sha256_after": negative_after,
    });
    Ok((positive, negative))
}

fn compose_native_theorem_slice(
    target: &mut Kernel,
    roots: &[&str],
) -> Result<serde_json::Value, String> {
    let mut native = Kernel::new();
    build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat prelude failed to build: {error:?}"))?;
    let native_names = declaration_names(&native);
    let target_names = declaration_names(target);
    let root_ids: Vec<NameId> = roots
        .iter()
        .map(|root| {
            native_names
                .get(*root)
                .copied()
                .ok_or_else(|| format!("native root missing: {root}"))
        })
        .collect::<Result<_, _>>()?;
    let closure = native
        .root_declaration_closure(&root_ids)
        .map_err(|error| format!("native closure failed: {error:?}"))?;
    let mut reused = Vec::new();
    let mut missing = Vec::new();
    for &source_name in &closure {
        let rendered = native.display_name(source_name).to_string();
        if let Some(&target_name) = target_names.get(&rendered) {
            let source_type = native
                .environment()
                .get(source_name)
                .expect("closure declaration")
                .ty();
            let target_type = target
                .environment()
                .get(target_name)
                .expect("mapped target declaration")
                .ty();
            let source_shape = canonical_kernel_type_shape_sha256(&native, source_type)?;
            let target_shape = canonical_kernel_type_shape_sha256(target, target_type)?;
            if source_shape != target_shape {
                return Err(format!(
                    "kernel type-shape mismatch for reused declaration {rendered}: native={source_shape} imported={target_shape}"
                ));
            }
            reused.push(rendered);
        } else {
            missing.push(rendered);
        }
    }

    let before = environment_sha256(target)?;
    let mut staged = target.clone();
    let mut translator = ExpressionTranslator::new(&native, &mut staged);
    let mut added = Vec::new();
    for &source_name in &closure {
        let rendered = native.display_name(source_name).to_string();
        if target_names.contains_key(&rendered) {
            continue;
        }
        let declaration = native
            .environment()
            .get(source_name)
            .expect("closure declaration")
            .clone();
        let translated = translate_checked_theorem(&mut translator, declaration, &rendered)?;
        translator
            .target
            .add_declaration(translated)
            .map_err(|error| format!("trusted gate rejected {rendered}: {error:?}"))?;
        added.push(rendered);
    }
    let evidence = added_theorem_evidence(translator.target, &added)?;
    let after = environment_sha256(translator.target)?;
    drop(translator);
    *target = staged;
    Ok(json!({
        "roots": roots,
        "outcome": "composed",
        "reused_dependency_names": reused,
        "declarations_absent_before": missing,
        "added_theorem_names": added,
        "added_declaration_sha256": evidence.digests,
        "added_axiom_footprints": evidence.footprints,
        "environment_sha256_before": before,
        "environment_sha256_after": after,
    }))
}

fn translate_checked_theorem(
    translator: &mut ExpressionTranslator<'_>,
    declaration: Declaration,
    rendered: &str,
) -> Result<Declaration, String> {
    let Declaration::Theorem {
        name,
        uparams,
        ty,
        value,
    } = declaration
    else {
        return Err(format!(
            "missing dependency is not a checked theorem: {rendered}"
        ));
    };
    Ok(Declaration::Theorem {
        name: translator.name(name),
        uparams: uparams
            .into_iter()
            .map(|name| translator.name(name))
            .collect(),
        ty: translator.expr(ty)?,
        value: translator.expr(value)?,
    })
}

struct AddedTheoremEvidence {
    digests: BTreeMap<String, String>,
    footprints: BTreeMap<String, Vec<String>>,
}

fn added_theorem_evidence(
    kernel: &Kernel,
    added: &[String],
) -> Result<AddedTheoremEvidence, String> {
    let names = declaration_names(kernel);
    let digests = added
        .iter()
        .map(|name| {
            Ok((
                name.clone(),
                canonical_declaration_sha256(kernel, names[name])?,
            ))
        })
        .collect::<Result<_, String>>()?;
    let footprints = added
        .iter()
        .map(|name| {
            let footprint = kernel
                .axiom_footprint(names[name])
                .into_iter()
                .map(|axiom| kernel.display_name(axiom).to_string())
                .collect();
            (name.clone(), footprint)
        })
        .collect();
    Ok(AddedTheoremEvidence {
        digests,
        footprints,
    })
}

struct ExpressionTranslator<'a> {
    source: &'a Kernel,
    target: &'a mut Kernel,
    names: HashMap<NameId, NameId>,
    levels: HashMap<LevelId, LevelId>,
    expressions: HashMap<ExprId, ExprId>,
}

impl<'a> ExpressionTranslator<'a> {
    fn new(source: &'a Kernel, target: &'a mut Kernel) -> Self {
        Self {
            source,
            target,
            names: HashMap::new(),
            levels: HashMap::new(),
            expressions: HashMap::new(),
        }
    }

    fn name(&mut self, source: NameId) -> NameId {
        if let Some(&translated) = self.names.get(&source) {
            return translated;
        }
        let translated = match self.source.name_node(source).clone() {
            NameNode::Anonymous => self.target.anon(),
            NameNode::Str(parent, component) => {
                let parent = self.name(parent);
                self.target.name_str(parent, component)
            }
            NameNode::Num(parent, component) => {
                let parent = self.name(parent);
                self.target.name_num(parent, component)
            }
        };
        self.names.insert(source, translated);
        translated
    }

    fn level(&mut self, source: LevelId) -> LevelId {
        if let Some(&translated) = self.levels.get(&source) {
            return translated;
        }
        let translated = match self.source.level_node(source).clone() {
            LevelNode::Zero => self.target.level_zero(),
            LevelNode::Succ(level) => {
                let level = self.level(level);
                self.target.level_succ(level)
            }
            LevelNode::Max(left, right) => {
                let left = self.level(left);
                let right = self.level(right);
                self.target.level_max(left, right)
            }
            LevelNode::IMax(left, right) => {
                let left = self.level(left);
                let right = self.level(right);
                self.target.level_imax(left, right)
            }
            LevelNode::Param(name) => {
                let name = self.name(name);
                self.target.level_param(name)
            }
        };
        self.levels.insert(source, translated);
        translated
    }

    fn expr(&mut self, source: ExprId) -> Result<ExprId, String> {
        if let Some(&translated) = self.expressions.get(&source) {
            return Ok(translated);
        }
        let translated = match self.source.expr_node(source).clone() {
            ExprNode::BVar(index) => self.target.bvar(index),
            ExprNode::FVar(_) => {
                return Err("closed declaration contains a free variable".to_owned());
            }
            ExprNode::Sort(level) => {
                let level = self.level(level);
                self.target.sort(level)
            }
            ExprNode::Const(name, levels) => {
                let name = self.name(name);
                let levels = levels.into_iter().map(|level| self.level(level)).collect();
                self.target.const_(name, levels)
            }
            ExprNode::Proj(name, index, structure) => {
                let name = self.name(name);
                let structure = self.expr(structure)?;
                self.target.proj(name, index, structure)
            }
            ExprNode::App(function, argument) => {
                let function = self.expr(function)?;
                let argument = self.expr(argument)?;
                self.target.app(function, argument)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let name = self.name(name);
                let ty = self.expr(ty)?;
                let body = self.expr(body)?;
                self.target.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let name = self.name(name);
                let ty = self.expr(ty)?;
                let body = self.expr(body)?;
                self.target.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, value, body) => {
                let name = self.name(name);
                let ty = self.expr(ty)?;
                let value = self.expr(value)?;
                let body = self.expr(body)?;
                self.target.let_(name, ty, value, body)
            }
            ExprNode::Lit(literal) => self.target.lit(literal),
        };
        self.expressions.insert(source, translated);
        Ok(translated)
    }
}

fn environment_sha256(kernel: &Kernel) -> Result<String, String> {
    let mut entries: Vec<(String, String)> = kernel
        .environment()
        .iter()
        .map(|(&name, _)| {
            Ok((
                kernel.display_name(name).to_string(),
                canonical_declaration_sha256(kernel, name)?,
            ))
        })
        .collect::<Result<_, String>>()?;
    entries.sort();
    let mut encoded = String::new();
    for (name, digest) in entries {
        let _ = writeln!(encoded, "{name}\t{digest}");
    }
    Ok(hex_sha256(encoded.as_bytes()))
}

fn declaration_names(kernel: &Kernel) -> BTreeMap<String, axeyum_lean_kernel::NameId> {
    kernel
        .environment()
        .iter()
        .map(|(&name, _)| (kernel.display_name(name).to_string(), name))
        .collect()
}

struct OverlapReport {
    native_declarations: usize,
    exact: Vec<String>,
    alpha_type_compatible_content_mismatched: Vec<String>,
    kernel_type_shape_compatible_content_mismatched: Vec<String>,
    type_mismatched: Vec<serde_json::Value>,
    required_theorem_dependency_closures: Vec<serde_json::Value>,
}

fn compare_native_overlaps(imported: &Kernel) -> Result<OverlapReport, String> {
    let imported_names = declaration_names(imported);
    let mut native = Kernel::new();
    build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat prelude failed to build: {error:?}"))?;
    let native_names = declaration_names(&native);
    let mut exact = Vec::new();
    let mut alpha_type_compatible_content_mismatched = Vec::new();
    let mut kernel_type_shape_compatible_content_mismatched = Vec::new();
    let mut type_mismatched = Vec::new();
    for (name, &native_id) in &native_names {
        let Some(&imported_id) = imported_names.get(name) else {
            continue;
        };
        let native_digest = canonical_declaration_sha256(&native, native_id)?;
        let imported_digest = canonical_declaration_sha256(imported, imported_id)?;
        if native_digest == imported_digest {
            exact.push(name.clone());
        } else {
            let native_type_id = native
                .environment()
                .get(native_id)
                .expect("native name")
                .ty();
            let imported_type_id = imported
                .environment()
                .get(imported_id)
                .expect("imported name")
                .ty();
            let native_type = canonical_expression_sha256(&native, native_type_id)?;
            let imported_type = canonical_expression_sha256(imported, imported_type_id)?;
            let native_alpha_type = canonical_alpha_expression_sha256(&native, native_type_id)?;
            let imported_alpha_type =
                canonical_alpha_expression_sha256(imported, imported_type_id)?;
            if native_alpha_type == imported_alpha_type {
                alpha_type_compatible_content_mismatched.push(name.clone());
            } else {
                let native_kernel_type_shape =
                    canonical_kernel_type_shape_sha256(&native, native_type_id)?;
                let imported_kernel_type_shape =
                    canonical_kernel_type_shape_sha256(imported, imported_type_id)?;
                if native_kernel_type_shape == imported_kernel_type_shape {
                    kernel_type_shape_compatible_content_mismatched.push(name.clone());
                } else {
                    type_mismatched.push(json!({
                        "name": name,
                        "native_content_sha256": native_digest,
                        "imported_content_sha256": imported_digest,
                        "native_type_sha256": native_type,
                        "imported_type_sha256": imported_type,
                        "native_alpha_type_sha256": native_alpha_type,
                        "imported_alpha_type_sha256": imported_alpha_type,
                        "native_kernel_type_shape_sha256": native_kernel_type_shape,
                        "imported_kernel_type_shape_sha256": imported_kernel_type_shape,
                        "native_type": native.render_lean(native_type_id),
                        "imported_type": imported.render_lean(imported_type_id),
                    }));
                }
            }
        }
    }
    let required_theorem_dependency_closures = required_theorem_dependency_closures(
        &native,
        &native_names,
        &imported_names,
        &exact,
        &alpha_type_compatible_content_mismatched,
        &kernel_type_shape_compatible_content_mismatched,
        &type_mismatched,
    )?;
    Ok(OverlapReport {
        native_declarations: native.environment().len(),
        exact,
        alpha_type_compatible_content_mismatched,
        kernel_type_shape_compatible_content_mismatched,
        type_mismatched,
        required_theorem_dependency_closures,
    })
}

#[allow(clippy::too_many_arguments)]
fn required_theorem_dependency_closures(
    native: &Kernel,
    native_names: &BTreeMap<String, axeyum_lean_kernel::NameId>,
    imported_names: &BTreeMap<String, axeyum_lean_kernel::NameId>,
    exact: &[String],
    alpha_compatible: &[String],
    kernel_shape_compatible: &[String],
    type_mismatched: &[serde_json::Value],
) -> Result<Vec<serde_json::Value>, String> {
    let exact: BTreeSet<&str> = exact.iter().map(String::as_str).collect();
    let alpha_compatible: BTreeSet<&str> = alpha_compatible.iter().map(String::as_str).collect();
    let kernel_shape_compatible: BTreeSet<&str> =
        kernel_shape_compatible.iter().map(String::as_str).collect();
    let type_mismatched: BTreeSet<&str> = type_mismatched
        .iter()
        .map(|row| {
            row["name"]
                .as_str()
                .expect("type mismatch rows always carry a name")
        })
        .collect();
    let required = [
        "Nat.add_comm",
        "Nat.dvd_add_iff_right",
        "Nat.dvd_gcd",
        "Nat.eq_one_of_dvd_one",
        "Nat.gcd_dvd_left",
        "Nat.gcd_dvd_right",
        "Nat.gcd_zero_left",
    ];
    required
        .into_iter()
        .map(|theorem| {
            let root = native_names
                .get(theorem)
                .copied()
                .ok_or_else(|| format!("required native theorem missing: {theorem}"))?;
            let dependencies: Vec<String> = native
                .declaration_dependency_closure(root)
                .into_iter()
                .map(|name| native.display_name(name).to_string())
                .collect();
            let mut missing = Vec::new();
            let mut exact_dependencies = Vec::new();
            let mut alpha_dependencies = Vec::new();
            let mut kernel_shape_dependencies = Vec::new();
            let mut type_mismatched_dependencies = Vec::new();
            for dependency in &dependencies {
                if !imported_names.contains_key(dependency) {
                    missing.push(dependency.clone());
                } else if exact.contains(dependency.as_str()) {
                    exact_dependencies.push(dependency.clone());
                } else if alpha_compatible.contains(dependency.as_str()) {
                    alpha_dependencies.push(dependency.clone());
                } else if kernel_shape_compatible.contains(dependency.as_str()) {
                    kernel_shape_dependencies.push(dependency.clone());
                } else if type_mismatched.contains(dependency.as_str()) {
                    type_mismatched_dependencies.push(dependency.clone());
                } else {
                    return Err(format!(
                        "shared dependency was absent from overlap partition: {dependency}"
                    ));
                }
            }
            Ok(json!({
                "theorem": theorem,
                "native_dependency_count": dependencies.len(),
                "missing_dependency_names": missing,
                "exact_dependency_names": exact_dependencies,
                "alpha_type_compatible_dependency_names": alpha_dependencies,
                "kernel_type_shape_compatible_dependency_names": kernel_shape_dependencies,
                "type_mismatched_dependency_names": type_mismatched_dependencies,
            }))
        })
        .collect()
}

fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        let _ = write!(hex, "{byte:02x}");
    }
    hex
}
