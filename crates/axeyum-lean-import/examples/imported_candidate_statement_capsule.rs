//! Materialize one imported theorem type as a proof-free diagnostic capsule.
//!
//! Definition abstraction proves proof isolation, not semantic sufficiency.
//! The committed audit separately rejects this unconstrained generalized goal
//! for execution using a concrete countermodel.

use std::env;
use std::fmt::Write;
use std::fs;
use std::io::Cursor;

use axeyum_lean_import::{
    ImportLimits, generalize_goal_constants, import_ndjson, import_statement_ndjson,
    select_definition_abstractions_auto_param_binders_v3,
};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, NameId, ReducibilityHint};
use sha2::{Digest, Sha256};

const FRESH_TARGET: &str = "Axeyum.Autogenesis.ImportedCandidateGoal";

fn main() {
    if let Err(error) = run() {
        eprintln!("imported-candidate-statement-capsule: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = env::args().skip(1);
    let source_path = arguments.next().ok_or_else(usage)?;
    let candidate = arguments.next().ok_or_else(usage)?;
    let output_path = arguments.next().ok_or_else(usage)?;
    if arguments.next().is_some() {
        return Err(usage());
    }
    let source_bytes =
        fs::read(&source_path).map_err(|error| format!("cannot read {source_path}: {error}"))?;
    let completed = import_ndjson(Cursor::new(source_bytes), ImportLimits::default())
        .map_err(|error| format!("cannot import {source_path}: {error:?}"))?;
    let (mut kernel, report) = completed.into_parts();
    let candidate_name = find_name(&kernel, &candidate)?;
    let candidate_type = match kernel.environment().get(candidate_name) {
        Some(Declaration::Theorem { uparams, ty, .. }) if uparams.is_empty() => *ty,
        Some(Declaration::Theorem { .. }) => {
            return Err(format!("{candidate} is universe-polymorphic"));
        }
        _ => return Err(format!("{candidate} is not an imported theorem")),
    };
    let inferred = kernel
        .infer(candidate_type)
        .map_err(|error| format!("cannot infer {candidate} type: {error:?}"))?;
    let prop = kernel.sort_zero();
    if !kernel.def_eq(inferred, prop) {
        return Err(format!("{candidate} type is not Prop"));
    }
    let abstractions =
        select_definition_abstractions_auto_param_binders_v3(&mut kernel, candidate_type)
            .map_err(|error| format!("cannot select proof-isolating abstractions: {error}"))?;
    let generalized = generalize_goal_constants(&mut kernel, candidate_type, &abstractions)
        .map_err(|error| format!("cannot generalize candidate type: {error}"))?;
    let target_name = nested_name(&mut kernel, FRESH_TARGET)?;
    if kernel.environment().get(target_name).is_some() {
        return Err(format!("reserved target {FRESH_TARGET} already exists"));
    }
    kernel
        .add_declaration(Declaration::Definition {
            name: target_name,
            uparams: vec![],
            ty: prop,
            value: generalized.goal,
            hint: ReducibilityHint::Regular(0),
        })
        .map_err(|error| format!("cannot add proof-free target: {error:?}"))?;
    let metadata = Lean4ExportMetadata::axeyum(report.lean_version);
    let (stream, normalization) = kernel
        .render_lean4export_ndjson_roots_checked_auto_param_binders(&metadata, &[target_name])
        .map_err(|error| format!("cannot render root-selected stream: {error}"))?;
    if stream
        .as_bytes()
        .windows(candidate.len())
        .any(|window| window == candidate.as_bytes())
    {
        return Err("root-selected stream still names the source theorem".to_owned());
    }
    let fresh = import_statement_ndjson(
        Cursor::new(stream.as_bytes()),
        ImportLimits::default(),
        FRESH_TARGET,
    )
    .map_err(|error| format!("fresh proof-isolated import failed: {error:?}"))?;
    let goal = fresh.kernel().render_lean(fresh.goal());
    let footprint: Vec<_> = fresh
        .kernel()
        .axiom_footprint(fresh.target_name())
        .into_iter()
        .map(|name| fresh.kernel().display_name(name).to_string())
        .collect();
    fs::write(&output_path, &stream)
        .map_err(|error| format!("cannot write {output_path}: {error}"))?;
    println!(
        "IMPORTED_CANDIDATE_STATEMENT_DIAGNOSTIC_OK|candidate={candidate}|target={FRESH_TARGET}|execution_eligible=false|bytes={}|sha256={}|goal_sha256={}|declarations={}|abstractions={}|normalization_rewrites={}|axiom_footprint={}",
        stream.len(),
        sha256(stream.as_bytes()),
        sha256(goal.as_bytes()),
        fresh.report().declaration_identities.len(),
        abstractions.len(),
        normalization.rewritten_occurrences,
        footprint.join(","),
    );
    Ok(())
}

fn usage() -> String {
    "usage: imported_candidate_statement_capsule <source-stream> <candidate> <output>".to_owned()
}

fn find_name(kernel: &Kernel, requested: &str) -> Result<NameId, String> {
    let found: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(name, _)| {
            (kernel.display_name(*name).to_string() == requested).then_some(*name)
        })
        .collect();
    match found.as_slice() {
        [name] => Ok(*name),
        [] => Err(format!("{requested} is absent")),
        _ => Err(format!("{requested} is ambiguous")),
    }
}

fn nested_name(kernel: &mut Kernel, rendered: &str) -> Result<NameId, String> {
    let mut current = kernel.anon();
    for part in rendered.split('.') {
        if part.is_empty() {
            return Err("fresh target contains an empty name part".to_owned());
        }
        current = kernel.name_str(current, part);
    }
    Ok(current)
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .fold(String::with_capacity(64), |mut output, byte| {
            write!(output, "{byte:02x}").expect("writing to a String cannot fail");
            output
        })
}
