//! Audit checked Lemire witnesses as seeds for cubic Capell composition.

use std::fs;
use std::path::PathBuf;

use axeyum_cas::gf2::{
    certify_irreducible, check_irreducible_certificate, cubic_composition_criterion,
};
use axeyum_cas::gf2_artifact::{ArtifactLimits, from_canonical_json};
use axeyum_cas::gf2_independent::check_irreducible_certificate_independent;

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_CAPELL_AUDIT|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let paths = std::env::args_os()
        .skip(1)
        .map(PathBuf::from)
        .collect::<Vec<_>>();
    if paths.is_empty() {
        return Err("usage: axeyum-gf2-capell-audit <artifact.json>...".to_owned());
    }
    let limits = ArtifactLimits::default();
    let mut degrees = Vec::with_capacity(paths.len());
    let mut eligible = Vec::new();
    let mut odd = 0_usize;
    let mut cubes = 0_usize;
    for path in paths {
        let metadata =
            fs::metadata(&path).map_err(|error| format!("{}: {error}", path.display()))?;
        let observed = usize::try_from(metadata.len()).unwrap_or(usize::MAX);
        if observed > limits.max_bytes {
            return Err(format!(
                "{} has {observed} bytes; limit is {}",
                path.display(),
                limits.max_bytes
            ));
        }
        let input =
            fs::read_to_string(&path).map_err(|error| format!("{}: {error}", path.display()))?;
        let artifact = from_canonical_json(&input, limits).map_err(|error| error.to_string())?;
        let report = cubic_composition_criterion(&artifact.certificate, limits.primary)
            .map_err(|error| format!("{}: {error}", path.display()))?;
        degrees.push(report.source_degree);
        if report.proves_composition_irreducible {
            if !report.source_is_half_degree_shaped || !report.composition.is_half_degree_shaped() {
                return Err(format!(
                    "{}: criterion-positive composition lost the half-degree shape",
                    path.display()
                ));
            }
            let certificate = certify_irreducible(&report.composition, limits.primary)
                .map_err(|error| format!("{}: composition producer: {error}", path.display()))?
                .ok_or_else(|| {
                    format!(
                        "{}: Capell-positive composition failed direct Rabin production",
                        path.display()
                    )
                })?;
            check_irreducible_certificate(&certificate, limits.primary)
                .map_err(|error| format!("{}: composition primary: {error}", path.display()))?;
            check_irreducible_certificate_independent(&certificate, limits.independent)
                .map_err(|error| format!("{}: composition independent: {error}", path.display()))?;
            eligible.push(report.source_degree);
        } else if report.cube_test_residue.is_none() {
            odd += 1;
        } else {
            cubes += 1;
        }
    }
    degrees.sort_unstable();
    eligible.sort_unstable();
    let min_degree = degrees.first().copied().unwrap_or(0);
    let max_degree = degrees.last().copied().unwrap_or(0);
    let eligible_text = eligible
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "GF2_CAPELL_AUDIT|status=PASS|sources={}|min_degree={min_degree}|max_degree={max_degree}|eligible={}|odd_degree={odd}|cube={cubes}|eligible_degrees={eligible_text}",
        degrees.len(),
        eligible.len(),
    );
    Ok(())
}
