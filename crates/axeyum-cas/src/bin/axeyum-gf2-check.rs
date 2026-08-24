//! Standalone dual checker for canonical `GF(2)` half-degree artifacts.

use std::fs;
use std::path::PathBuf;

use axeyum_cas::gf2_artifact::{ArtifactLimits, from_canonical_json};

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_CHECK|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os();
    let _program = arguments.next();
    let path = PathBuf::from(
        arguments
            .next()
            .ok_or_else(|| "usage: axeyum-gf2-check <artifact.json>".to_owned())?,
    );
    if arguments.next().is_some() {
        return Err("usage: axeyum-gf2-check <artifact.json>".to_owned());
    }
    let limits = ArtifactLimits::default();
    let metadata = fs::metadata(&path).map_err(|error| format!("{}: {error}", path.display()))?;
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
    let degree = artifact.certificate.polynomial.degree().unwrap_or(0);
    println!(
        "GF2_CHECK|status=PASS|id={}|degree={degree}|primary=PASS|independent=PASS",
        artifact.id
    );
    Ok(())
}
