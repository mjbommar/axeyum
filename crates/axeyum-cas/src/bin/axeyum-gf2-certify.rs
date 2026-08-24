//! Produce one canonical half-degree artifact from an explicit polynomial.

use std::fs::{self, OpenOptions};
use std::io::Write as _;
use std::path::{Path, PathBuf};

use axeyum_cas::gf2::{Gf2Limits, Gf2Poly, certify_irreducible};
use axeyum_cas::gf2_artifact::{ArtifactLimits, HalfDegreeArtifact, to_canonical_json};

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_CERTIFY|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os();
    let _program = arguments.next();
    let output = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let id = arguments
        .next()
        .ok_or_else(usage)?
        .into_string()
        .map_err(|_| "artifact id is not UTF-8".to_owned())?;
    let producer = arguments
        .next()
        .ok_or_else(usage)?
        .into_string()
        .map_err(|_| "producer identity is not UTF-8".to_owned())?;
    let exponent_text = arguments
        .next()
        .ok_or_else(usage)?
        .into_string()
        .map_err(|_| "exponent list is not UTF-8".to_owned())?;
    if arguments.next().is_some() {
        return Err(usage());
    }

    let exponents = parse_exponents(&exponent_text)?;
    let artifact_limits = ArtifactLimits::default();
    let polynomial = Gf2Poly::from_exponents(&exponents, artifact_limits.primary)
        .map_err(|error| error.to_string())?;
    let certificate = certify_irreducible(&polynomial, Gf2Limits::default())
        .map_err(|error| error.to_string())?
        .ok_or_else(|| "candidate is reducible".to_owned())?;
    let artifact = HalfDegreeArtifact {
        id,
        producer,
        certificate,
    };
    let json = to_canonical_json(&artifact, artifact_limits).map_err(|error| error.to_string())?;
    write_new_atomic(&output, json.as_bytes())?;
    println!(
        "GF2_CERTIFY|status=PASS|path={}|degree={}|bytes={}",
        output.display(),
        polynomial.degree().unwrap_or(0),
        json.len()
    );
    Ok(())
}

fn usage() -> String {
    "usage: axeyum-gf2-certify <output.json> <id> <producer> <ascending-comma-exponents>".to_owned()
}

fn parse_exponents(text: &str) -> Result<Vec<usize>, String> {
    if text.is_empty() {
        return Err("exponent list is empty".to_owned());
    }
    let mut result = Vec::new();
    for item in text.split(',') {
        if item.is_empty() || (item.len() > 1 && item.starts_with('0')) {
            return Err("exponents must be canonical decimal integers".to_owned());
        }
        let exponent = item
            .parse::<usize>()
            .map_err(|_| format!("invalid exponent: {item}"))?;
        if result.last().is_some_and(|previous| *previous >= exponent) {
            return Err("exponents must be strictly increasing".to_owned());
        }
        result.push(exponent);
    }
    Ok(result)
}

fn write_new_atomic(path: &Path, bytes: &[u8]) -> Result<(), String> {
    if path.exists() {
        return Err(format!("{} already exists", path.display()));
    }
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    if !parent.is_dir() {
        return Err(format!(
            "parent directory {} does not exist",
            parent.display()
        ));
    }
    let file_name = path
        .file_name()
        .ok_or_else(|| "output path has no file name".to_owned())?
        .to_string_lossy();
    let temporary = parent.join(format!(".{file_name}.tmp-{}", std::process::id()));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)
        .map_err(|error| format!("{}: {error}", temporary.display()))?;
    if let Err(error) = file.write_all(bytes).and_then(|()| file.sync_all()) {
        let _ = fs::remove_file(&temporary);
        return Err(format!("{}: {error}", temporary.display()));
    }
    drop(file);
    if let Err(error) = fs::rename(&temporary, path) {
        let _ = fs::remove_file(&temporary);
        return Err(format!(
            "{} -> {}: {error}",
            temporary.display(),
            path.display()
        ));
    }
    Ok(())
}
