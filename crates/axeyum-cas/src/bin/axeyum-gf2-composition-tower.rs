//! Find a certified nonmonomial shaped-composition tower from one artifact.

use std::fs;
use std::path::PathBuf;

use axeyum_cas::gf2::{
    Gf2Error, Gf2Limits, Gf2Poly, IrreducibilityCertificate, ShapedCompositionSearchHit,
    certify_irreducible, check_irreducible_certificate, search_shaped_compositions,
};
use axeyum_cas::gf2_artifact::{ArtifactLimits, from_canonical_json};

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_COMPOSITION_TOWER|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn parse_usize(value: Option<String>, name: &str) -> Result<usize, String> {
    value
        .ok_or_else(|| format!("missing {name}"))?
        .parse::<usize>()
        .map_err(|_| format!("invalid {name}"))
}

fn find_chain(
    source: &IrreducibilityCertificate,
    substitution_degree: usize,
    depth: usize,
    max_candidates: usize,
    limits: Gf2Limits,
) -> Result<Option<Vec<ShapedCompositionSearchHit>>, Gf2Error> {
    if depth == 0 {
        return Ok(Some(Vec::new()));
    }
    let report = search_shaped_compositions(source, substitution_degree, max_candidates, limits)?;
    for hit in report.hits {
        if let Some(mut suffix) = find_chain(
            &hit.composition_certificate,
            substitution_degree,
            depth - 1,
            max_candidates,
            limits,
        )? {
            suffix.insert(0, hit);
            return Ok(Some(suffix));
        }
    }
    Ok(None)
}

fn words_text(certificate: &IrreducibilityCertificate) -> String {
    certificate
        .polynomial
        .words()
        .iter()
        .map(|word| format!("{word:016x}"))
        .collect::<Vec<_>>()
        .join(",")
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args().skip(1);
    let source_argument = arguments.next().ok_or_else(|| {
        "usage: axeyum-gf2-composition-tower <artifact|hex:WORDS> <k> <depth> [max-word-ops]"
            .to_owned()
    })?;
    let substitution_degree = parse_usize(arguments.next(), "substitution degree")?;
    let depth = parse_usize(arguments.next(), "depth")?;
    let max_word_ops = arguments
        .next()
        .map(|value| {
            value
                .parse::<u64>()
                .map_err(|_| "invalid max-word-ops".to_owned())
        })
        .transpose()?
        .unwrap_or(2_000_000_000);
    if arguments.next().is_some() {
        return Err("too many arguments".to_owned());
    }
    if depth == 0 || substitution_degree == 0 {
        return Err("substitution degree and depth must be positive".to_owned());
    }
    let source_certificate = if let Some(words) = source_argument.strip_prefix("hex:") {
        let packed = words
            .split(',')
            .map(|word| {
                u64::from_str_radix(word, 16)
                    .map_err(|_| "invalid hexadecimal source word".to_owned())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let polynomial = Gf2Poly::from_words(packed);
        certify_irreducible(&polynomial, Gf2Limits::default())
            .map_err(|error| error.to_string())?
            .ok_or_else(|| "hexadecimal source polynomial is reducible".to_owned())?
    } else {
        let path = PathBuf::from(&source_argument);
        let input =
            fs::read_to_string(&path).map_err(|error| format!("{}: {error}", path.display()))?;
        from_canonical_json(&input, ArtifactLimits::default())
            .map_err(|error| error.to_string())?
            .certificate
    };
    let base_degree = source_certificate
        .polynomial
        .degree()
        .ok_or_else(|| "source has degree zero".to_owned())?;
    let target_degree = (0..depth).try_fold(base_degree, |degree, _| {
        degree
            .checked_mul(substitution_degree)
            .ok_or_else(|| "tower degree overflow".to_owned())
    })?;
    let limits = Gf2Limits {
        max_input_degree: target_degree,
        max_intermediate_degree: target_degree.saturating_mul(2),
        max_frobenius_steps: target_degree,
        max_word_ops,
    };
    check_irreducible_certificate(&source_certificate, limits)
        .map_err(|error| format!("source certificate: {error}"))?;
    let free_width = substitution_degree / 2 + 1;
    let max_candidates = 1_usize
        .checked_shl(
            u32::try_from(free_width).map_err(|_| "candidate exponent overflow".to_owned())?,
        )
        .ok_or_else(|| "candidate count overflow".to_owned())?
        - 1;
    let chain = find_chain(
        &source_certificate,
        substitution_degree,
        depth,
        max_candidates,
        limits,
    )
    .map_err(|error| error.to_string())?
    .ok_or_else(|| "no certified tower at the requested depth".to_owned())?;
    let mut degrees = vec![base_degree];
    let mut substitutions = Vec::new();
    let mut outputs = Vec::new();
    for hit in &chain {
        let degree = hit
            .composition_certificate
            .polynomial
            .degree()
            .ok_or_else(|| "tower output has degree zero".to_owned())?;
        degrees.push(degree);
        substitutions.push(
            hit.substitution
                .exponents()
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join(","),
        );
        outputs.push(words_text(&hit.composition_certificate));
    }
    println!(
        "GF2_COMPOSITION_TOWER|status=PASS|base_degree={base_degree}|substitution_degree={substitution_degree}|depth={depth}|degrees={}|substitutions={}|output_words={}",
        degrees
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(","),
        substitutions.join(";"),
        outputs.join(";")
    );
    Ok(())
}
