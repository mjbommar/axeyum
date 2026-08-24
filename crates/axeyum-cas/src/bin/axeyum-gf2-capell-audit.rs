//! Audit checked Lemire witnesses as seeds for monomial Capell composition.

use std::fs;
use std::path::PathBuf;

use axeyum_cas::gf2::{
    certify_irreducible, check_irreducible_certificate, cubic_composition_criterion,
    monomial_composition_criterion, monomial_prime_eligibility,
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
    let mut arguments = std::env::args_os().skip(1);
    let mut prime_limit = None;
    let mut paths = Vec::new();
    while let Some(argument) = arguments.next() {
        if argument == "--prime-limit" {
            let value = arguments
                .next()
                .ok_or_else(|| "--prime-limit requires an integer".to_owned())?;
            let parsed = value
                .to_str()
                .ok_or_else(|| "--prime-limit is not UTF-8".to_owned())?
                .parse::<usize>()
                .map_err(|_| "--prime-limit is not an integer".to_owned())?;
            if !(5..=50_000_000).contains(&parsed) {
                return Err("--prime-limit must be between 5 and 50000000".to_owned());
            }
            prime_limit = Some(parsed);
        } else {
            paths.push(PathBuf::from(argument));
        }
    }
    if paths.is_empty() {
        return Err(
            "usage: axeyum-gf2-capell-audit [--prime-limit N] <artifact.json>...".to_owned(),
        );
    }
    if let Some(limit) = prime_limit {
        return run_general_prime_audit(&paths, limit);
    }
    run_cubic_audit(&paths)
}

fn run_cubic_audit(paths: &[PathBuf]) -> Result<(), String> {
    let limits = ArtifactLimits::default();
    let mut degrees = Vec::with_capacity(paths.len());
    let mut eligible = Vec::new();
    let mut odd = 0_usize;
    let mut cubes = 0_usize;
    for path in paths {
        let metadata =
            fs::metadata(path).map_err(|error| format!("{}: {error}", path.display()))?;
        let observed = usize::try_from(metadata.len()).unwrap_or(usize::MAX);
        if observed > limits.max_bytes {
            return Err(format!(
                "{} has {observed} bytes; limit is {}",
                path.display(),
                limits.max_bytes
            ));
        }
        let input =
            fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))?;
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

fn odd_primes_through(limit: usize) -> Vec<usize> {
    let mut composite = vec![false; limit + 1];
    let mut prime = 2_usize;
    while prime <= limit / prime {
        if !composite[prime] {
            let mut multiple = prime * prime;
            while multiple <= limit {
                composite[multiple] = true;
                multiple += prime;
            }
        }
        prime += 1;
    }
    (3..=limit)
        .step_by(2)
        .filter(|&candidate| !composite[candidate])
        .collect()
}

fn two_power_mod(exponent: usize, modulus: usize) -> usize {
    let modulus_wide = modulus as u128;
    let mut result = 1_u128;
    let mut base = 2_u128 % modulus_wide;
    let mut remaining = exponent;
    while remaining > 0 {
        if remaining & 1 == 1 {
            result = result * base % modulus_wide;
        }
        base = base * base % modulus_wide;
        remaining >>= 1;
    }
    usize::try_from(result).expect("modular residue is below usize modulus")
}

#[allow(clippy::too_many_lines)]
fn run_general_prime_audit(paths: &[PathBuf], prime_limit: usize) -> Result<(), String> {
    let limits = ArtifactLimits::default();
    let primes = odd_primes_through(prime_limit);
    let mut degrees = Vec::with_capacity(paths.len());
    let mut eligible_rays = Vec::new();
    let mut odd_eligible = 0_usize;
    let mut direct_certificates = 0_usize;
    let mut falsification_controls = 0_usize;
    for path in paths {
        let metadata =
            fs::metadata(path).map_err(|error| format!("{}: {error}", path.display()))?;
        let observed = usize::try_from(metadata.len()).unwrap_or(usize::MAX);
        if observed > limits.max_bytes {
            return Err(format!(
                "{} has {observed} bytes; limit is {}",
                path.display(),
                limits.max_bytes
            ));
        }
        let input =
            fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))?;
        let artifact = from_canonical_json(&input, limits).map_err(|error| error.to_string())?;
        check_irreducible_certificate(&artifact.certificate, limits.primary)
            .map_err(|error| format!("{}: source certificate: {error}", path.display()))?;
        let degree = artifact
            .certificate
            .polynomial
            .degree()
            .ok_or_else(|| format!("{}: source has degree zero", path.display()))?;
        if !artifact.certificate.polynomial.is_half_degree_shaped() {
            return Err(format!(
                "{}: source is not half-degree shaped",
                path.display()
            ));
        }
        degrees.push(degree);

        let wrong_prime = primes
            .iter()
            .copied()
            .find(|&prime| two_power_mod(degree, prime) != 1)
            .ok_or_else(|| format!("degree {degree}: no falsification prime within limit"))?;
        let wrong = monomial_prime_eligibility(&artifact.certificate, wrong_prime, limits.primary)
            .map_err(|error| format!("{}: falsification control: {error}", path.display()))?;
        if wrong.divides_source_group_order || wrong.root_is_not_prime_power {
            return Err(format!(
                "{}: incompatible prime {wrong_prime} passed the falsification control",
                path.display()
            ));
        }
        falsification_controls += 1;

        let mut eligible_prime = None;
        for prime in primes
            .iter()
            .copied()
            .filter(|&prime| two_power_mod(degree, prime) == 1)
        {
            let test = monomial_prime_eligibility(&artifact.certificate, prime, limits.primary)
                .map_err(|error| format!("{}: prime {prime}: {error}", path.display()))?;
            if !test.divides_source_group_order {
                return Err(format!(
                    "{}: modular prefilter and exact group-order test disagree at {prime}",
                    path.display()
                ));
            }
            if test.root_is_not_prime_power {
                eligible_prime = Some(prime);
                break;
            }
        }
        let Some(prime) = eligible_prime else {
            continue;
        };
        eligible_rays.push((degree, prime));
        if degree % 2 == 1 {
            odd_eligible += 1;
        }

        let output_degree = degree.saturating_mul(prime);
        // The prime-local criterion already proves the ray.  Retain two
        // independent whole-composition Rabin checks as bounded spot checks;
        // the independent oracle's default work ceiling is intentionally not
        // sized for every product degree through 4096.
        if output_degree <= 256.min(limits.primary.max_input_degree) {
            let report =
                monomial_composition_criterion(&artifact.certificate, prime, limits.primary)
                    .map_err(|error| {
                        format!("{}: composition criterion: {error}", path.display())
                    })?;
            if !report.proves_composition_irreducible || !report.composition.is_half_degree_shaped()
            {
                return Err(format!(
                    "{}: eligibility-positive composition failed its criterion or shape",
                    path.display()
                ));
            }
            let certificate = certify_irreducible(&report.composition, limits.primary)
                .map_err(|error| format!("{}: composition producer: {error}", path.display()))?
                .ok_or_else(|| {
                    format!(
                        "{}: criterion-positive composition failed direct Rabin production",
                        path.display()
                    )
                })?;
            check_irreducible_certificate(&certificate, limits.primary)
                .map_err(|error| format!("{}: composition primary: {error}", path.display()))?;
            check_irreducible_certificate_independent(&certificate, limits.independent)
                .map_err(|error| format!("{}: composition independent: {error}", path.display()))?;
            direct_certificates += 1;
        }
    }
    degrees.sort_unstable();
    eligible_rays.sort_unstable();
    let min_degree = degrees.first().copied().unwrap_or(0);
    let max_degree = degrees.last().copied().unwrap_or(0);
    let ray_text = eligible_rays
        .iter()
        .map(|(degree, prime)| format!("{degree}:{prime}"))
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "GF2_GENERAL_CAPELL_AUDIT|status=PASS|sources={}|min_degree={min_degree}|max_degree={max_degree}|prime_limit={prime_limit}|eligible={}|odd_eligible={odd_eligible}|direct_certificates={direct_certificates}|falsification_controls={falsification_controls}|eligible_rays={ray_text}",
        degrees.len(),
        eligible_rays.len(),
    );
    Ok(())
}
