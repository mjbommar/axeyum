//! Re-derive a committed sum-of-squares certificate from its artifact file.
//!
//! ```text
//! usage: sos_certify <file.json> [--expect-kind KIND] [--expect-id ID]
//!                                [--expect-checks N] [--expect-rate NUM/DEN]
//!                                [--show]
//! ```
//!
//! Every flag is an assertion about *content*, and the run fails when the
//! content is not what was asserted. The design constraint this binary was
//! written under is the 2026-08-15 ledger audit, which found 40 of 162 checker
//! runs exiting zero on completion alone: so a run that discharges no obligation
//! is a failure here, not a pass, and `--expect-checks` exists so that a
//! certificate quietly shrinking to fewer obligations is caught by the fact that
//! cites it rather than by nobody.
//!
//! Nothing about the mathematics is read from the file beyond the system, the
//! candidate functions and the squares. The Lie derivatives, the norm, the
//! monomial basis and the moment matrix are all rebuilt here.

use std::path::PathBuf;
use std::process::ExitCode;

use axeyum_cas::sos::{self, SosArtifact, json};

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("sos_certify: {message}");
            ExitCode::FAILURE
        }
    }
}

struct Args {
    path: PathBuf,
    expect_kind: Option<String>,
    expect_id: Option<String>,
    expect_checks: Option<usize>,
    expect_rate: Option<(i128, i128)>,
    show: bool,
}

fn parse_args() -> Result<Args, String> {
    let mut path: Option<PathBuf> = None;
    let mut expect_kind = None;
    let mut expect_id = None;
    let mut expect_checks = None;
    let mut expect_rate = None;
    let mut show = false;

    let mut argv = std::env::args().skip(1);
    while let Some(argument) = argv.next() {
        match argument.as_str() {
            "--expect-kind" => {
                expect_kind = Some(argv.next().ok_or("--expect-kind needs a value")?);
            }
            "--expect-id" => {
                expect_id = Some(argv.next().ok_or("--expect-id needs a value")?);
            }
            "--expect-checks" => {
                let value = argv.next().ok_or("--expect-checks needs a value")?;
                expect_checks = Some(
                    value
                        .parse::<usize>()
                        .map_err(|_| format!("`{value}` is not a count"))?,
                );
            }
            "--expect-rate" => {
                let value = argv.next().ok_or("--expect-rate needs a value")?;
                expect_rate = Some(parse_rate(&value)?);
            }
            "--show" => show = true,
            other if other.starts_with("--") => {
                return Err(format!(
                    "unknown flag `{other}`; an ignored flag is an assertion that never ran"
                ));
            }
            other => {
                if path.is_some() {
                    return Err("more than one artifact path given".into());
                }
                path = Some(PathBuf::from(other));
            }
        }
    }
    Ok(Args {
        path: path.ok_or(
            "usage: sos_certify <file.json> [--expect-kind KIND] [--expect-id ID] \
             [--expect-checks N] [--expect-rate NUM/DEN] [--show]",
        )?,
        expect_kind,
        expect_id,
        expect_checks,
        expect_rate,
        show,
    })
}

fn parse_rate(text: &str) -> Result<(i128, i128), String> {
    let (numerator, denominator) = text
        .split_once('/')
        .ok_or_else(|| format!("`{text}` is not a NUM/DEN rate"))?;
    Ok((
        numerator
            .trim()
            .parse::<i128>()
            .map_err(|_| format!("`{text}` has a non-integer numerator"))?,
        denominator
            .trim()
            .parse::<i128>()
            .map_err(|_| format!("`{text}` has a non-integer denominator"))?,
    ))
}

fn run() -> Result<(), String> {
    let args = parse_args()?;
    let text = std::fs::read_to_string(&args.path)
        .map_err(|error| format!("cannot read {}: {error}", args.path.display()))?;
    let artifact =
        json::from_json(&text).map_err(|message| format!("{}: {message}", args.path.display()))?;

    if let Some(expected) = &args.expect_kind
        && artifact.kind() != expected
    {
        return Err(format!(
            "expected a `{expected}` certificate, the file is `{}`",
            artifact.kind()
        ));
    }
    if let Some(expected) = &args.expect_id
        && artifact.id() != expected
    {
        return Err(format!(
            "expected the certificate `{expected}`, the file is `{}`",
            artifact.id()
        ));
    }

    let report = sos::check(&artifact)
        .map_err(|message| format!("{} REJECTED: {message}", artifact.id()))?;

    // A checker that discharged nothing and exited zero is indistinguishable
    // from one that passed. It is a failure here.
    if report.is_empty() {
        return Err(format!(
            "{} discharged ZERO obligations; a check that never ran is not a check that passed",
            artifact.id()
        ));
    }
    if let Some(expected) = args.expect_checks
        && expected != report.len()
    {
        return Err(format!(
            "expected {expected} obligations, discharged {}",
            report.len()
        ));
    }

    match (args.expect_rate, report.rate) {
        (Some((numerator, denominator)), Some(rate)) => {
            let wanted = axeyum_ir::Rational::checked_new(numerator, denominator)
                .ok_or("--expect-rate is out of the exact rational range")?;
            if rate != wanted {
                return Err(format!(
                    "expected the certified decay rate {numerator}/{denominator}, got {}/{}",
                    rate.numerator(),
                    rate.denominator()
                ));
            }
        }
        (Some(_), None) => {
            return Err(format!(
                "--expect-rate was given but a `{}` certificate reports no rate",
                artifact.kind()
            ));
        }
        (None, _) => {}
    }

    if args.show {
        for obligation in &report.obligations {
            println!("  {:<40} {}", obligation.name, obligation.detail);
        }
        if let SosArtifact::PsdNotSos(problem, certificate) = &artifact {
            println!(
                "  {:<40} the dual functional is supported on {} of the degree-{} monomials",
                "dual-support",
                certificate.dual.len(),
                u64::from(problem.half_degree) * 2
            );
        }
    }

    println!(
        "VERIFIED  {}  [{}]  {} obligation(s) re-derived{}",
        artifact.id(),
        artifact.kind(),
        report.len(),
        report.rate.map_or_else(String::new, |rate| format!(
            ", certified decay rate {}/{}",
            rate.numerator(),
            rate.denominator()
        ))
    );
    Ok(())
}
