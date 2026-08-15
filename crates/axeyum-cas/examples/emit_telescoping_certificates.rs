//! Regenerate the committed creative-telescoping certificates under
//! `artifacts/cas-certificates/`.
//!
//! ```sh
//! cargo run -p axeyum-cas --example emit_telescoping_certificates
//! ```
//!
//! The certificates are the *evidence* for the `cas-certificate` facts, so this
//! binary only writes a file after the independent checker has accepted what it
//! is about to write. A search that regresses produces a loud failure here, not a
//! quietly weakened artifact.
//!
//! Re-checking the committed files is a separate program that shares nothing with
//! this one: `cargo test -p axeyum-cas --test telescoping_certificate_artifacts`.

use std::path::PathBuf;
use std::process::ExitCode;

use axeyum_cas::mvpoly::MvPoly;
use axeyum_cas::telescoping::{
    Factor, HyperTerm, Limits, LinearForm, TelescopingOutcome, binomial_factors, zeilberger,
};
use axeyum_cas::telescoping_check::{
    CheckOptions, check_certificate, check_closed_form, check_closed_form_symbolic,
};
use axeyum_cas::telescoping_json::{CertificateDocument, ClosedFormClaim, to_json};
use axeyum_ir::Rational;

fn form(terms: &[(&str, i64)], constant: i64) -> LinearForm {
    LinearForm::new(terms, constant)
}

/// `C(n,k)^power`.
fn binomial_n_k(power: i32) -> Vec<Factor> {
    binomial_factors(&form(&[("n", 1)], 0), &form(&[("k", 1)], 0), power)
}

/// One identity to certify.
struct Identity {
    id: &'static str,
    title: &'static str,
    term: HyperTerm,
    shift_var: &'static str,
    sum_var: &'static str,
    options: CheckOptions,
    closed_form: Option<ClosedFormClaim>,
}

/// The single-parameter binomial row sums.
fn row_sum_identities() -> Vec<Identity> {
    let mut alternating = vec![Factor::Power {
        base: Rational::integer(-1),
        form: form(&[("k", 1)], 0),
    }];
    alternating.extend(binomial_n_k(1));

    let mut weighted = vec![Factor::Poly {
        poly: MvPoly::var("k"),
        exponent: 1,
    }];
    weighted.extend(binomial_n_k(1));

    vec![
        Identity {
            id: "binomial-row-sum-two-power",
            title: "sum_k C(n,k) = 2^n",
            term: HyperTerm::new(binomial_n_k(1)),
            shift_var: "n",
            sum_var: "k",
            options: CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6, 7], (-2, 14)),
            closed_form: Some(ClosedFormClaim {
                term: HyperTerm::new(vec![Factor::Power {
                    base: Rational::integer(2),
                    form: form(&[("n", 1)], 0),
                }]),
                base: 0,
                symbolic: false,
            }),
        },
        Identity {
            id: "alternating-binomial-row-sum-zero",
            title: "sum_k (-1)^k C(n,k) = 0 for n >= 1 (order-0 certificate: n*S(n) = 0)",
            term: HyperTerm::new(alternating),
            shift_var: "n",
            sum_var: "k",
            options: CheckOptions::over("n", &[1, 2, 3, 4, 5, 6, 7], (-2, 14)),
            closed_form: None,
        },
        Identity {
            id: "squared-binomial-row-sum-central",
            title: "sum_k C(n,k)^2 = C(2n,n)",
            term: HyperTerm::new(binomial_n_k(2)),
            shift_var: "n",
            sum_var: "k",
            options: CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6], (-2, 12)),
            closed_form: Some(ClosedFormClaim {
                term: HyperTerm::new(binomial_factors(
                    &form(&[("n", 2)], 0),
                    &form(&[("n", 1)], 0),
                    1,
                )),
                base: 0,
                symbolic: false,
            }),
        },
        Identity {
            id: "weighted-binomial-row-sum",
            title: "sum_k k*C(n,k) = n*2^(n-1) for n >= 1",
            term: HyperTerm::new(weighted),
            shift_var: "n",
            sum_var: "k",
            options: CheckOptions::over("n", &[1, 2, 3, 4, 5, 6, 7], (-2, 14)),
            closed_form: Some(ClosedFormClaim {
                term: HyperTerm::new(vec![
                    Factor::Poly {
                        poly: MvPoly::var("n"),
                        exponent: 1,
                    },
                    Factor::Power {
                        base: Rational::new(1, 2),
                        form: form(&[], 1),
                    },
                    Factor::Power {
                        base: Rational::integer(2),
                        form: form(&[("n", 1)], 0),
                    },
                ]),
                base: 1,
                symbolic: false,
            }),
        },
        Identity {
            id: "franel-numbers-recurrence",
            title: "sum_k C(n,k)^3: the order-2 Franel recurrence (no closed form exists)",
            term: HyperTerm::new(binomial_n_k(3)),
            shift_var: "n",
            sum_var: "k",
            options: CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6], (-2, 14)),
            closed_form: None,
        },
    ]
}

/// Apéry's summand, the deepest this route reaches.
fn apery_identity() -> Identity {
    Identity {
        id: "apery-numbers-recurrence",
        title: "sum_k C(n,k)^2*C(n+k,k)^2: Apery's order-2 recurrence (no closed form exists)",
        term: {
            let mut factors = binomial_n_k(2);
            factors.extend(binomial_factors(
                &form(&[("n", 1), ("k", 1)], 0),
                &form(&[("k", 1)], 0),
                2,
            ));
            HyperTerm::new(factors)
        },
        shift_var: "n",
        sum_var: "k",
        // The window starts at k = 0: at n = 0 the summand is not evaluable
        // at a negative k, and the checker refuses a window edge it cannot
        // evaluate. G still vanishes there, which is what it needs to.
        options: CheckOptions::over("n", &[0, 1, 2, 3, 4, 5], (0, 12)),
        closed_form: None,
    }
}

/// The Vandermonde family, which carries symbolic parameters throughout.
fn vandermonde_identities() -> Vec<Identity> {
    let mut convolution = binomial_factors(&form(&[("m", 1)], 0), &form(&[("k", 1)], 0), 1);
    convolution.extend(binomial_factors(
        &form(&[("n", 1)], 0),
        &form(&[("p", 1), ("k", -1)], 0),
        1,
    ));

    let mut cross = binomial_factors(&form(&[("m", 1)], 0), &form(&[("k", 1)], 0), 1);
    cross.extend(binomial_factors(
        &form(&[("n", 1)], 0),
        &form(&[("k", 1)], 0),
        1,
    ));

    vec![
        Identity {
            id: "chu-vandermonde-convolution",
            title: "sum_k C(m,k)*C(n,p-k) = C(m+n,p), symbolic in m and n",
            term: HyperTerm::new(convolution),
            shift_var: "p",
            sum_var: "k",
            options: CheckOptions::over("p", &[0, 1, 2, 3, 4], (-2, 12))
                .with("m", &[3, 5])
                .with("n", &[4, 6]),
            closed_form: Some(ClosedFormClaim {
                term: HyperTerm::new(binomial_factors(
                    &form(&[("m", 1), ("n", 1)], 0),
                    &form(&[("p", 1)], 0),
                    1,
                )),
                base: 0,
                symbolic: true,
            }),
        },
        Identity {
            id: "cross-binomial-row-sum",
            title: "sum_k C(m,k)*C(n,k) = C(m+n,n), symbolic in m",
            term: HyperTerm::new(cross),
            shift_var: "n",
            sum_var: "k",
            options: CheckOptions::over("n", &[0, 1, 2, 3, 4], (-2, 12)).with("m", &[3, 5, 7]),
            closed_form: Some(ClosedFormClaim {
                term: HyperTerm::new(binomial_factors(
                    &form(&[("m", 1), ("n", 1)], 0),
                    &form(&[("n", 1)], 0),
                    1,
                )),
                base: 0,
                symbolic: true,
            }),
        },
    ]
}

fn main() -> ExitCode {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../artifacts/cas-certificates")
        .canonicalize()
        .unwrap_or_else(|_| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../artifacts/cas-certificates")
        });
    if let Err(error) = std::fs::create_dir_all(&directory) {
        eprintln!("cannot create {}: {error}", directory.display());
        return ExitCode::FAILURE;
    }

    let mut failures = 0usize;
    let mut all = row_sum_identities();
    all.push(apery_identity());
    all.extend(vandermonde_identities());
    for identity in all {
        let TelescopingOutcome::Found(certificate) = zeilberger(
            &identity.term,
            identity.shift_var,
            identity.sum_var,
            &Limits::classical(),
        ) else {
            eprintln!("{}: the search declined", identity.id);
            failures += 1;
            continue;
        };
        let verdict = check_certificate(&certificate, &identity.options);
        if !verdict.is_verified() {
            eprintln!(
                "{}: the checker rejected the certificate: {verdict:?}",
                identity.id
            );
            failures += 1;
            continue;
        }
        if let Some(claim) = &identity.closed_form {
            let outcome = if claim.symbolic {
                check_closed_form_symbolic(&certificate, &claim.term, claim.base, &identity.options)
                    .map(|report| format!("{report:?}"))
            } else {
                check_closed_form(&certificate, &claim.term, claim.base, &identity.options)
                    .map(|report| format!("{report:?}"))
            };
            if let Err(reasons) = outcome {
                eprintln!("{}: the closed form was rejected: {reasons:?}", identity.id);
                failures += 1;
                continue;
            }
        }
        let document = CertificateDocument {
            id: identity.id.to_owned(),
            title: identity.title.to_owned(),
            certificate: *certificate,
            options: identity.options,
            closed_form: identity.closed_form,
        };
        let path = directory.join(format!("{}.json", identity.id));
        match std::fs::write(&path, to_json(&document)) {
            Ok(()) => println!(
                "wrote {} (order {})",
                path.display(),
                document.certificate.order()
            ),
            Err(error) => {
                eprintln!("cannot write {}: {error}", path.display());
                failures += 1;
            }
        }
    }
    if failures == 0 {
        ExitCode::SUCCESS
    } else {
        eprintln!("{failures} certificate(s) not written");
        ExitCode::FAILURE
    }
}
