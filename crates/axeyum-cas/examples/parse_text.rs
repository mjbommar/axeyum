//! Parse bounded exact CAS text and export canonical syntax without certification.
use std::io::{self, BufRead};

fn main() {
    for line in io::stdin().lock().lines() {
        let source = match line {
            Ok(source) => source,
            Err(error) => {
                eprintln!("input error: {error}");
                std::process::exit(1);
            }
        };
        match axeyum_cas::text_parser::parse(&source).and_then(|expr| {
            axeyum_cas::expression_wire::to_json(&expr).map_err(|error| {
                axeyum_cas::text_parser::ParseError {
                    message: error.to_string(),
                    start: 0,
                    end: source.len(),
                }
            })
        }) {
            Ok(json) => println!("{json}"),
            Err(error) => {
                eprintln!("{error}");
                std::process::exit(1);
            }
        }
    }
}
