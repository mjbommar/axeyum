//! The cover status ledger: one flushed row per finished cell.
//!
//! # Finding B2, and the two things that fix it
//!
//! The scratch harness opened its status file with `create(true).append(true)`.
//! A restarted run therefore appended to the previous run's rows, and the result
//! was a 1093-row ledger over a 1024-cell product carrying 69 duplicates. It was
//! caught only because a downstream checker verified the cover was exactly the
//! product — which is to say, it was caught by luck and a good habit rather than
//! by the ledger.
//!
//! Two independent defences now sit on it:
//!
//! * **The writer refuses to append.** [`LedgerWriter::create`] opens with
//!   `create_new`, so an existing path is [`SearchError::LedgerExists`] rather
//!   than a silent concatenation. A restart that genuinely wants its own file
//!   asks for one: [`run_ledger_path`] stamps the run id into the name, and each
//!   row carries its [`RunId`] as well.
//! * **The reader detects duplicates regardless.** [`parse_ledger`] rejects a
//!   repeated cell index whatever run ids the rows carry, so a ledger
//!   concatenated by any other route — a shell redirect, a copy, an older
//!   binary — is still caught. A ledger this crate cannot have written is
//!   exactly the one worth being suspicious of.
//!
//! The row format is tab-separated with a fixed header:
//!
//! ```text
//! run  index  choices  verdict  solve_s  steps  adds  check  check_s
//! ```

use std::fs::{File, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::SearchError;
use crate::cover::{CellCheck, CellRecord, CellVerdict};

/// The header line every ledger this crate writes starts with.
pub const LEDGER_HEADER: &str =
    "run\tindex\tchoices\tverdict\tsolve_s\tsteps\tadds\tcheck\tcheck_s";

/// Identifier stamped on every row a run writes.
///
/// Run ids are supplied by the caller, never invented: determinism is a public
/// API promise, and a ledger whose contents depend on a clock read cannot be
/// compared byte for byte between reruns.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RunId(String);

impl RunId {
    /// Builds a run id from a string.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] unless the id is a non-empty
    /// string of ASCII alphanumerics, `.`, `_`, or `-` — it has to be safe both
    /// in a filename and in a tab-separated field.
    pub fn new(id: impl Into<String>) -> Result<Self, SearchError> {
        let id = id.into();
        let usable = !id.is_empty()
            && id
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-'));
        if usable {
            Ok(Self(id))
        } else {
            Err(SearchError::InvalidParameter {
                what: format!("run id {id:?} must be non-empty [A-Za-z0-9._-]"),
            })
        }
    }

    /// The id as a string.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Default for RunId {
    fn default() -> Self {
        Self("run".to_string())
    }
}

impl core::fmt::Display for RunId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(&self.0)
    }
}

/// The per-run ledger path for a stem, e.g. `cover` and run `a2` give
/// `cover.run-a2.tsv`.
///
/// This is the supported way to restart a cover without touching the previous
/// run's rows.
pub fn run_ledger_path(stem: &Path, run: &RunId) -> PathBuf {
    let mut name = stem.as_os_str().to_os_string();
    name.push(format!(".run-{run}.tsv"));
    PathBuf::from(name)
}

/// Renders one ledger row, newline included.
pub fn render_row(record: &CellRecord) -> String {
    let choices: Vec<String> = record.choices.iter().map(usize::to_string).collect();
    format!(
        "{run}\t{index}\t{choices}\t{verdict}\t{solve:.3}\t{steps}\t{adds}\t{check}\t{check_s:.3}\n",
        run = record.run,
        index = record.index,
        choices = choices.join(","),
        verdict = record.verdict.as_str(),
        solve = record.solve.as_secs_f64(),
        steps = record.steps,
        adds = record.adds,
        check = record.check.as_field(),
        check_s = record.check_time.as_secs_f64(),
    )
}

/// Renders a whole ledger, header included.
pub fn render_ledger(records: &[CellRecord]) -> String {
    let mut out = String::from(LEDGER_HEADER);
    out.push('\n');
    for record in records {
        out.push_str(&render_row(record));
    }
    out
}

/// Parses a ledger, rejecting duplicates.
///
/// A cell index that appears twice is [`SearchError::DuplicateCell`] **whatever
/// run ids the rows carry**. Rows from two runs are still two rows for one cell,
/// and the certification that follows must not average them, prefer one, or
/// silently take the last.
///
/// # Errors
///
/// Returns [`SearchError::LedgerHeader`] for a foreign header,
/// [`SearchError::LedgerRow`] for a malformed row, and
/// [`SearchError::DuplicateCell`] for a repeated cell.
pub fn parse_ledger(text: &str) -> Result<Vec<CellRecord>, SearchError> {
    let mut lines = text.lines().enumerate();
    let Some((_, header)) = lines.next() else {
        return Err(SearchError::LedgerHeader {
            found: String::new(),
        });
    };
    if header.trim_end() != LEDGER_HEADER {
        return Err(SearchError::LedgerHeader {
            found: header.to_string(),
        });
    }
    let mut records = Vec::new();
    let mut seen: Vec<usize> = Vec::new();
    for (position, line) in lines {
        if line.trim().is_empty() {
            continue;
        }
        let number = position + 1;
        // A repeated header is what a naive concatenation of two ledgers looks
        // like; name it rather than reporting a field-count error.
        if line.trim_end() == LEDGER_HEADER {
            return Err(SearchError::LedgerRow {
                line: number,
                message: "a second header line: this file is two ledgers concatenated".to_string(),
            });
        }
        let record = parse_row(number, line)?;
        if seen.contains(&record.index) {
            return Err(SearchError::DuplicateCell {
                index: record.index,
            });
        }
        seen.push(record.index);
        records.push(record);
    }
    Ok(records)
}

/// Parses one row.
fn parse_row(number: usize, line: &str) -> Result<CellRecord, SearchError> {
    let fields: Vec<&str> = line.trim_end().split('\t').collect();
    let row = |message: String| SearchError::LedgerRow {
        line: number,
        message,
    };
    if fields.len() != 9 {
        return Err(row(format!("{} fields, want 9", fields.len())));
    }
    let number_field = |index: usize| -> Result<usize, SearchError> {
        fields[index]
            .parse::<usize>()
            .map_err(|_| row(format!("field {index} {:?} is not a number", fields[index])))
    };
    let seconds_field = |index: usize| -> Result<Duration, SearchError> {
        fields[index]
            .parse::<f64>()
            .ok()
            .filter(|value| value.is_finite() && *value >= 0.0)
            .map(Duration::from_secs_f64)
            .ok_or_else(|| {
                row(format!(
                    "field {index} {:?} is not a duration",
                    fields[index]
                ))
            })
    };
    let choices = fields[2]
        .split(',')
        .map(|token| {
            token
                .parse::<usize>()
                .map_err(|_| row(format!("choice {token:?} is not a number")))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(CellRecord {
        run: RunId::new(fields[0])?,
        index: number_field(1)?,
        choices,
        verdict: CellVerdict::parse(fields[3])?,
        solve: seconds_field(4)?,
        steps: number_field(5)?,
        adds: number_field(6)?,
        check: CellCheck::parse(fields[7])?,
        check_time: seconds_field(8)?,
    })
}

/// Reads and parses a ledger file.
///
/// # Errors
///
/// Returns [`SearchError::Io`] if the file cannot be read, plus anything
/// [`parse_ledger`] rejects.
pub fn read_ledger(path: &Path) -> Result<Vec<CellRecord>, SearchError> {
    let text = std::fs::read_to_string(path).map_err(|error| SearchError::io(path, &error))?;
    parse_ledger(&text)
}

/// The distinct run ids in a ledger, in first-seen order.
pub fn ledger_runs(records: &[CellRecord]) -> Vec<RunId> {
    let mut runs: Vec<RunId> = Vec::new();
    for record in records {
        if !runs.contains(&record.run) {
            runs.push(record.run.clone());
        }
    }
    runs
}

/// Append-only ledger writer that refuses to reuse an existing file.
#[derive(Debug)]
pub struct LedgerWriter {
    file: File,
    path: PathBuf,
}

impl LedgerWriter {
    /// Creates a ledger, writing the header.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::LedgerExists`] if `path` already exists — that is
    /// finding B2's fix, not a convenience check — and [`SearchError::Io`] for
    /// any other failure.
    pub fn create(path: &Path) -> Result<Self, SearchError> {
        if path.exists() {
            return Err(SearchError::LedgerExists {
                path: path.display().to_string(),
            });
        }
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .map_err(|error| {
                if error.kind() == std::io::ErrorKind::AlreadyExists {
                    SearchError::LedgerExists {
                        path: path.display().to_string(),
                    }
                } else {
                    SearchError::io(path, &error)
                }
            })?;
        writeln!(file, "{LEDGER_HEADER}").map_err(|error| SearchError::io(path, &error))?;
        file.flush()
            .map_err(|error| SearchError::io(path, &error))?;
        Ok(Self {
            file,
            path: path.to_path_buf(),
        })
    }

    /// Creates the ledger for a run at `<stem>.run-<id>.tsv`.
    ///
    /// # Errors
    ///
    /// As [`LedgerWriter::create`].
    pub fn create_for_run(stem: &Path, run: &RunId) -> Result<Self, SearchError> {
        Self::create(&run_ledger_path(stem, run))
    }

    /// The path being written.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Appends a row and flushes it, so a monitor can poll the file safely.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::Io`] if the write or flush fails.
    pub fn append(&mut self, record: &CellRecord) -> Result<(), SearchError> {
        self.file
            .write_all(render_row(record).as_bytes())
            .map_err(|error| SearchError::io(&self.path, &error))?;
        self.file
            .flush()
            .map_err(|error| SearchError::io(&self.path, &error))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(index: usize, run: &str) -> CellRecord {
        CellRecord {
            run: RunId::new(run).expect("run id"),
            index,
            choices: vec![index + 1],
            verdict: CellVerdict::Unsat,
            solve: Duration::from_millis(1500),
            steps: 42,
            adds: 21,
            check: CellCheck::Passed,
            check_time: Duration::from_millis(250),
        }
    }

    #[test]
    fn rows_round_trip_through_text() {
        let records = vec![record(0, "a"), record(1, "a")];
        let parsed = parse_ledger(&render_ledger(&records)).expect("parse");
        assert_eq!(parsed, records);
    }

    #[test]
    fn a_failed_check_round_trips_with_its_reason() {
        let mut row = record(0, "a");
        row.check = CellCheck::Failed("no empty clause derived".to_string());
        let parsed = parse_ledger(&render_ledger(&[row.clone()])).expect("parse");
        assert_eq!(parsed, vec![row]);
    }

    #[test]
    fn run_ids_reject_separator_characters() {
        assert!(RunId::new("a\tb").is_err());
        assert!(RunId::new("").is_err());
        assert!(RunId::new("2026-08-12.a_1").is_ok());
    }

    #[test]
    fn run_ledger_path_stamps_the_run() {
        let run = RunId::new("second").expect("run id");
        assert_eq!(
            run_ledger_path(Path::new("/tmp/cover"), &run),
            PathBuf::from("/tmp/cover.run-second.tsv")
        );
    }

    #[test]
    fn foreign_headers_are_rejected() {
        let error = parse_ledger("index\tcolours\n").expect_err("foreign header");
        assert!(matches!(error, SearchError::LedgerHeader { .. }));
    }

    #[test]
    fn malformed_rows_name_their_line() {
        let text = format!("{LEDGER_HEADER}\na\t0\t1\tunsat\t0.0\t1\t1\tpassed\n");
        let error = parse_ledger(&text).expect_err("8 fields");
        assert_eq!(
            error,
            SearchError::LedgerRow {
                line: 2,
                message: "8 fields, want 9".to_string()
            }
        );
    }

    #[test]
    fn ledger_runs_lists_distinct_runs_in_order() {
        let records = vec![record(0, "a"), record(1, "b"), record(2, "a")];
        let runs = ledger_runs(&records);
        assert_eq!(
            runs,
            vec![RunId::new("a").expect("a"), RunId::new("b").expect("b")]
        );
    }
}
