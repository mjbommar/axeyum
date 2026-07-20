//! End-to-end process-isolation regression for `QF_BV` certificate work.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;

fn temp_dir() -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "axeyum-certificate-process-{}-{unique}",
        std::process::id()
    ));
    fs::create_dir_all(&path).unwrap();
    path
}

fn run_benchmark(corpus: &Path, out: &Path, process_timeout_ms: u64) -> Value {
    let output = Command::new(env!("CARGO_BIN_EXE_axeyum-bench"))
        .arg(corpus)
        .args([
            "--backend",
            "sat-bv",
            "--rewrite",
            "off",
            "--prove-unsat",
            "--certify-end-to-end-unsat",
            "--end-to-end-deadline-ms",
            "1000",
            "--end-to-end-process-timeout-ms",
            &process_timeout_ms.to_string(),
            "--jobs",
            "1",
            "--out",
        ])
        .arg(out)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "benchmark failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&fs::read(out).unwrap()).unwrap()
}

#[test]
fn complete_worker_self_rechecks_and_hard_timeout_stays_in_denominator() {
    let root = temp_dir();
    fs::write(
        root.join("contradiction.smt2"),
        "(set-logic QF_BV)\n\
         (set-info :status unsat)\n\
         (declare-fun x () (_ BitVec 4))\n\
         (assert (= x #x0))\n\
         (assert (= x #x1))\n\
         (check-sat)\n",
    )
    .unwrap();

    let completed = run_benchmark(&root, &root.join("completed.json"), 5000);
    assert_eq!(completed["version"], 37);
    assert_eq!(completed["summary"]["end_to_end_unsat"]["attempted"], 1);
    assert_eq!(completed["summary"]["end_to_end_unsat"]["certified"], 1);
    assert_eq!(completed["summary"]["end_to_end_unsat"]["hard_timeouts"], 0);
    assert_eq!(
        completed["instances"][0]["end_to_end_unsat"]["isolation"],
        "subprocess-hard-timeout"
    );
    assert_eq!(
        completed["instances"][0]["end_to_end_unsat"]["hard_timeout"],
        false
    );

    let timed_out = run_benchmark(&root, &root.join("timed-out.json"), 1);
    assert_eq!(timed_out["summary"]["end_to_end_unsat"]["attempted"], 1);
    assert_eq!(timed_out["summary"]["end_to_end_unsat"]["not_certified"], 1);
    assert_eq!(timed_out["summary"]["end_to_end_unsat"]["hard_timeouts"], 1);
    assert_eq!(
        timed_out["instances"][0]["end_to_end_unsat"]["hard_timeout"],
        true
    );
    assert!(
        timed_out["instances"][0]["end_to_end_unsat"]["detail"]
            .as_str()
            .unwrap()
            .contains("killed and reaped")
    );

    fs::remove_dir_all(root).unwrap();
}
