//! Evidence checks for the Chapter 15 three-machine XOR route.

use std::fs;

use axeyum_machine_evidence::{
    check_three_machine_xor, check_three_machine_xor_pointer_control, three_machine_xor_report,
    write_json,
};

#[test]
fn report_replays_all_cases_and_pointer_control_fires() {
    let report = three_machine_xor_report().unwrap();
    assert_eq!(report.cases.len(), 8);
    assert_eq!(
        (
            report.a0_static_instructions,
            report.rv64_static_instructions,
            report.x64_static_instructions,
        ),
        (11, 9, 8)
    );
    assert_eq!(report.cases[0].name, "empty");
    assert_eq!(report.cases[5].result, 0);
    let path = std::env::temp_dir().join(format!(
        "axeyum-three-machine-xor-{}.json",
        std::process::id()
    ));
    write_json(&path, &report).unwrap();
    assert_eq!(check_three_machine_xor(&path).unwrap(), report);
    assert!(check_three_machine_xor_pointer_control(&path).is_err());
    fs::remove_file(path).unwrap();
}
