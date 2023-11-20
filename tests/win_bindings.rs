#![cfg(all(windows, feature = "clock", feature = "std"))]

use similar_asserts::assert_eq;
use std::fs;
use windows_bindgen::bindgen;

#[test]
fn gen_bindings() {
    let input = "src/offset/local/win_bindings.txt";
    let output = "src/offset/local/win_bindings.rs";
    let existing = fs::read_to_string(output).unwrap().replace("\r\n", "\n");

    let log = bindgen(["--etc", input]).unwrap();
    eprintln!("{}", log);

    // Check the output is the same as before.
    // Depending on the git configuration the file may have been checked out with `\r\n` newlines or
    // with `\n`. Compare line-by-line to ignore this difference.
    let new = fs::read_to_string(output).unwrap().replace("\r\n", "\n");
    assert_eq!(new, existing);
}
