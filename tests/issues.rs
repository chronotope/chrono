// issues.rs
//
// Regressions tests of specific issues.

#[cfg(test)]
use chrono::NaiveDateTime;

#[test]
#[should_panic]
/// When Issue #1096 is fixed then `#[should_panic]` should be removed.
/// See https://github.com/chronotope/chrono/issues/1096
fn issue_1096() {
    let test = NaiveDateTime::from_timestamp_millis(0).unwrap();
    let tf = test.format("%+");
    let output = tf.to_string();
    assert_eq!(output, "1970-01-01T00:00:00.00000+00:00");
}
