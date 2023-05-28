#[cfg(unix)]
use chrono::offset::TimeZone;
#[cfg(unix)]
use chrono::Local;
#[cfg(unix)]
use chrono::{Datelike, NaiveDate, NaiveDateTime, Timelike};

#[cfg(unix)]
use std::{path, process};

#[cfg(unix)]
fn verify_against_date_command_local(path: &'static str, dt: NaiveDateTime) {
    let output = process::Command::new(path)
        .arg("-d")
        .arg(format!("{}-{:02}-{:02} {:02}:05:01", dt.year(), dt.month(), dt.day(), dt.hour()))
        .arg("+%Y-%m-%d %H:%M:%S %:z")
        .output()
        .unwrap();

    let date_command_str = String::from_utf8(output.stdout).unwrap();

    // The below would be preferred. At this stage neither earliest() or latest()
    // seems to be consistent with the output of the `date` command, so we simply
    // compare both.
    // let local = Local
    //     .with_ymd_and_hms(year, month, day, hour, 5, 1)
    //     // looks like the "date" command always returns a given time when it is ambiguous
    //     .earliest();

    // if let Some(local) = local {
    //     assert_eq!(format!("{}\n", local), date_command_str);
    // } else {
    //     // we are in a "Spring forward gap" due to DST, and so date also returns ""
    //     assert_eq!("", date_command_str);
    // }

    // This is used while a decision is made wheter the `date` output needs to
    // be exactly matched, or whether LocalResult::Ambigious should be handled
    // differently

    let date = NaiveDate::from_ymd_opt(dt.year(), dt.month(), dt.day()).unwrap();
    match Local.from_local_datetime(&date.and_hms_opt(dt.hour(), 5, 1).unwrap()) {
        chrono::LocalResult::Ambiguous(a, b) => assert!(
            format!("{}\n", a) == date_command_str || format!("{}\n", b) == date_command_str
        ),
        chrono::LocalResult::Single(a) => {
            assert_eq!(format!("{}\n", a), date_command_str);
        }
        chrono::LocalResult::None => {
            assert_eq!("", date_command_str);
        }
    }
}

#[test]
#[cfg(unix)]
fn try_verify_against_date_command() {
    #[cfg(not(target_os = "aix"))]
    let date_path = "/usr/bin/date";
    #[cfg(target_os = "aix")]
    let date_path = "/opt/freeware/bin/date";

    if !path::Path::new(date_path).exists() {
        // date command not found, skipping
        // avoid running this on macOS, which has path /bin/date
        // as the required CLI arguments are not present in the
        // macOS build.
        return;
    }

    let mut date = NaiveDate::from_ymd_opt(1975, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();

    while date.year() < 2078 {
        if (1975..=1977).contains(&date.year())
            || (2020..=2022).contains(&date.year())
            || (2073..=2077).contains(&date.year())
        {
            verify_against_date_command_local(date_path, date);
        }

        date += chrono::Duration::hours(1);
    }
}

#[cfg(target_os = "linux")]
fn verify_against_date_command_format_local(path: &'static str, dt: NaiveDateTime) {
    let required_format =
        "d%d D%D F%F H%H I%I j%j k%k l%l m%m M%M S%S T%T u%u U%U w%w W%W X%X y%y Y%Y z%:z";
    // a%a - depends from localization
    // A%A - depends from localization
    // b%b - depends from localization
    // B%B - depends from localization
    // h%h - depends from localization
    // c%c - depends from localization
    // p%p - depends from localization
    // r%r - depends from localization
    // x%x - fails, date is dd/mm/yyyy, chrono is dd/mm/yy, same as %D
    // Z%Z - too many ways to represent it, will most likely fail

    let output = process::Command::new(path)
        .arg("-d")
        .arg(format!(
            "{}-{:02}-{:02} {:02}:{:02}:{:02}",
            dt.year(),
            dt.month(),
            dt.day(),
            dt.hour(),
            dt.minute(),
            dt.second()
        ))
        .arg(format!("+{}", required_format))
        .output()
        .unwrap();

    let date_command_str = String::from_utf8(output.stdout).unwrap();
    let date = NaiveDate::from_ymd_opt(dt.year(), dt.month(), dt.day()).unwrap();
    let ldt = Local
        .from_local_datetime(&date.and_hms_opt(dt.hour(), dt.minute(), dt.second()).unwrap())
        .unwrap();
    let formated_date = format!("{}\n", ldt.format(required_format));
    assert_eq!(date_command_str, formated_date);
}

#[test]
#[cfg(target_os = "linux")]
fn try_verify_against_date_command_format() {
    let date_path = "/usr/bin/date";

    if !path::Path::new(date_path).exists() {
        // date command not found, skipping
        return;
    }
    let mut date = NaiveDate::from_ymd_opt(1970, 1, 1).unwrap().and_hms_opt(12, 11, 13).unwrap();
    while date.year() < 2008 {
        verify_against_date_command_format_local(date_path, date);
        date += chrono::Duration::days(55);
    }
}

// The following panic tests should remove `#[should_panic]` after
// Issue #1010 is fixed.

#[test]
#[should_panic]
/// Derived from https://github.com/Koral77/replay_files/blob/ce5b5c88c2a45a089d7d5ce19c60a5e50283ba60/replays/chrono/replay_chrono1/src/main.rs
fn issue_1010_panic1() {
    let _local0 = chrono::naive::NaiveDateTime::from_timestamp_opt(-4227854320, 1678774288);
    let _local1 = chrono::Duration::microseconds(-7019067213869040);
    let _local2_param0_helper1 = _local0.unwrap();
    // panics
    _ = chrono::DurationRound::duration_trunc(_local2_param0_helper1, _local1);
}

#[test]
#[should_panic]
/// Derived from https://github.com/Koral77/replay_files/blob/ce5b5c88c2a45a089d7d5ce19c60a5e50283ba60/replays/chrono/replay_chrono2/src/main.rs
fn issue_1010_panic2() {
    let _local0 = chrono::naive::NaiveDateTime::from_timestamp_opt(320041586, 1920103021);
    let _local1 = chrono::Duration::nanoseconds(-8923838508697114584);
    let _local2_param0_helper1 = _local0.unwrap();
    // panics
    _ = chrono::DurationRound::duration_round(_local2_param0_helper1, _local1);
}

#[test]
#[should_panic]
/// Derived from https://github.com/Koral77/replay_files/blob/ce5b5c88c2a45a089d7d5ce19c60a5e50283ba60/replays/chrono/replay_chrono3/src/main.rs
fn issue_1010_panic3() {
    let _local0 = chrono::naive::NaiveDateTime::from_timestamp_opt(-2621440, 0);
    let _local1 = chrono::Duration::nanoseconds(-9223372036854771421);
    let _local2_param0_helper1 = _local0.unwrap();
    // panics
    _ = chrono::DurationRound::duration_round(_local2_param0_helper1, _local1);
}

#[test]
/// Derived from https://github.com/Koral77/replay_files/blob/ce5b5c88c2a45a089d7d5ce19c60a5e50283ba60/replays/chrono/replay_chrono4/src/main.rs
fn issue_1010_nopanic4() {
    let _local1 = chrono::offset::FixedOffset::east_opt(17367308);
    assert!(_local1.is_none());
}

#[test]
/// Derived from https://github.com/Koral77/replay_files/blob/ce5b5c88c2a45a089d7d5ce19c60a5e50283ba60/replays/chrono/replay_chrono5/src/main.rs
fn issue_1010_nopanic5() {
    let _local0 = chrono::naive::NaiveDateTime::from_timestamp_opt(-502509993984, 64);
    let _local1_param0_helper1 = _local0.unwrap();
    assert!(chrono::Datelike::with_ordinal0(&(_local1_param0_helper1), 4294967295).is_none());
}

#[test]
/// Derived from https://github.com/Koral77/replay_files/blob/ce5b5c88c2a45a089d7d5ce19c60a5e50283ba60/replays/chrono/replay_chrono6/src/main.rs
fn issue_1010_nopanic6() {
    let _local0 = chrono::naive::NaiveDateTime::from_timestamp_opt(-754576364, 336909572);
    let _local1_param0_helper1 = _local0.unwrap();
    assert!(chrono::Datelike::with_day0(&(_local1_param0_helper1), 4294967295).is_none());
}

#[test]
/// Derived from https://github.com/Koral77/replay_files/blob/ce5b5c88c2a45a089d7d5ce19c60a5e50283ba60/replays/chrono/replay_chrono7/src/main.rs
fn issue_1010_nopanic7() {
    #[allow(deprecated)]
    let _local0 = chrono::naive::NaiveDateTime::from_timestamp(-8377300, 742391807);
    assert!(chrono::Datelike::with_month0(&(_local0), 4294967295).is_none());
}

#[test]
#[should_panic]
/// Derived from https://github.com/Koral77/replay_files/blob/ce5b5c88c2a45a089d7d5ce19c60a5e50283ba60/replays/chrono/replay_chrono8/src/main.rs
fn issue_1010_panic8() {
    #[allow(deprecated)]
    let _local0 = chrono::naive::NaiveDateTime::from_timestamp(-11676614656, 15282199);
    // panics
    _ = chrono::naive::NaiveDateTime::timestamp_nanos(&(&_local0));
}
