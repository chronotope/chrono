use chrono::offset::TimeZone;
use chrono::Local;
use chrono::{Datelike, Error, NaiveDate, NaiveDateTime, Timelike};

use std::{path, process};

#[cfg(unix)]
fn verify_against_date_command_local(path: &'static str, dt: NaiveDateTime) -> Result<(), Error> {
    let output = process::Command::new(path)
        .arg("-d")
        .arg(format!("{}-{:02}-{:02} {:02}:05:01", dt.year(), dt.month(), dt.day(), dt.hour()))
        .arg("+%Y-%m-%d %H:%M:%S %:z")
        .output()
        .unwrap();

    let date_command_str = String::from_utf8(output.stdout)?;
    
    match Local.from_local_datetime(
        &NaiveDate::from_ymd(dt.year(), dt.month(), dt.day())?.and_hms(dt.hour(), 5, 1)?
    ) {
        // compare a legit date to the "date" output
        Ok(chrono::LocalResult::Single(dt)) => assert_eq!(format!("{}\n", dt), date_command_str),
        // "date" command always returns a given time when it is ambiguous (dt.earliest())
        Ok(chrono::LocalResult::Ambiguous(dt1, _dt2)) => assert_eq!(format!("{}\n", dt1), date_command_str),
        // "date" command returns an empty string for an invalid time (e.g. spring forward gap due to DST)
        Err(_) => assert_eq!(date_command_str, ""),
    }
    Ok(())
}

#[test]
#[cfg(unix)]
fn try_verify_against_date_command() -> Result<(), Error> {
    let date_path = "/usr/bin/date";

    if !path::Path::new(date_path).exists() {
        // date command not found, skipping
        // avoid running this on macOS, which has path /bin/date
        // as the required CLI arguments are not present in the
        // macOS build.
        return Ok(());
    }

    let mut date = NaiveDate::from_ymd(1975, 1, 1).unwrap().and_hms(0, 0, 0).unwrap();

    while date.year() < 2078 {
        if (1975..=1977).contains(&date.year())
            || (2020..=2022).contains(&date.year())
            || (2073..=2077).contains(&date.year())
        {
            verify_against_date_command_local(date_path, date)?;
        }

        date += chrono::TimeDelta::hours(1);
    }
    Ok(())
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
    let date = NaiveDate::from_ymd(dt.year(), dt.month(), dt.day()).unwrap();
    let ldt = Local
        .from_local_datetime(&date.and_hms(dt.hour(), dt.minute(), dt.second()).unwrap())
        .unwrap()
        .single()
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
    let mut date = NaiveDate::from_ymd(1970, 1, 1).unwrap().and_hms(12, 11, 13).unwrap();
    while date.year() < 2008 {
        verify_against_date_command_format_local(date_path, date);
        date += chrono::TimeDelta::days(55);
    }
}
