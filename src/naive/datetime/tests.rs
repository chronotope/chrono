use super::NaiveDateTime;
use crate::oldtime::Duration;
use crate::NaiveDate;
use crate::{Datelike, FixedOffset, Utc};
use std::i64;

#[test]
fn test_datetime_from_timestamp_millis() {
    let valid_map = [
        (1662921288000, "2022-09-11 18:34:48.000000000"),
        (1662921288123, "2022-09-11 18:34:48.123000000"),
        (1662921287890, "2022-09-11 18:34:47.890000000"),
        (-2208936075000, "1900-01-01 14:38:45.000000000"),
        (0, "1970-01-01 00:00:00.000000000"),
        (119731017000, "1973-10-17 18:36:57.000000000"),
        (1234567890000, "2009-02-13 23:31:30.000000000"),
        (2034061609000, "2034-06-16 09:06:49.000000000"),
    ];

    for (timestamp_millis, formatted) in valid_map.iter().copied() {
        let naive_datetime = NaiveDateTime::from_timestamp_millis(timestamp_millis);
        assert_eq!(timestamp_millis, naive_datetime.unwrap().timestamp_millis());
        assert_eq!(naive_datetime.unwrap().format("%F %T%.9f").to_string(), formatted);
    }

    let invalid = [i64::MAX, i64::MIN];

    for timestamp_millis in invalid.iter().copied() {
        let naive_datetime = NaiveDateTime::from_timestamp_millis(timestamp_millis);
        assert!(naive_datetime.is_none());
    }

    // Test that the result of `from_timestamp_millis` compares equal to
    // that of `from_timestamp_opt`.
    let secs_test = [0, 1, 2, 1000, 1234, 12345678, -1, -2, -1000, -12345678];
    for secs in secs_test.iter().cloned() {
        assert_eq!(
            NaiveDateTime::from_timestamp_millis(secs * 1000),
            NaiveDateTime::from_timestamp_opt(secs, 0)
        );
    }
}

#[test]
fn test_datetime_from_timestamp_micros() {
    let valid_map = [
        (1662921288000000, "2022-09-11 18:34:48.000000000"),
        (1662921288123456, "2022-09-11 18:34:48.123456000"),
        (1662921287890000, "2022-09-11 18:34:47.890000000"),
        (-2208936075000000, "1900-01-01 14:38:45.000000000"),
        (0, "1970-01-01 00:00:00.000000000"),
        (119731017000000, "1973-10-17 18:36:57.000000000"),
        (1234567890000000, "2009-02-13 23:31:30.000000000"),
        (2034061609000000, "2034-06-16 09:06:49.000000000"),
    ];

    for (timestamp_micros, formatted) in valid_map.iter().copied() {
        let naive_datetime = NaiveDateTime::from_timestamp_micros(timestamp_micros);
        assert_eq!(timestamp_micros, naive_datetime.unwrap().timestamp_micros());
        assert_eq!(naive_datetime.unwrap().format("%F %T%.9f").to_string(), formatted);
    }

    let invalid = [i64::MAX, i64::MIN];

    for timestamp_micros in invalid.iter().copied() {
        let naive_datetime = NaiveDateTime::from_timestamp_micros(timestamp_micros);
        assert!(naive_datetime.is_none());
    }

    // Test that the result of `from_timestamp_micros` compares equal to
    // that of `from_timestamp_opt`.
    let secs_test = [0, 1, 2, 1000, 1234, 12345678, -1, -2, -1000, -12345678];
    for secs in secs_test.iter().copied() {
        assert_eq!(
            NaiveDateTime::from_timestamp_micros(secs * 1_000_000),
            NaiveDateTime::from_timestamp_opt(secs, 0)
        );
    }
}

#[test]
fn test_datetime_from_timestamp() {
    let from_timestamp = |secs| NaiveDateTime::from_timestamp_opt(secs, 0);
    let ymdhms =
        |y, m, d, h, n, s| NaiveDate::from_ymd_opt(y, m, d).unwrap().and_hms_opt(h, n, s).unwrap();
    assert_eq!(from_timestamp(-1), Some(ymdhms(1969, 12, 31, 23, 59, 59)));
    assert_eq!(from_timestamp(0), Some(ymdhms(1970, 1, 1, 0, 0, 0)));
    assert_eq!(from_timestamp(1), Some(ymdhms(1970, 1, 1, 0, 0, 1)));
    assert_eq!(from_timestamp(1_000_000_000), Some(ymdhms(2001, 9, 9, 1, 46, 40)));
    assert_eq!(from_timestamp(0x7fffffff), Some(ymdhms(2038, 1, 19, 3, 14, 7)));
    assert_eq!(from_timestamp(i64::MIN), None);
    assert_eq!(from_timestamp(i64::MAX), None);
}

#[test]
fn test_datetime_add() {
    fn check(
        (y, m, d, h, n, s): (i32, u32, u32, u32, u32, u32),
        rhs: Duration,
        result: Option<(i32, u32, u32, u32, u32, u32)>,
    ) {
        let lhs = NaiveDate::from_ymd_opt(y, m, d).unwrap().and_hms_opt(h, n, s).unwrap();
        let sum = result.map(|(y, m, d, h, n, s)| {
            NaiveDate::from_ymd_opt(y, m, d).unwrap().and_hms_opt(h, n, s).unwrap()
        });
        assert_eq!(lhs.checked_add_signed(rhs), sum);
        assert_eq!(lhs.checked_sub_signed(-rhs), sum);
    }

    check((2014, 5, 6, 7, 8, 9), Duration::seconds(3600 + 60 + 1), Some((2014, 5, 6, 8, 9, 10)));
    check((2014, 5, 6, 7, 8, 9), Duration::seconds(-(3600 + 60 + 1)), Some((2014, 5, 6, 6, 7, 8)));
    check((2014, 5, 6, 7, 8, 9), Duration::seconds(86399), Some((2014, 5, 7, 7, 8, 8)));
    check((2014, 5, 6, 7, 8, 9), Duration::seconds(86_400 * 10), Some((2014, 5, 16, 7, 8, 9)));
    check((2014, 5, 6, 7, 8, 9), Duration::seconds(-86_400 * 10), Some((2014, 4, 26, 7, 8, 9)));
    check((2014, 5, 6, 7, 8, 9), Duration::seconds(86_400 * 10), Some((2014, 5, 16, 7, 8, 9)));

    // overflow check
    // assumes that we have correct values for MAX/MIN_DAYS_FROM_YEAR_0 from `naive::date`.
    // (they are private constants, but the equivalence is tested in that module.)
    let max_days_from_year_0 =
        NaiveDate::MAX.signed_duration_since(NaiveDate::from_ymd_opt(0, 1, 1).unwrap());
    check((0, 1, 1, 0, 0, 0), max_days_from_year_0, Some((NaiveDate::MAX.year(), 12, 31, 0, 0, 0)));
    check(
        (0, 1, 1, 0, 0, 0),
        max_days_from_year_0 + Duration::seconds(86399),
        Some((NaiveDate::MAX.year(), 12, 31, 23, 59, 59)),
    );
    check((0, 1, 1, 0, 0, 0), max_days_from_year_0 + Duration::seconds(86_400), None);
    check((0, 1, 1, 0, 0, 0), Duration::max_value(), None);

    let min_days_from_year_0 =
        NaiveDate::MIN.signed_duration_since(NaiveDate::from_ymd_opt(0, 1, 1).unwrap());
    check((0, 1, 1, 0, 0, 0), min_days_from_year_0, Some((NaiveDate::MIN.year(), 1, 1, 0, 0, 0)));
    check((0, 1, 1, 0, 0, 0), min_days_from_year_0 - Duration::seconds(1), None);
    check((0, 1, 1, 0, 0, 0), Duration::min_value(), None);
}

#[test]
fn test_datetime_sub() {
    let ymdhms =
        |y, m, d, h, n, s| NaiveDate::from_ymd_opt(y, m, d).unwrap().and_hms_opt(h, n, s).unwrap();
    let since = NaiveDateTime::signed_duration_since;
    assert_eq!(since(ymdhms(2014, 5, 6, 7, 8, 9), ymdhms(2014, 5, 6, 7, 8, 9)), Duration::zero());
    assert_eq!(
        since(ymdhms(2014, 5, 6, 7, 8, 10), ymdhms(2014, 5, 6, 7, 8, 9)),
        Duration::seconds(1)
    );
    assert_eq!(
        since(ymdhms(2014, 5, 6, 7, 8, 9), ymdhms(2014, 5, 6, 7, 8, 10)),
        Duration::seconds(-1)
    );
    assert_eq!(
        since(ymdhms(2014, 5, 7, 7, 8, 9), ymdhms(2014, 5, 6, 7, 8, 10)),
        Duration::seconds(86399)
    );
    assert_eq!(
        since(ymdhms(2001, 9, 9, 1, 46, 39), ymdhms(1970, 1, 1, 0, 0, 0)),
        Duration::seconds(999_999_999)
    );
}

#[test]
fn test_datetime_addassignment() {
    let ymdhms =
        |y, m, d, h, n, s| NaiveDate::from_ymd_opt(y, m, d).unwrap().and_hms_opt(h, n, s).unwrap();
    let mut date = ymdhms(2016, 10, 1, 10, 10, 10);
    date += Duration::minutes(10_000_000);
    assert_eq!(date, ymdhms(2035, 10, 6, 20, 50, 10));
    date += Duration::days(10);
    assert_eq!(date, ymdhms(2035, 10, 16, 20, 50, 10));
}

#[test]
fn test_datetime_subassignment() {
    let ymdhms =
        |y, m, d, h, n, s| NaiveDate::from_ymd_opt(y, m, d).unwrap().and_hms_opt(h, n, s).unwrap();
    let mut date = ymdhms(2016, 10, 1, 10, 10, 10);
    date -= Duration::minutes(10_000_000);
    assert_eq!(date, ymdhms(1997, 9, 26, 23, 30, 10));
    date -= Duration::days(10);
    assert_eq!(date, ymdhms(1997, 9, 16, 23, 30, 10));
}

#[test]
fn test_datetime_timestamp() {
    let to_timestamp = |y, m, d, h, n, s| {
        NaiveDate::from_ymd_opt(y, m, d).unwrap().and_hms_opt(h, n, s).unwrap().timestamp()
    };
    assert_eq!(to_timestamp(1969, 12, 31, 23, 59, 59), -1);
    assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 0), 0);
    assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 1), 1);
    assert_eq!(to_timestamp(2001, 9, 9, 1, 46, 40), 1_000_000_000);
    assert_eq!(to_timestamp(2038, 1, 19, 3, 14, 7), 0x7fffffff);
}

#[test]
fn test_datetime_from_str() {
    // valid cases
    let valid = [
        "2015-2-18T23:16:9.15",
        "-77-02-18T23:16:09",
        "  +82701  -  05  -  6  T  15  :  9  : 60.898989898989   ",
    ];
    for &s in &valid {
        let d = match s.parse::<NaiveDateTime>() {
            Ok(d) => d,
            Err(e) => panic!("parsing `{}` has failed: {}", s, e),
        };
        let s_ = format!("{:?}", d);
        // `s` and `s_` may differ, but `s.parse()` and `s_.parse()` must be same
        let d_ = match s_.parse::<NaiveDateTime>() {
            Ok(d) => d,
            Err(e) => {
                panic!("`{}` is parsed into `{:?}`, but reparsing that has failed: {}", s, d, e)
            }
        };
        assert!(
            d == d_,
            "`{}` is parsed into `{:?}`, but reparsed result \
             `{:?}` does not match",
            s,
            d,
            d_
        );
    }

    // some invalid cases
    // since `ParseErrorKind` is private, all we can do is to check if there was an error
    assert!("".parse::<NaiveDateTime>().is_err());
    assert!("x".parse::<NaiveDateTime>().is_err());
    assert!("15".parse::<NaiveDateTime>().is_err());
    assert!("15:8:9".parse::<NaiveDateTime>().is_err());
    assert!("15-8-9".parse::<NaiveDateTime>().is_err());
    assert!("2015-15-15T15:15:15".parse::<NaiveDateTime>().is_err());
    assert!("2012-12-12T12:12:12x".parse::<NaiveDateTime>().is_err());
    assert!("2012-123-12T12:12:12".parse::<NaiveDateTime>().is_err());
    assert!("+ 82701-123-12T12:12:12".parse::<NaiveDateTime>().is_err());
    assert!("+802701-123-12T12:12:12".parse::<NaiveDateTime>().is_err()); // out-of-bound
}

#[test]
fn test_datetime_parse_from_str() {
    let ymdhms =
        |y, m, d, h, n, s| NaiveDate::from_ymd_opt(y, m, d).unwrap().and_hms_opt(h, n, s).unwrap();
    let ymdhmsn = |y, m, d, h, n, s, nano| {
        NaiveDate::from_ymd_opt(y, m, d).unwrap().and_hms_nano_opt(h, n, s, nano).unwrap()
    };
    assert_eq!(
        NaiveDateTime::parse_from_str("2014-5-7T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z"),
        Ok(ymdhms(2014, 5, 7, 12, 34, 56))
    ); // ignore offset
    assert_eq!(
        NaiveDateTime::parse_from_str("2015-W06-1 000000", "%G-W%V-%u%H%M%S"),
        Ok(ymdhms(2015, 2, 2, 0, 0, 0))
    );
    assert_eq!(
        NaiveDateTime::parse_from_str("Fri, 09 Aug 2013 23:54:35 GMT", "%a, %d %b %Y %H:%M:%S GMT"),
        Ok(ymdhms(2013, 8, 9, 23, 54, 35))
    );
    assert!(NaiveDateTime::parse_from_str(
        "Sat, 09 Aug 2013 23:54:35 GMT",
        "%a, %d %b %Y %H:%M:%S GMT"
    )
    .is_err());
    assert!(NaiveDateTime::parse_from_str("2014-5-7 12:3456", "%Y-%m-%d %H:%M:%S").is_err());
    assert!(NaiveDateTime::parse_from_str("12:34:56", "%H:%M:%S").is_err()); // insufficient
    assert_eq!(
        NaiveDateTime::parse_from_str("1441497364", "%s"),
        Ok(ymdhms(2015, 9, 5, 23, 56, 4))
    );
    assert_eq!(
        NaiveDateTime::parse_from_str("1283929614.1234", "%s.%f"),
        Ok(ymdhmsn(2010, 9, 8, 7, 6, 54, 1234))
    );
    assert_eq!(
        NaiveDateTime::parse_from_str("1441497364.649", "%s%.3f"),
        Ok(ymdhmsn(2015, 9, 5, 23, 56, 4, 649000000))
    );
    assert_eq!(
        NaiveDateTime::parse_from_str("1497854303.087654", "%s%.6f"),
        Ok(ymdhmsn(2017, 6, 19, 6, 38, 23, 87654000))
    );
    assert_eq!(
        NaiveDateTime::parse_from_str("1437742189.918273645", "%s%.9f"),
        Ok(ymdhmsn(2015, 7, 24, 12, 49, 49, 918273645))
    );
}

#[test]
fn test_datetime_format() {
    let dt = NaiveDate::from_ymd_opt(2010, 9, 8).unwrap().and_hms_milli_opt(7, 6, 54, 321).unwrap();
    assert_eq!(dt.format("%c").to_string(), "Wed Sep  8 07:06:54 2010");
    assert_eq!(dt.format("%s").to_string(), "1283929614");
    assert_eq!(dt.format("%t%n%%%n%t").to_string(), "\t\n%\n\t");

    // a horror of leap second: coming near to you.
    let dt =
        NaiveDate::from_ymd_opt(2012, 6, 30).unwrap().and_hms_milli_opt(23, 59, 59, 1_000).unwrap();
    assert_eq!(dt.format("%c").to_string(), "Sat Jun 30 23:59:60 2012");
    assert_eq!(dt.format("%s").to_string(), "1341100799"); // not 1341100800, it's intentional.
}

#[test]
fn test_datetime_add_sub_invariant() {
    // issue #37
    let base = NaiveDate::from_ymd_opt(2000, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();
    let t = -946684799990000;
    let time = base + Duration::microseconds(t);
    assert_eq!(t, time.signed_duration_since(base).num_microseconds().unwrap());
}

#[test]
fn test_nanosecond_range() {
    const A_BILLION: i64 = 1_000_000_000;
    let maximum = "2262-04-11T23:47:16.854775804";
    let parsed: NaiveDateTime = maximum.parse().unwrap();
    let nanos = parsed.timestamp_nanos();
    assert_eq!(
        parsed,
        NaiveDateTime::from_timestamp_opt(nanos / A_BILLION, (nanos % A_BILLION) as u32).unwrap()
    );

    let minimum = "1677-09-21T00:12:44.000000000";
    let parsed: NaiveDateTime = minimum.parse().unwrap();
    let nanos = parsed.timestamp_nanos();
    assert_eq!(
        parsed,
        NaiveDateTime::from_timestamp_opt(nanos / A_BILLION, (nanos % A_BILLION) as u32).unwrap()
    );
}

#[test]
fn test_and_local_timezone() {
    let ndt = NaiveDate::from_ymd_opt(2022, 6, 15).unwrap().and_hms_opt(18, 59, 36).unwrap();
    let dt_utc = ndt.and_local_timezone(Utc).unwrap();
    assert_eq!(dt_utc.naive_local(), ndt);
    assert_eq!(dt_utc.timezone(), Utc);

    let offset_tz = FixedOffset::west_opt(4 * 3600).unwrap();
    let dt_offset = ndt.and_local_timezone(offset_tz).unwrap();
    assert_eq!(dt_offset.naive_local(), ndt);
    assert_eq!(dt_offset.timezone(), offset_tz);
}

#[test]
fn test_and_utc() {
    let ndt = NaiveDate::from_ymd_opt(2023, 1, 30).unwrap().and_hms_opt(19, 32, 33).unwrap();
    let dt_utc = ndt.and_utc();
    assert_eq!(dt_utc.naive_local(), ndt);
    assert_eq!(dt_utc.timezone(), Utc);
}
