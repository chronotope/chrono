use super::NaiveDateTime;
use crate::naive::NaiveDate;
use crate::time_delta::TimeDelta;
use crate::{ChronoError, Datelike, FixedOffset, Utc};
use std::i64;

#[test]
fn test_datetime_from_timestamp() {
    let from_timestamp = |secs| NaiveDateTime::from_timestamp(secs, 0);
    let ymdhms =
        |y, m, d, h, n, s| Ok::<_, ChronoError>(NaiveDate::from_ymd(y, m, d)?.and_hms(h, n, s)?);
    assert_eq!(from_timestamp(-1), Ok(ymdhms(1969, 12, 31, 23, 59, 59).unwrap()));
    assert_eq!(from_timestamp(0), Ok(ymdhms(1970, 1, 1, 0, 0, 0).unwrap()));
    assert_eq!(from_timestamp(1), Ok(ymdhms(1970, 1, 1, 0, 0, 1).unwrap()));
    assert_eq!(from_timestamp(1_000_000_000), Ok(ymdhms(2001, 9, 9, 1, 46, 40).unwrap()));
    assert_eq!(from_timestamp(0x7fffffff), Ok(ymdhms(2038, 1, 19, 3, 14, 7).unwrap()));
    assert!(from_timestamp(i64::MIN).is_err());
    assert!(from_timestamp(i64::MAX).is_err());
}

#[test]
fn test_datetime_add() {
    macro_rules! check {
        ($input:expr, $rhs:expr, $result:expr $(,)?) => {{
            let (y, m, d, h, n, s) = $input;
            let lhs = NaiveDate::from_ymd(y, m, d).unwrap().and_hms(h, n, s).unwrap();
            let sum = $result.map(|(y, m, d, h, n, s)| {
                NaiveDate::from_ymd(y, m, d).unwrap().and_hms(h, n, s).unwrap()
            });
            assert_eq!(lhs.checked_add_signed($rhs), sum);
            assert_eq!(lhs.checked_sub_signed(-$rhs), sum);
        }};
    }

    check!((2014, 5, 6, 7, 8, 9), TimeDelta::seconds(3600 + 60 + 1), Some((2014, 5, 6, 8, 9, 10)));
    check!(
        (2014, 5, 6, 7, 8, 9),
        TimeDelta::seconds(-(3600 + 60 + 1)),
        Some((2014, 5, 6, 6, 7, 8))
    );
    check!((2014, 5, 6, 7, 8, 9), TimeDelta::seconds(86399), Some((2014, 5, 7, 7, 8, 8)));
    check!((2014, 5, 6, 7, 8, 9), TimeDelta::seconds(86_400 * 10), Some((2014, 5, 16, 7, 8, 9)));
    check!((2014, 5, 6, 7, 8, 9), TimeDelta::seconds(-86_400 * 10), Some((2014, 4, 26, 7, 8, 9)));
    check!((2014, 5, 6, 7, 8, 9), TimeDelta::seconds(86_400 * 10), Some((2014, 5, 16, 7, 8, 9)));

    // overflow check
    // assumes that we have correct values for MAX/MIN_DAYS_FROM_YEAR_0 from `naive::date`.
    // (they are private constants, but the equivalence is tested in that module.)
    let max_days_from_year_0 =
        NaiveDate::MAX.signed_duration_since(NaiveDate::from_ymd(0, 1, 1).unwrap());
    check!(
        (0, 1, 1, 0, 0, 0),
        max_days_from_year_0,
        Some((NaiveDate::MAX.year(), 12, 31, 0, 0, 0))
    );
    check!(
        (0, 1, 1, 0, 0, 0),
        max_days_from_year_0 + TimeDelta::seconds(86399),
        Some((NaiveDate::MAX.year(), 12, 31, 23, 59, 59)),
    );
    check!((0, 1, 1, 0, 0, 0), max_days_from_year_0 + TimeDelta::seconds(86_400), None,);
    check!((0, 1, 1, 0, 0, 0), TimeDelta::max_value(), None,);

    let min_days_from_year_0 =
        NaiveDate::MIN.signed_duration_since(NaiveDate::from_ymd(0, 1, 1).unwrap());
    check!((0, 1, 1, 0, 0, 0), min_days_from_year_0, Some((NaiveDate::MIN.year(), 1, 1, 0, 0, 0)));
    check!((0, 1, 1, 0, 0, 0), min_days_from_year_0 - TimeDelta::seconds(1), None,);
    check!((0, 1, 1, 0, 0, 0), TimeDelta::min_value(), None,);
}

#[test]
fn test_datetime_sub() {
    let ymdhms =
        |y, m, d, h, n, s| Ok::<_, ChronoError>(NaiveDate::from_ymd(y, m, d)?.and_hms(h, n, s)?);
    let since = NaiveDateTime::signed_duration_since;
    assert_eq!(
        since(ymdhms(2014, 5, 6, 7, 8, 9).unwrap(), ymdhms(2014, 5, 6, 7, 8, 9).unwrap()),
        TimeDelta::zero()
    );
    assert_eq!(
        since(ymdhms(2014, 5, 6, 7, 8, 10).unwrap(), ymdhms(2014, 5, 6, 7, 8, 9).unwrap()),
        TimeDelta::seconds(1)
    );
    assert_eq!(
        since(ymdhms(2014, 5, 6, 7, 8, 9).unwrap(), ymdhms(2014, 5, 6, 7, 8, 10).unwrap()),
        TimeDelta::seconds(-1)
    );
    assert_eq!(
        since(ymdhms(2014, 5, 7, 7, 8, 9).unwrap(), ymdhms(2014, 5, 6, 7, 8, 10).unwrap()),
        TimeDelta::seconds(86399)
    );
    assert_eq!(
        since(ymdhms(2001, 9, 9, 1, 46, 39).unwrap(), ymdhms(1970, 1, 1, 0, 0, 0).unwrap()),
        TimeDelta::seconds(999_999_999)
    );
}

#[test]
fn test_datetime_addassignment() {
    let ymdhms =
        |y, m, d, h, n, s| Ok::<_, ChronoError>(NaiveDate::from_ymd(y, m, d)?.and_hms(h, n, s)?);
    let mut date = ymdhms(2016, 10, 1, 10, 10, 10).unwrap();
    date += TimeDelta::minutes(10_000_000);
    assert_eq!(date, ymdhms(2035, 10, 6, 20, 50, 10).unwrap());
    date += TimeDelta::days(10);
    assert_eq!(date, ymdhms(2035, 10, 16, 20, 50, 10).unwrap());
}

#[test]
fn test_datetime_subassignment() {
    let ymdhms =
        |y, m, d, h, n, s| Ok::<_, ChronoError>(NaiveDate::from_ymd(y, m, d)?.and_hms(h, n, s)?);
    let mut date = ymdhms(2016, 10, 1, 10, 10, 10).unwrap();
    date -= TimeDelta::minutes(10_000_000);
    assert_eq!(date, ymdhms(1997, 9, 26, 23, 30, 10).unwrap());
    date -= TimeDelta::days(10);
    assert_eq!(date, ymdhms(1997, 9, 16, 23, 30, 10).unwrap());
}

#[test]
fn test_datetime_timestamp() {
    let to_timestamp = |y, m, d, h, n, s| {
        Ok::<_, ChronoError>(NaiveDate::from_ymd(y, m, d)?.and_hms(h, n, s)?.timestamp())
    };
    assert_eq!(to_timestamp(1969, 12, 31, 23, 59, 59).unwrap(), -1);
    assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 0).unwrap(), 0);
    assert_eq!(to_timestamp(1970, 1, 1, 0, 0, 1).unwrap(), 1);
    assert_eq!(to_timestamp(2001, 9, 9, 1, 46, 40).unwrap(), 1_000_000_000);
    assert_eq!(to_timestamp(2038, 1, 19, 3, 14, 7).unwrap(), 0x7fffffff);
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
        |y, m, d, h, n, s| Ok::<_, ChronoError>(NaiveDate::from_ymd(y, m, d)?.and_hms(h, n, s)?);
    let ymdhmsn = |y, m, d, h, n, s, nano| {
        Ok::<_, ChronoError>(NaiveDate::from_ymd(y, m, d)?.and_hms_nano(h, n, s, nano)?)
    };
    assert_eq!(
        NaiveDateTime::parse_from_str("2014-5-7T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z"),
        Ok(ymdhms(2014, 5, 7, 12, 34, 56).unwrap())
    ); // ignore offset
    assert_eq!(
        NaiveDateTime::parse_from_str("2015-W06-1 000000", "%G-W%V-%u%H%M%S"),
        Ok(ymdhms(2015, 2, 2, 0, 0, 0).unwrap())
    );
    assert_eq!(
        NaiveDateTime::parse_from_str("Fri, 09 Aug 2013 23:54:35 GMT", "%a, %d %b %Y %H:%M:%S GMT"),
        Ok(ymdhms(2013, 8, 9, 23, 54, 35).unwrap())
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
        Ok(ymdhms(2015, 9, 5, 23, 56, 4).unwrap())
    );
    assert_eq!(
        NaiveDateTime::parse_from_str("1283929614.1234", "%s.%f"),
        Ok(ymdhmsn(2010, 9, 8, 7, 6, 54, 1234).unwrap())
    );
    assert_eq!(
        NaiveDateTime::parse_from_str("1441497364.649", "%s%.3f"),
        Ok(ymdhmsn(2015, 9, 5, 23, 56, 4, 649000000).unwrap())
    );
    assert_eq!(
        NaiveDateTime::parse_from_str("1497854303.087654", "%s%.6f"),
        Ok(ymdhmsn(2017, 6, 19, 6, 38, 23, 87654000).unwrap())
    );
    assert_eq!(
        NaiveDateTime::parse_from_str("1437742189.918273645", "%s%.9f"),
        Ok(ymdhmsn(2015, 7, 24, 12, 49, 49, 918273645).unwrap())
    );
}

#[test]
fn test_datetime_format() {
    let dt = NaiveDate::from_ymd(2010, 9, 8).unwrap().and_hms_milli(7, 6, 54, 321).unwrap();
    assert_eq!(dt.format("%c").to_string(), "Wed Sep  8 07:06:54 2010");
    assert_eq!(dt.format("%s").to_string(), "1283929614");
    assert_eq!(dt.format("%t%n%%%n%t").to_string(), "\t\n%\n\t");

    // a horror of leap second: coming near to you.
    let dt = NaiveDate::from_ymd(2012, 6, 30).unwrap().and_hms_milli(23, 59, 59, 1_000).unwrap();
    assert_eq!(dt.format("%c").to_string(), "Sat Jun 30 23:59:60 2012");
    assert_eq!(dt.format("%s").to_string(), "1341100799"); // not 1341100800, it's intentional.
}

#[test]
fn test_datetime_add_sub_invariant() {
    // issue #37
    let base = NaiveDate::from_ymd(2000, 1, 1).unwrap().and_hms(0, 0, 0).unwrap();
    let t = -946684799990000;
    let time = base + TimeDelta::microseconds(t);
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
        NaiveDateTime::from_timestamp(nanos / A_BILLION, (nanos % A_BILLION) as u32).unwrap()
    );

    let minimum = "1677-09-21T00:12:44.000000000";
    let parsed: NaiveDateTime = minimum.parse().unwrap();
    let nanos = parsed.timestamp_nanos();
    assert_eq!(
        parsed,
        NaiveDateTime::from_timestamp(nanos / A_BILLION, (nanos % A_BILLION) as u32).unwrap()
    );
}

#[test]
fn test_and_timezone() {
    let ndt = NaiveDate::from_ymd(2022, 6, 15).unwrap().and_hms(18, 59, 36).unwrap();
    let dt_utc = ndt.and_local_timezone(Utc).unwrap();
    assert_eq!(dt_utc.naive_local(), ndt);
    assert_eq!(dt_utc.timezone(), Utc);

    let offset_tz = FixedOffset::west(4 * 3600).unwrap();
    let dt_offset = ndt.and_local_timezone(offset_tz).unwrap();
    assert_eq!(dt_offset.naive_local(), ndt);
    assert_eq!(dt_offset.timezone(), offset_tz);
}
