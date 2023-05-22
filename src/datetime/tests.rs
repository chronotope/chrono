use std::time::{SystemTime, UNIX_EPOCH};

use super::DateTime;
use crate::naive::{NaiveDate, NaiveTime};
use crate::offset::{FixedOffset, TimeZone, Utc};
#[cfg(feature = "clock")]
use crate::offset::{Local, Offset};
use crate::oldtime::Duration;
use crate::{Datelike, Days, LocalResult, Months, NaiveDateTime};

#[derive(Clone)]
struct DstTester;

impl DstTester {
    fn winter_offset() -> FixedOffset {
        FixedOffset::east_opt(8 * 60 * 60).unwrap()
    }
    fn summer_offset() -> FixedOffset {
        FixedOffset::east_opt(9 * 60 * 60).unwrap()
    }

    const TO_WINTER_MONTH_DAY: (u32, u32) = (4, 15);
    const TO_SUMMER_MONTH_DAY: (u32, u32) = (9, 15);

    fn transition_start_local() -> NaiveTime {
        NaiveTime::from_hms_opt(2, 0, 0).unwrap()
    }
}

impl TimeZone for DstTester {
    type Offset = FixedOffset;

    fn from_offset(_: &Self::Offset) -> Self {
        DstTester
    }

    fn offset_from_local_date(&self, _: &NaiveDate) -> crate::LocalResult<Self::Offset> {
        unimplemented!()
    }

    fn offset_from_local_datetime(
        &self,
        local: &NaiveDateTime,
    ) -> crate::LocalResult<Self::Offset> {
        let local_to_winter_transition_start = NaiveDate::from_ymd_opt(
            local.year(),
            DstTester::TO_WINTER_MONTH_DAY.0,
            DstTester::TO_WINTER_MONTH_DAY.1,
        )
        .unwrap()
        .and_time(DstTester::transition_start_local());

        let local_to_winter_transition_end = NaiveDate::from_ymd_opt(
            local.year(),
            DstTester::TO_WINTER_MONTH_DAY.0,
            DstTester::TO_WINTER_MONTH_DAY.1,
        )
        .unwrap()
        .and_time(DstTester::transition_start_local() - Duration::hours(1));

        let local_to_summer_transition_start = NaiveDate::from_ymd_opt(
            local.year(),
            DstTester::TO_SUMMER_MONTH_DAY.0,
            DstTester::TO_SUMMER_MONTH_DAY.1,
        )
        .unwrap()
        .and_time(DstTester::transition_start_local());

        let local_to_summer_transition_end = NaiveDate::from_ymd_opt(
            local.year(),
            DstTester::TO_SUMMER_MONTH_DAY.0,
            DstTester::TO_SUMMER_MONTH_DAY.1,
        )
        .unwrap()
        .and_time(DstTester::transition_start_local() + Duration::hours(1));

        if *local < local_to_winter_transition_end || *local >= local_to_summer_transition_end {
            LocalResult::Single(DstTester::summer_offset())
        } else if *local >= local_to_winter_transition_start
            && *local < local_to_summer_transition_start
        {
            LocalResult::Single(DstTester::winter_offset())
        } else if *local >= local_to_winter_transition_end
            && *local < local_to_winter_transition_start
        {
            LocalResult::Ambiguous(DstTester::winter_offset(), DstTester::summer_offset())
        } else if *local >= local_to_summer_transition_start
            && *local < local_to_summer_transition_end
        {
            LocalResult::None
        } else {
            panic!("Unexpected local time {}", local)
        }
    }

    fn offset_from_utc_date(&self, _: &NaiveDate) -> Self::Offset {
        unimplemented!()
    }

    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> Self::Offset {
        let utc_to_winter_transition = NaiveDate::from_ymd_opt(
            utc.year(),
            DstTester::TO_WINTER_MONTH_DAY.0,
            DstTester::TO_WINTER_MONTH_DAY.1,
        )
        .unwrap()
        .and_time(DstTester::transition_start_local())
            - DstTester::summer_offset();

        let utc_to_summer_transition = NaiveDate::from_ymd_opt(
            utc.year(),
            DstTester::TO_SUMMER_MONTH_DAY.0,
            DstTester::TO_SUMMER_MONTH_DAY.1,
        )
        .unwrap()
        .and_time(DstTester::transition_start_local())
            - DstTester::winter_offset();

        if *utc < utc_to_winter_transition || *utc >= utc_to_summer_transition {
            DstTester::summer_offset()
        } else if *utc >= utc_to_winter_transition && *utc < utc_to_summer_transition {
            DstTester::winter_offset()
        } else {
            panic!("Unexpected utc time {}", utc)
        }
    }
}

#[test]
fn test_datetime_add_days() {
    let est = FixedOffset::west_opt(5 * 60 * 60).unwrap();
    let kst = FixedOffset::east_opt(9 * 60 * 60).unwrap();

    assert_eq!(
        format!("{}", est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Days::new(5)),
        "2014-05-11 07:08:09 -05:00"
    );
    assert_eq!(
        format!("{}", kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Days::new(5)),
        "2014-05-11 07:08:09 +09:00"
    );

    assert_eq!(
        format!("{}", est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Days::new(35)),
        "2014-06-10 07:08:09 -05:00"
    );
    assert_eq!(
        format!("{}", kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Days::new(35)),
        "2014-06-10 07:08:09 +09:00"
    );

    assert_eq!(
        format!("{}", DstTester.with_ymd_and_hms(2014, 4, 6, 7, 8, 9).unwrap() + Days::new(5)),
        "2014-04-11 07:08:09 +09:00"
    );
    assert_eq!(
        format!("{}", DstTester.with_ymd_and_hms(2014, 4, 6, 7, 8, 9).unwrap() + Days::new(10)),
        "2014-04-16 07:08:09 +08:00"
    );

    assert_eq!(
        format!("{}", DstTester.with_ymd_and_hms(2014, 9, 6, 7, 8, 9).unwrap() + Days::new(5)),
        "2014-09-11 07:08:09 +08:00"
    );
    assert_eq!(
        format!("{}", DstTester.with_ymd_and_hms(2014, 9, 6, 7, 8, 9).unwrap() + Days::new(10)),
        "2014-09-16 07:08:09 +09:00"
    );
}

#[test]
fn test_datetime_sub_days() {
    let est = FixedOffset::west_opt(5 * 60 * 60).unwrap();
    let kst = FixedOffset::east_opt(9 * 60 * 60).unwrap();

    assert_eq!(
        format!("{}", est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Days::new(5)),
        "2014-05-01 07:08:09 -05:00"
    );
    assert_eq!(
        format!("{}", kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Days::new(5)),
        "2014-05-01 07:08:09 +09:00"
    );

    assert_eq!(
        format!("{}", est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Days::new(35)),
        "2014-04-01 07:08:09 -05:00"
    );
    assert_eq!(
        format!("{}", kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Days::new(35)),
        "2014-04-01 07:08:09 +09:00"
    );
}

#[test]
fn test_datetime_add_months() {
    let est = FixedOffset::west_opt(5 * 60 * 60).unwrap();
    let kst = FixedOffset::east_opt(9 * 60 * 60).unwrap();

    assert_eq!(
        format!("{}", est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Months::new(1)),
        "2014-06-06 07:08:09 -05:00"
    );
    assert_eq!(
        format!("{}", kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Months::new(1)),
        "2014-06-06 07:08:09 +09:00"
    );

    assert_eq!(
        format!("{}", est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Months::new(5)),
        "2014-10-06 07:08:09 -05:00"
    );
    assert_eq!(
        format!("{}", kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Months::new(5)),
        "2014-10-06 07:08:09 +09:00"
    );
}

#[test]
fn test_datetime_sub_months() {
    let est = FixedOffset::west_opt(5 * 60 * 60).unwrap();
    let kst = FixedOffset::east_opt(9 * 60 * 60).unwrap();

    assert_eq!(
        format!("{}", est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Months::new(1)),
        "2014-04-06 07:08:09 -05:00"
    );
    assert_eq!(
        format!("{}", kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Months::new(1)),
        "2014-04-06 07:08:09 +09:00"
    );

    assert_eq!(
        format!("{}", est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Months::new(5)),
        "2013-12-06 07:08:09 -05:00"
    );
    assert_eq!(
        format!("{}", kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Months::new(5)),
        "2013-12-06 07:08:09 +09:00"
    );
}

// local helper function to easily create a DateTime<FixedOffset>
fn ymdhms(
    fixedoffset: &FixedOffset,
    year: i32,
    month: u32,
    day: u32,
    hour: u32,
    min: u32,
    sec: u32,
) -> DateTime<FixedOffset> {
    fixedoffset.with_ymd_and_hms(year, month, day, hour, min, sec).unwrap()
}

// local helper function to easily create a DateTime<FixedOffset>
fn ymdhms_milli(
    fixedoffset: &FixedOffset,
    year: i32,
    month: u32,
    day: u32,
    hour: u32,
    min: u32,
    sec: u32,
    milli: i64,
) -> DateTime<FixedOffset> {
    fixedoffset
        .with_ymd_and_hms(year, month, day, hour, min, sec)
        .unwrap()
        .checked_add_signed(Duration::milliseconds(milli))
        .unwrap()
}

// local helper function to easily create a DateTime<FixedOffset>
fn ymdhms_micro(
    fixedoffset: &FixedOffset,
    year: i32,
    month: u32,
    day: u32,
    hour: u32,
    min: u32,
    sec: u32,
    micro: i64,
) -> DateTime<FixedOffset> {
    fixedoffset
        .with_ymd_and_hms(year, month, day, hour, min, sec)
        .unwrap()
        .checked_add_signed(Duration::microseconds(micro))
        .unwrap()
}

// local helper function to easily create a DateTime<FixedOffset>
fn ymdhms_nano(
    fixedoffset: &FixedOffset,
    year: i32,
    month: u32,
    day: u32,
    hour: u32,
    min: u32,
    sec: u32,
    nano: i64,
) -> DateTime<FixedOffset> {
    fixedoffset
        .with_ymd_and_hms(year, month, day, hour, min, sec)
        .unwrap()
        .checked_add_signed(Duration::nanoseconds(nano))
        .unwrap()
}

// local helper function to easily create a DateTime<Utc>
fn ymdhms_utc(year: i32, month: u32, day: u32, hour: u32, min: u32, sec: u32) -> DateTime<Utc> {
    Utc.with_ymd_and_hms(year, month, day, hour, min, sec).unwrap()
}

// local helper function to easily create a DateTime<Utc>
fn ymdhms_milli_utc(
    year: i32,
    month: u32,
    day: u32,
    hour: u32,
    min: u32,
    sec: u32,
    milli: i64,
) -> DateTime<Utc> {
    Utc.with_ymd_and_hms(year, month, day, hour, min, sec)
        .unwrap()
        .checked_add_signed(Duration::milliseconds(milli))
        .unwrap()
}

#[test]
fn test_datetime_offset() {
    let est = FixedOffset::west_opt(5 * 60 * 60).unwrap();
    let edt = FixedOffset::west_opt(4 * 60 * 60).unwrap();
    let kst = FixedOffset::east_opt(9 * 60 * 60).unwrap();

    assert_eq!(
        format!("{}", Utc.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap()),
        "2014-05-06 07:08:09 UTC"
    );
    assert_eq!(
        format!("{}", edt.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap()),
        "2014-05-06 07:08:09 -04:00"
    );
    assert_eq!(
        format!("{}", kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap()),
        "2014-05-06 07:08:09 +09:00"
    );
    assert_eq!(
        format!("{:?}", Utc.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap()),
        "2014-05-06T07:08:09Z"
    );
    assert_eq!(
        format!("{:?}", edt.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap()),
        "2014-05-06T07:08:09-04:00"
    );
    assert_eq!(
        format!("{:?}", kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap()),
        "2014-05-06T07:08:09+09:00"
    );

    // edge cases
    assert_eq!(
        format!("{:?}", Utc.with_ymd_and_hms(2014, 5, 6, 0, 0, 0).unwrap()),
        "2014-05-06T00:00:00Z"
    );
    assert_eq!(
        format!("{:?}", edt.with_ymd_and_hms(2014, 5, 6, 0, 0, 0).unwrap()),
        "2014-05-06T00:00:00-04:00"
    );
    assert_eq!(
        format!("{:?}", kst.with_ymd_and_hms(2014, 5, 6, 0, 0, 0).unwrap()),
        "2014-05-06T00:00:00+09:00"
    );
    assert_eq!(
        format!("{:?}", Utc.with_ymd_and_hms(2014, 5, 6, 23, 59, 59).unwrap()),
        "2014-05-06T23:59:59Z"
    );
    assert_eq!(
        format!("{:?}", edt.with_ymd_and_hms(2014, 5, 6, 23, 59, 59).unwrap()),
        "2014-05-06T23:59:59-04:00"
    );
    assert_eq!(
        format!("{:?}", kst.with_ymd_and_hms(2014, 5, 6, 23, 59, 59).unwrap()),
        "2014-05-06T23:59:59+09:00"
    );

    let dt = Utc.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap();
    assert_eq!(dt, edt.with_ymd_and_hms(2014, 5, 6, 3, 8, 9).unwrap());
    assert_eq!(
        dt + Duration::seconds(3600 + 60 + 1),
        Utc.with_ymd_and_hms(2014, 5, 6, 8, 9, 10).unwrap()
    );
    assert_eq!(
        dt.signed_duration_since(edt.with_ymd_and_hms(2014, 5, 6, 10, 11, 12).unwrap()),
        Duration::seconds(-7 * 3600 - 3 * 60 - 3)
    );

    assert_eq!(*Utc.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap().offset(), Utc);
    assert_eq!(*edt.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap().offset(), edt);
    assert!(*edt.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap().offset() != est);
}

#[test]
fn test_datetime_date_and_time() {
    let tz = FixedOffset::east_opt(5 * 60 * 60).unwrap();
    let d = tz.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap();
    assert_eq!(d.time(), NaiveTime::from_hms_opt(7, 8, 9).unwrap());
    assert_eq!(d.date_naive(), NaiveDate::from_ymd_opt(2014, 5, 6).unwrap());

    let tz = FixedOffset::east_opt(4 * 60 * 60).unwrap();
    let d = tz.with_ymd_and_hms(2016, 5, 4, 3, 2, 1).unwrap();
    assert_eq!(d.time(), NaiveTime::from_hms_opt(3, 2, 1).unwrap());
    assert_eq!(d.date_naive(), NaiveDate::from_ymd_opt(2016, 5, 4).unwrap());

    let tz = FixedOffset::west_opt(13 * 60 * 60).unwrap();
    let d = tz.with_ymd_and_hms(2017, 8, 9, 12, 34, 56).unwrap();
    assert_eq!(d.time(), NaiveTime::from_hms_opt(12, 34, 56).unwrap());
    assert_eq!(d.date_naive(), NaiveDate::from_ymd_opt(2017, 8, 9).unwrap());

    let utc_d = Utc.with_ymd_and_hms(2017, 8, 9, 12, 34, 56).unwrap();
    assert!(utc_d < d);
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_with_timezone() {
    let local_now = Local::now();
    let utc_now = local_now.with_timezone(&Utc);
    let local_now2 = utc_now.with_timezone(&Local);
    assert_eq!(local_now, local_now2);
}

#[test]
fn test_datetime_rfc2822() {
    let edt = FixedOffset::east_opt(5 * 60 * 60).unwrap();

    // timezone 0
    assert_eq!(
        Utc.with_ymd_and_hms(2015, 2, 18, 23, 16, 9).unwrap().to_rfc2822(),
        "Wed, 18 Feb 2015 23:16:09 +0000"
    );
    // timezone +05
    assert_eq!(
        edt.from_local_datetime(
            &NaiveDate::from_ymd_opt(2015, 2, 18)
                .unwrap()
                .and_hms_milli_opt(23, 16, 9, 150)
                .unwrap()
        )
        .unwrap()
        .to_rfc2822(),
        "Wed, 18 Feb 2015 23:16:09 +0500"
    );
    // seconds 60
    assert_eq!(
        edt.from_local_datetime(
            &NaiveDate::from_ymd_opt(2015, 2, 18)
                .unwrap()
                .and_hms_micro_opt(23, 59, 59, 1_234_567)
                .unwrap()
        )
        .unwrap()
        .to_rfc2822(),
        "Wed, 18 Feb 2015 23:59:60 +0500"
    );

    assert_eq!(
        DateTime::parse_from_rfc2822("Wed, 18 Feb 2015 23:16:09 +0000"),
        Ok(FixedOffset::east_opt(0).unwrap().with_ymd_and_hms(2015, 2, 18, 23, 16, 9).unwrap())
    );
    assert_eq!(
        DateTime::parse_from_rfc2822("Wed, 18 Feb 2015 23:16:09 -0000"),
        Ok(FixedOffset::east_opt(0).unwrap().with_ymd_and_hms(2015, 2, 18, 23, 16, 9).unwrap())
    );
    assert_eq!(
        ymdhms_milli(&edt, 2015, 2, 18, 23, 59, 58, 1_234_567).to_rfc2822(),
        "Thu, 19 Feb 2015 00:20:32 +0500"
    );
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc2822("Wed, 18 Feb 2015 23:59:58 +0500"),
        Ok(ymdhms(&edt, 2015, 2, 18, 23, 59, 58))
    );
    assert_ne!(
        DateTime::<FixedOffset>::parse_from_rfc2822("Wed, 18 Feb 2015 23:59:58 +0500"),
        Ok(ymdhms_milli(&edt, 2015, 2, 18, 23, 59, 58, 500))
    );

    // many varying whitespace intermixed
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc2822(
            "\t\t\tWed,\n\t\t18 \r\n\t\tFeb \u{3000} 2015\r\n\t\t\t23:59:58    \t+0500"
        ),
        Ok(ymdhms(&edt, 2015, 2, 18, 23, 59, 58))
    );
    // example from RFC 2822 Appendix A.5.
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc2822(
            "Thu,\n\t13\n      Feb\n        1969\n    23:32\n             -0330 (Newfoundland Time)"
        ),
        Ok(
            ymdhms(
                &FixedOffset::east_opt(-3 * 60 * 60 - 30 * 60).unwrap(),
                1969, 2, 13, 23, 32, 0,
            )
        )
    );
    // example from RFC 2822 Appendix A.5. without trailing " (Newfoundland Time)"
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc2822(
            "Thu,\n\t13\n      Feb\n        1969\n    23:32\n             -0330"
        ),
        Ok(
            ymdhms(&FixedOffset::east_opt(-3 * 60 * 60 - 30 * 60).unwrap(), 1969, 2, 13, 23, 32, 0,)
        )
    );

    // bad year
    assert!(DateTime::<FixedOffset>::parse_from_rfc2822("31 DEC 262143 23:59 -2359").is_err());
    // wrong format
    assert!(
        DateTime::<FixedOffset>::parse_from_rfc2822("Wed, 18 Feb 2015 23:16:09 +00:00").is_err()
    );
    // full name day of week
    assert!(DateTime::<FixedOffset>::parse_from_rfc2822("Wednesday, 18 Feb 2015 23:16:09 +0000")
        .is_err());
    // full name day of week
    assert!(DateTime::<FixedOffset>::parse_from_rfc2822("Wednesday 18 Feb 2015 23:16:09 +0000")
        .is_err());
    // wrong day of week separator '.'
    assert!(DateTime::<FixedOffset>::parse_from_rfc2822("Wed. 18 Feb 2015 23:16:09 +0000").is_err());
    // *trailing* space causes failure
    assert!(
        DateTime::<FixedOffset>::parse_from_rfc2822("Wed, 18 Feb 2015 23:16:09 +0000   ").is_err()
    );
}

#[test]
fn test_datetime_rfc3339() {
    let edt5 = FixedOffset::east_opt(5 * 60 * 60).unwrap();
    let edt0 = FixedOffset::east_opt(0).unwrap();

    // timezone 0
    assert_eq!(
        Utc.with_ymd_and_hms(2015, 2, 18, 23, 16, 9).unwrap().to_rfc3339(),
        "2015-02-18T23:16:09+00:00"
    );
    // timezone +05
    assert_eq!(
        edt5.from_local_datetime(
            &NaiveDate::from_ymd_opt(2015, 2, 18)
                .unwrap()
                .and_hms_milli_opt(23, 16, 9, 150)
                .unwrap()
        )
        .unwrap()
        .to_rfc3339(),
        "2015-02-18T23:16:09.150+05:00"
    );

    assert_eq!(ymdhms_utc(2015, 2, 18, 23, 16, 9).to_rfc3339(), "2015-02-18T23:16:09+00:00");
    assert_eq!(
        ymdhms_milli(&edt5, 2015, 2, 18, 23, 16, 9, 150).to_rfc3339(),
        "2015-02-18T23:16:09.150+05:00"
    );
    assert_eq!(
        ymdhms_micro(&edt5, 2015, 2, 18, 23, 59, 59, 1_234_567).to_rfc3339(),
        "2015-02-19T00:00:00.234567+05:00"
    );
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:59.123+05:00"),
        Ok(ymdhms_micro(&edt5, 2015, 2, 18, 23, 59, 59, 123_000))
    );
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:59.123456+05:00"),
        Ok(ymdhms_micro(&edt5, 2015, 2, 18, 23, 59, 59, 123_456))
    );
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:59.123456789+05:00"),
        Ok(ymdhms_nano(&edt5, 2015, 2, 18, 23, 59, 59, 123_456_789))
    );
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:16:09Z"),
        Ok(ymdhms(&edt0, 2015, 2, 18, 23, 16, 9))
    );

    assert_eq!(
        ymdhms_micro(&edt5, 2015, 2, 18, 23, 59, 59, 1_234_567).to_rfc3339(),
        "2015-02-19T00:00:00.234567+05:00"
    );
    assert_eq!(
        ymdhms_milli(&edt5, 2015, 2, 18, 23, 16, 9, 150).to_rfc3339(),
        "2015-02-18T23:16:09.150+05:00"
    );
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T00:00:00.234567+05:00"),
        Ok(ymdhms_micro(&edt5, 2015, 2, 18, 0, 0, 0, 234_567))
    );
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:16:09Z"),
        Ok(ymdhms(&edt0, 2015, 2, 18, 23, 16, 9))
    );
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc2822("Wed, 18 Feb 2015 23:59:60 +0500"),
        Ok(edt5
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 59, 59, 1_000)
                    .unwrap()
            )
            .unwrap())
    );
    assert!(DateTime::parse_from_rfc2822("31 DEC 262143 23:59 -2359").is_err());
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:60.234567+05:00"),
        Ok(edt5
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_micro_opt(23, 59, 59, 1_234_567)
                    .unwrap()
            )
            .unwrap())
    );
    assert_eq!(ymdhms_utc(2015, 2, 18, 23, 16, 9).to_rfc3339(), "2015-02-18T23:16:09+00:00");

    assert!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:60.234567 +05:00").is_err()
    );
    assert!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:059:60.234567+05:00").is_err()
    );
    assert!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:60.234567+05:00PST").is_err()
    );
    assert!(DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:60.234567+PST").is_err());
    assert!(DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:60.234567PST").is_err());
    assert!(DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:60.234567+0500").is_err());
    assert!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:60.234567+05:00:00").is_err()
    );
    assert!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18 23:59:60.234567+05:00").is_err()
    );
    assert!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:60.234567:+05:00").is_err()
    );
    assert!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:60.234567+05:00 ").is_err()
    );
    assert!(
        DateTime::<FixedOffset>::parse_from_rfc3339(" 2015-02-18T23:59:60.234567+05:00").is_err()
    );
    assert!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015- 02-18T23:59:60.234567+05:00").is_err()
    );
    assert!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:60.234567A+05:00").is_err()
    );
}

#[test]
fn test_rfc3339_opts() {
    use crate::SecondsFormat::*;
    let pst = FixedOffset::east_opt(8 * 60 * 60).unwrap();
    let dt = pst
        .from_local_datetime(
            &NaiveDate::from_ymd_opt(2018, 1, 11)
                .unwrap()
                .and_hms_nano_opt(10, 5, 13, 84_660_000)
                .unwrap(),
        )
        .unwrap();
    assert_eq!(dt.to_rfc3339_opts(Secs, false), "2018-01-11T10:05:13+08:00");
    assert_eq!(dt.to_rfc3339_opts(Secs, true), "2018-01-11T10:05:13+08:00");
    assert_eq!(dt.to_rfc3339_opts(Millis, false), "2018-01-11T10:05:13.084+08:00");
    assert_eq!(dt.to_rfc3339_opts(Micros, false), "2018-01-11T10:05:13.084660+08:00");
    assert_eq!(dt.to_rfc3339_opts(Nanos, false), "2018-01-11T10:05:13.084660000+08:00");
    assert_eq!(dt.to_rfc3339_opts(AutoSi, false), "2018-01-11T10:05:13.084660+08:00");

    let ut = DateTime::<Utc>::from_utc(dt.naive_utc(), Utc);
    assert_eq!(ut.to_rfc3339_opts(Secs, false), "2018-01-11T02:05:13+00:00");
    assert_eq!(ut.to_rfc3339_opts(Secs, true), "2018-01-11T02:05:13Z");
    assert_eq!(ut.to_rfc3339_opts(Millis, false), "2018-01-11T02:05:13.084+00:00");
    assert_eq!(ut.to_rfc3339_opts(Millis, true), "2018-01-11T02:05:13.084Z");
    assert_eq!(ut.to_rfc3339_opts(Micros, true), "2018-01-11T02:05:13.084660Z");
    assert_eq!(ut.to_rfc3339_opts(Nanos, true), "2018-01-11T02:05:13.084660000Z");
    assert_eq!(ut.to_rfc3339_opts(AutoSi, true), "2018-01-11T02:05:13.084660Z");
}

#[test]
#[should_panic]
fn test_rfc3339_opts_nonexhaustive() {
    use crate::SecondsFormat;
    let dt = Utc.with_ymd_and_hms(1999, 10, 9, 1, 2, 3).unwrap();
    let _ = dt.to_rfc3339_opts(SecondsFormat::__NonExhaustive, true);
}

#[test]
fn test_datetime_from_str() {
    assert_eq!(
        "2015-02-18T23:16:9.15Z".parse::<DateTime<FixedOffset>>(),
        Ok(FixedOffset::east_opt(0)
            .unwrap()
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert_eq!(
        "2015-02-18T23:16:9.15Z".parse::<DateTime<Utc>>(),
        Ok(Utc
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert_eq!(
        "2015-02-18T23:16:9.15 UTC".parse::<DateTime<Utc>>(),
        Ok(Utc
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert_eq!(
        "2015-02-18T23:16:9.15UTC".parse::<DateTime<Utc>>(),
        Ok(Utc
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );

    assert_eq!(
        "2015-2-18T23:16:9.15Z".parse::<DateTime<FixedOffset>>(),
        Ok(FixedOffset::east_opt(0)
            .unwrap()
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert_eq!(
        "2015-2-18T13:16:9.15-10:00".parse::<DateTime<FixedOffset>>(),
        Ok(FixedOffset::west_opt(10 * 3600)
            .unwrap()
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(13, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert!("2015-2-18T23:16:9.15".parse::<DateTime<FixedOffset>>().is_err());

    assert_eq!(
        "2015-2-18T23:16:9.15Z".parse::<DateTime<Utc>>(),
        Ok(Utc
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert_eq!(
        "2015-2-18T13:16:9.15-10:00".parse::<DateTime<Utc>>(),
        Ok(Utc
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert!("2015-2-18T23:16:9.15".parse::<DateTime<Utc>>().is_err());

    // no test for `DateTime<Local>`, we cannot verify that much.
}

#[test]
fn test_parse_datetime_utc() {
    // valid cases
    let valid = [
        "2001-02-03T04:05:06Z",
        "2001-02-03T04:05:06+0000",
        "2001-02-03T04:05:06-00:00",
        "2001-02-03T04:05:06-01:00",
        "2012-12-12T12:12:12Z",
        "2015-02-18T23:16:09.153Z",
        "2015-2-18T23:16:09.153Z",
        "+2015-2-18T23:16:09.153Z",
        "-77-02-18T23:16:09Z",
        "+82701-05-6T15:9:60.898989898989Z",
    ];
    for &s in &valid {
        eprintln!("test_parse_datetime_utc valid {:?}", s);
        let d = match s.parse::<DateTime<Utc>>() {
            Ok(d) => d,
            Err(e) => panic!("parsing `{}` has failed: {}", s, e),
        };
        let s_ = format!("{:?}", d);
        // `s` and `s_` may differ, but `s.parse()` and `s_.parse()` must be same
        let d_ = match s_.parse::<DateTime<Utc>>() {
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
    let invalid = [
        "",                                                          // empty
        "Z",                                                         // missing data
        "15Z",                                                       // missing data
        "15:8:9Z",                                                   // missing date
        "15-8-9Z",                                                   // missing time or date
        "Fri, 09 Aug 2013 23:54:35 GMT",                             // valid datetime, wrong format
        "Sat Jun 30 23:59:60 2012",                                  // valid datetime, wrong format
        "1441497364.649",                                            // valid datetime, wrong format
        "+1441497364.649",                                           // valid datetime, wrong format
        "+1441497364",                                               // valid datetime, wrong format
        "+1441497364Z",                                              // valid datetime, wrong format
        "2014/02/03 04:05:06Z",                                      // valid datetime, wrong format
        "2001-02-03T04:05:0600:00",   // valid datetime, timezone too close
        "2015-15-15T15:15:15Z",       // invalid datetime
        "2012-12-12T12:12:12x",       // invalid timezone
        "2012-123-12T12:12:12Z",      // invalid month
        "2012-12-77T12:12:12Z",       // invalid day
        "2012-12-12T26:12:12Z",       // invalid hour
        "2012-12-12T12:61:12Z",       // invalid minute
        "2012-12-12T12:12:62Z",       // invalid second
        "2012-12-12 T12:12:12Z",      // space after date
        "2012-12-12t12:12:12Z",       // wrong divider 't'
        "2012-12-12T12:12:12ZZ",      // trailing literal 'Z'
        "+802701-12-12T12:12:12Z",    // invalid year (out of bounds)
        "+ 2012-12-12T12:12:12Z",     // invalid space before year
        "2012 -12-12T12:12:12Z",      // space after year
        "2012  -12-12T12:12:12Z",     // multi space after year
        "2012- 12-12T12:12:12Z",      // space after year divider
        "2012-  12-12T12:12:12Z",     // multi space after year divider
        "2012-12-12T 12:12:12Z",      // space after date-time divider
        "2012-12-12T12 :12:12Z",      // space after hour
        "2012-12-12T12  :12:12Z",     // multi space after hour
        "2012-12-12T12: 12:12Z",      // space before minute
        "2012-12-12T12:  12:12Z",     // multi space before minute
        "2012-12-12T12 : 12:12Z",     // space space before and after hour-minute divider
        "2012-12-12T12:12:12Z ",      // trailing space
        " 2012-12-12T12:12:12Z",      // leading space
        "2001-02-03T04:05:06-00 00",  // invalid timezone spacing
        "2001-02-03T04:05:06-01: 00", // invalid timezone spacing
        "2001-02-03T04:05:06-01 :00", // invalid timezone spacing
        "2001-02-03T04:05:06-01 : 00", // invalid timezone spacing
        "2001-02-03T04:05:06-01 :     00", // invalid timezone spacing
        "2001-02-03T04:05:06-01 :    :00", // invalid timezone spacing
        "  +82701  -  05  -  6  T  15  :  9  : 60.898989898989   Z", // valid datetime, wrong format
    ];
    for &s in invalid.iter() {
        eprintln!("test_parse_datetime_utc invalid {:?}", s);
        assert!(s.parse::<DateTime<Utc>>().is_err());
    }
}

#[test]
fn test_utc_datetime_from_str() {
    let edt = FixedOffset::east_opt(570 * 60).unwrap();
    let edt0 = FixedOffset::east_opt(0).unwrap();
    let wdt = FixedOffset::west_opt(10 * 3600).unwrap();
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_str("2014-5-7T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z"),
        Ok(ymdhms(&edt, 2014, 5, 7, 12, 34, 56))
    ); // ignore offset
    assert!(DateTime::parse_from_str("20140507000000", "%Y%m%d%H%M%S").is_err()); // no offset
    assert!(DateTime::parse_from_str("Fri, 09 Aug 2013 23:54:35 GMT", "%a, %d %b %Y %H:%M:%S GMT")
        .is_err());
    assert_eq!(
        Utc.datetime_from_str("Fri, 09 Aug 2013 23:54:35 GMT", "%a, %d %b %Y %H:%M:%S GMT"),
        Ok(Utc.with_ymd_and_hms(2013, 8, 9, 23, 54, 35).unwrap())
    );

    assert_eq!(
        "2015-02-18T23:16:9.15Z".parse::<DateTime<FixedOffset>>(),
        Ok(ymdhms_milli(&edt0, 2015, 2, 18, 23, 16, 9, 150))
    );
    assert_eq!(
        "2015-02-18T23:16:9.15Z".parse::<DateTime<Utc>>(),
        Ok(ymdhms_milli_utc(2015, 2, 18, 23, 16, 9, 150)),
    );
    assert_eq!(
        "2015-02-18T23:16:9.15 UTC".parse::<DateTime<Utc>>(),
        Ok(ymdhms_milli_utc(2015, 2, 18, 23, 16, 9, 150))
    );
    assert_eq!(
        "2015-02-18T23:16:9.15UTC".parse::<DateTime<Utc>>(),
        Ok(ymdhms_milli_utc(2015, 2, 18, 23, 16, 9, 150))
    );

    assert_eq!(
        "2015-2-18T23:16:9.15Z".parse::<DateTime<FixedOffset>>(),
        Ok(ymdhms_milli(&edt0, 2015, 2, 18, 23, 16, 9, 150))
    );
    assert_eq!(
        "2015-2-18T13:16:9.15-10:00".parse::<DateTime<FixedOffset>>(),
        Ok(ymdhms_milli(&wdt, 2015, 2, 18, 13, 16, 9, 150))
    );
    assert!("2015-2-18T23:16:9.15".parse::<DateTime<FixedOffset>>().is_err());

    assert_eq!(
        "2015-2-18T23:16:9.15Z".parse::<DateTime<Utc>>(),
        Ok(ymdhms_milli_utc(2015, 2, 18, 23, 16, 9, 150))
    );
    assert_eq!(
        "2015-2-18T13:16:9.15-10:00".parse::<DateTime<Utc>>(),
        Ok(ymdhms_milli_utc(2015, 2, 18, 23, 16, 9, 150))
    );
    assert!("2015-2-18T23:16:9.15".parse::<DateTime<Utc>>().is_err());

    // no test for `DateTime<Local>`, we cannot verify that much.
}

#[test]
fn test_utc_datetime_from_str_with_spaces() {
    let dt = ymdhms_utc(2013, 8, 9, 23, 54, 35);
    // with varying spaces - should succeed
    assert_eq!(Utc.datetime_from_str(" Aug 09 2013 23:54:35", " %b %d %Y %H:%M:%S"), Ok(dt),);
    assert_eq!(Utc.datetime_from_str("Aug 09 2013 23:54:35 ", "%b %d %Y %H:%M:%S "), Ok(dt),);
    assert_eq!(Utc.datetime_from_str(" Aug 09 2013  23:54:35 ", " %b %d %Y  %H:%M:%S "), Ok(dt),);
    assert_eq!(Utc.datetime_from_str("  Aug 09 2013 23:54:35", "  %b %d %Y %H:%M:%S"), Ok(dt),);
    assert_eq!(Utc.datetime_from_str("   Aug 09 2013 23:54:35", "   %b %d %Y %H:%M:%S"), Ok(dt),);
    assert_eq!(
        Utc.datetime_from_str("\n\tAug 09 2013 23:54:35  ", "\n\t%b %d %Y %H:%M:%S  "),
        Ok(dt),
    );
    assert_eq!(Utc.datetime_from_str("\tAug 09 2013 23:54:35\t", "\t%b %d %Y %H:%M:%S\t"), Ok(dt),);
    assert_eq!(Utc.datetime_from_str("Aug  09 2013 23:54:35", "%b  %d %Y %H:%M:%S"), Ok(dt),);
    assert_eq!(Utc.datetime_from_str("Aug    09 2013 23:54:35", "%b    %d %Y %H:%M:%S"), Ok(dt),);
    assert_eq!(Utc.datetime_from_str("Aug  09 2013\t23:54:35", "%b  %d %Y\t%H:%M:%S"), Ok(dt),);
    assert_eq!(Utc.datetime_from_str("Aug  09 2013\t\t23:54:35", "%b  %d %Y\t\t%H:%M:%S"), Ok(dt),);
    // with varying spaces - should fail
    // leading whitespace in format
    assert!(Utc.datetime_from_str("Aug 09 2013 23:54:35", " %b %d %Y %H:%M:%S").is_err());
    // trailing whitespace in format
    assert!(Utc.datetime_from_str("Aug 09 2013 23:54:35", "%b %d %Y %H:%M:%S ").is_err());
    // extra mid-string whitespace in format
    assert!(Utc.datetime_from_str("Aug 09 2013 23:54:35", "%b %d %Y  %H:%M:%S").is_err());
    // mismatched leading whitespace
    assert!(Utc.datetime_from_str("\tAug 09 2013 23:54:35", "\n%b %d %Y %H:%M:%S").is_err());
    // mismatched trailing whitespace
    assert!(Utc.datetime_from_str("Aug 09 2013 23:54:35 ", "%b %d %Y %H:%M:%S\n").is_err());
    // mismatched mid-string whitespace
    assert!(Utc.datetime_from_str("Aug 09 2013 23:54:35", "%b %d %Y\t%H:%M:%S").is_err());
    // trailing whitespace in format
    assert!(Utc.datetime_from_str("Aug 09 2013 23:54:35", "%b %d %Y %H:%M:%S ").is_err());
    // trailing whitespace (newline) in format
    assert!(Utc.datetime_from_str("Aug 09 2013 23:54:35", "%b %d %Y %H:%M:%S\n").is_err());
    // leading space in data
    assert!(Utc.datetime_from_str(" Aug 09 2013 23:54:35", "%b %d %Y %H:%M:%S").is_err());
    // trailing space in data
    assert!(Utc.datetime_from_str("Aug 09 2013 23:54:35 ", "%b %d %Y %H:%M:%S").is_err());
    // trailing tab in data
    assert!(Utc.datetime_from_str("Aug 09 2013 23:54:35\t", "%b %d %Y %H:%M:%S").is_err());
    // mismatched newlines
    assert!(Utc.datetime_from_str("\nAug 09 2013 23:54:35", "%b %d %Y %H:%M:%S\n").is_err());
    // trailing literal in data
    assert!(Utc.datetime_from_str("Aug 09 2013 23:54:35 !!!", "%b %d %Y %H:%M:%S ").is_err());
}

#[test]
fn test_datetime_parse_from_str() {
    let dt = ymdhms(&FixedOffset::east_opt(-9 * 60 * 60).unwrap(), 2013, 8, 9, 23, 54, 35);
    let parse = DateTime::<FixedOffset>::parse_from_str;

    // timezone variations

    //
    // %Z
    //
    // wrong timezone format
    assert!(parse("Aug 09 2013 23:54:35 -0900", "%b %d %Y %H:%M:%S %Z").is_err());
    // bad timezone data?
    assert!(parse("Aug 09 2013 23:54:35 PST", "%b %d %Y %H:%M:%S %Z").is_err());
    // bad timezone data
    assert!(parse("Aug 09 2013 23:54:35 XXXXX", "%b %d %Y %H:%M:%S %Z").is_err());

    //
    // %z
    //
    assert_eq!(parse("Aug 09 2013 23:54:35 -0900", "%b %d %Y %H:%M:%S %z"), Ok(dt));
    assert!(parse("Aug 09 2013 23:54:35 -09 00", "%b %d %Y %H:%M:%S %z").is_err());
    assert_eq!(parse("Aug 09 2013 23:54:35 -09:00", "%b %d %Y %H:%M:%S %z"), Ok(dt));
    assert!(parse("Aug 09 2013 23:54:35 -09 : 00", "%b %d %Y %H:%M:%S %z").is_err());
    assert_eq!(parse("Aug 09 2013 23:54:35 --0900", "%b %d %Y %H:%M:%S -%z"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 +-0900", "%b %d %Y %H:%M:%S +%z"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -09:00 ", "%b %d %Y %H:%M:%S %z "), Ok(dt));
    // trailing newline after timezone
    assert!(parse("Aug 09 2013 23:54:35 -09:00\n", "%b %d %Y %H:%M:%S %z").is_err());
    assert!(parse("Aug 09 2013 23:54:35 -09:00\n", "%b %d %Y %H:%M:%S %z ").is_err());
    // trailing colon
    assert!(parse("Aug 09 2013 23:54:35 -09:00:", "%b %d %Y %H:%M:%S %z").is_err());
    // trailing colon with space
    assert!(parse("Aug 09 2013 23:54:35 -09:00: ", "%b %d %Y %H:%M:%S %z ").is_err());
    // trailing colon, mismatch space
    assert!(parse("Aug 09 2013 23:54:35 -09:00:", "%b %d %Y %H:%M:%S %z ").is_err());
    // wrong timezone data
    assert!(parse("Aug 09 2013 23:54:35 -09", "%b %d %Y %H:%M:%S %z").is_err());
    assert!(parse("Aug 09 2013 23:54:35 -09::00", "%b %d %Y %H:%M:%S %z").is_err());
    assert_eq!(parse("Aug 09 2013 23:54:35 -0900::", "%b %d %Y %H:%M:%S %z::"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -09:00:00", "%b %d %Y %H:%M:%S %z:00"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -09:00:00 ", "%b %d %Y %H:%M:%S %z:00 "), Ok(dt));

    //
    // %:z
    //
    assert_eq!(parse("Aug 09 2013 23:54:35  -09:00", "%b %d %Y %H:%M:%S  %:z"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -0900", "%b %d %Y %H:%M:%S %:z"), Ok(dt));
    assert!(parse("Aug 09 2013 23:54:35 -09 00", "%b %d %Y %H:%M:%S %:z").is_err());
    assert!(parse("Aug 09 2013 23:54:35 -09 : 00", "%b %d %Y %H:%M:%S %:z").is_err());
    assert!(parse("Aug 09 2013 23:54:35 -09 : 00:", "%b %d %Y %H:%M:%S %:z:").is_err());
    // wrong timezone data
    assert!(parse("Aug 09 2013 23:54:35 -09", "%b %d %Y %H:%M:%S %:z").is_err());
    assert!(parse("Aug 09 2013 23:54:35 -09::00", "%b %d %Y %H:%M:%S %:z").is_err());
    // timezone data hs too many colons
    assert!(parse("Aug 09 2013 23:54:35 -09:00:", "%b %d %Y %H:%M:%S %:z").is_err());
    // timezone data hs too many colons
    assert!(parse("Aug 09 2013 23:54:35 -09:00::", "%b %d %Y %H:%M:%S %:z").is_err());
    assert_eq!(parse("Aug 09 2013 23:54:35 -09:00::", "%b %d %Y %H:%M:%S %:z::"), Ok(dt));

    //
    // %::z
    //
    assert_eq!(parse("Aug 09 2013 23:54:35 -0900", "%b %d %Y %H:%M:%S %::z"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -09:00", "%b %d %Y %H:%M:%S %::z"), Ok(dt));
    assert!(parse("Aug 09 2013 23:54:35 -09 : 00", "%b %d %Y %H:%M:%S %::z").is_err());
    // mismatching colon expectations
    assert!(parse("Aug 09 2013 23:54:35 -09:00:00", "%b %d %Y %H:%M:%S %::z").is_err());
    assert!(parse("Aug 09 2013 23:54:35 -09::00", "%b %d %Y %H:%M:%S %::z").is_err());
    assert!(parse("Aug 09 2013 23:54:35 -09::00", "%b %d %Y %H:%M:%S %:z").is_err());
    // wrong timezone data
    assert!(parse("Aug 09 2013 23:54:35 -09", "%b %d %Y %H:%M:%S %::z").is_err());
    assert_eq!(parse("Aug 09 2013 23:54:35 -09001234", "%b %d %Y %H:%M:%S %::z1234"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -09:001234", "%b %d %Y %H:%M:%S %::z1234"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -0900 ", "%b %d %Y %H:%M:%S %::z "), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -0900\t\n", "%b %d %Y %H:%M:%S %::z\t\n"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -0900:", "%b %d %Y %H:%M:%S %::z:"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 :-0900:0", "%b %d %Y %H:%M:%S :%::z:0"), Ok(dt));
    // mismatching colons and spaces
    assert!(parse("Aug 09 2013 23:54:35 :-0900: ", "%b %d %Y %H:%M:%S :%::z::").is_err());
    // mismatching colons expectations
    assert!(parse("Aug 09 2013 23:54:35 -09:00:00", "%b %d %Y %H:%M:%S %::z").is_err());
    assert_eq!(parse("Aug 09 2013 -0900: 23:54:35", "%b %d %Y %::z: %H:%M:%S"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 :-0900:0 23:54:35", "%b %d %Y :%::z:0 %H:%M:%S"), Ok(dt));
    // mismatching colons expectations mid-string
    assert!(parse("Aug 09 2013 :-0900: 23:54:35", "%b %d %Y :%::z  %H:%M:%S").is_err());
    // mismatching colons expectations, before end
    assert!(parse("Aug 09 2013 23:54:35 -09:00:00 ", "%b %d %Y %H:%M:%S %::z ").is_err());

    //
    // %:::z
    //
    assert_eq!(parse("Aug 09 2013 23:54:35 -09:00", "%b %d %Y %H:%M:%S %:::z"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -0900", "%b %d %Y %H:%M:%S %:::z"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -0900  ", "%b %d %Y %H:%M:%S %:::z  "), Ok(dt));
    // wrong timezone data
    assert!(parse("Aug 09 2013 23:54:35 -09", "%b %d %Y %H:%M:%S %:::z").is_err());

    //
    // %::::z
    //
    // too many colons
    assert!(parse("Aug 09 2013 23:54:35 -0900", "%b %d %Y %H:%M:%S %::::z").is_err());
    // too many colons
    assert!(parse("Aug 09 2013 23:54:35 -09:00", "%b %d %Y %H:%M:%S %::::z").is_err());
    // too many colons
    assert!(parse("Aug 09 2013 23:54:35 -09:00:", "%b %d %Y %H:%M:%S %::::z").is_err());
    // too many colons
    assert!(parse("Aug 09 2013 23:54:35 -09:00:00", "%b %d %Y %H:%M:%S %::::z").is_err());

    //
    // %#z
    //
    assert_eq!(parse("Aug 09 2013 23:54:35 -09:00", "%b %d %Y %H:%M:%S %#z"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -0900", "%b %d %Y %H:%M:%S %#z"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35  -09:00  ", "%b %d %Y %H:%M:%S  %#z  "), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35  -0900  ", "%b %d %Y %H:%M:%S  %#z  "), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -09", "%b %d %Y %H:%M:%S %#z"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -0900", "%b %d %Y %H:%M:%S %#z"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35 -09:", "%b %d %Y %H:%M:%S %#z"), Ok(dt));
    assert!(parse("Aug 09 2013 23:54:35 -09: ", "%b %d %Y %H:%M:%S %#z ").is_err());
    assert_eq!(parse("Aug 09 2013 23:54:35+-09", "%b %d %Y %H:%M:%S+%#z"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 23:54:35--09", "%b %d %Y %H:%M:%S-%#z"), Ok(dt));
    assert!(parse("Aug 09 2013 -09:00 23:54:35", "%b %d %Y %#z%H:%M:%S").is_err());
    assert!(parse("Aug 09 2013 -0900 23:54:35", "%b %d %Y %#z%H:%M:%S").is_err());
    assert_eq!(parse("Aug 09 2013 -090023:54:35", "%b %d %Y %#z%H:%M:%S"), Ok(dt));
    assert_eq!(parse("Aug 09 2013 -09:0023:54:35", "%b %d %Y %#z%H:%M:%S"), Ok(dt));
    // timezone with partial minutes adjacent hours
    assert_ne!(parse("Aug 09 2013 -09023:54:35", "%b %d %Y %#z%H:%M:%S"), Ok(dt));
    // bad timezone data
    assert!(parse("Aug 09 2013 23:54:35 -09:00:00", "%b %d %Y %H:%M:%S %#z").is_err());
    // bad timezone data (partial minutes)
    assert!(parse("Aug 09 2013 23:54:35 -090", "%b %d %Y %H:%M:%S %#z").is_err());
    // bad timezone data (partial minutes) with trailing space
    assert!(parse("Aug 09 2013 23:54:35 -090 ", "%b %d %Y %H:%M:%S %#z ").is_err());
    // bad timezone data (partial minutes) mid-string
    assert!(parse("Aug 09 2013 -090 23:54:35", "%b %d %Y %#z %H:%M:%S").is_err());
    // bad timezone data
    assert!(parse("Aug 09 2013 -09:00:00 23:54:35", "%b %d %Y %#z %H:%M:%S").is_err());
    // timezone data ambiguous with hours
    assert!(parse("Aug 09 2013 -09:00:23:54:35", "%b %d %Y %#z%H:%M:%S").is_err());
}

#[test]
fn test_to_string_round_trip() {
    let dt = Utc.with_ymd_and_hms(2000, 1, 1, 0, 0, 0).unwrap();
    let _dt: DateTime<Utc> = dt.to_string().parse().unwrap();

    let ndt_fixed = dt.with_timezone(&FixedOffset::east_opt(3600).unwrap());
    let _dt: DateTime<FixedOffset> = ndt_fixed.to_string().parse().unwrap();

    let ndt_fixed = dt.with_timezone(&FixedOffset::east_opt(0).unwrap());
    let _dt: DateTime<FixedOffset> = ndt_fixed.to_string().parse().unwrap();
}

#[test]
#[cfg(feature = "clock")]
fn test_to_string_round_trip_with_local() {
    let ndt = Local::now();
    let _dt: DateTime<FixedOffset> = ndt.to_string().parse().unwrap();
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_format_with_local() {
    // if we are not around the year boundary, local and UTC date should have the same year
    let dt = Local::now().with_month(5).unwrap();
    assert_eq!(dt.format("%Y").to_string(), dt.with_timezone(&Utc).format("%Y").to_string());
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_is_copy() {
    // UTC is known to be `Copy`.
    let a = Utc::now();
    let b = a;
    assert_eq!(a, b);
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_is_send() {
    use std::thread;

    // UTC is known to be `Send`.
    let a = Utc::now();
    thread::spawn(move || {
        let _ = a;
    })
    .join()
    .unwrap();
}

#[test]
fn test_subsecond_part() {
    let datetime = Utc
        .from_local_datetime(
            &NaiveDate::from_ymd_opt(2014, 7, 8)
                .unwrap()
                .and_hms_nano_opt(9, 10, 11, 1234567)
                .unwrap(),
        )
        .unwrap();

    assert_eq!(1, datetime.timestamp_subsec_millis());
    assert_eq!(1234, datetime.timestamp_subsec_micros());
    assert_eq!(1234567, datetime.timestamp_subsec_nanos());
}

#[test]
#[cfg(not(target_os = "windows"))]
fn test_from_system_time() {
    use std::time::Duration;

    let epoch = Utc.with_ymd_and_hms(1970, 1, 1, 0, 0, 0).unwrap();
    let nanos = 999_999_999;

    // SystemTime -> DateTime<Utc>
    assert_eq!(DateTime::<Utc>::from(UNIX_EPOCH), epoch);
    assert_eq!(
        DateTime::<Utc>::from(UNIX_EPOCH + Duration::new(999_999_999, nanos)),
        Utc.from_local_datetime(
            &NaiveDate::from_ymd_opt(2001, 9, 9)
                .unwrap()
                .and_hms_nano_opt(1, 46, 39, nanos)
                .unwrap()
        )
        .unwrap()
    );
    assert_eq!(
        DateTime::<Utc>::from(UNIX_EPOCH - Duration::new(999_999_999, nanos)),
        Utc.from_local_datetime(
            &NaiveDate::from_ymd_opt(1938, 4, 24).unwrap().and_hms_nano_opt(22, 13, 20, 1).unwrap()
        )
        .unwrap()
    );

    // DateTime<Utc> -> SystemTime
    assert_eq!(SystemTime::from(epoch), UNIX_EPOCH);
    assert_eq!(
        SystemTime::from(
            Utc.from_local_datetime(
                &NaiveDate::from_ymd_opt(2001, 9, 9)
                    .unwrap()
                    .and_hms_nano_opt(1, 46, 39, nanos)
                    .unwrap()
            )
            .unwrap()
        ),
        UNIX_EPOCH + Duration::new(999_999_999, nanos)
    );
    assert_eq!(
        SystemTime::from(
            Utc.from_local_datetime(
                &NaiveDate::from_ymd_opt(1938, 4, 24)
                    .unwrap()
                    .and_hms_nano_opt(22, 13, 20, 1)
                    .unwrap()
            )
            .unwrap()
        ),
        UNIX_EPOCH - Duration::new(999_999_999, 999_999_999)
    );

    // DateTime<any tz> -> SystemTime (via `with_timezone`)
    #[cfg(feature = "clock")]
    {
        assert_eq!(SystemTime::from(epoch.with_timezone(&Local)), UNIX_EPOCH);
    }
    assert_eq!(
        SystemTime::from(epoch.with_timezone(&FixedOffset::east_opt(32400).unwrap())),
        UNIX_EPOCH
    );
    assert_eq!(
        SystemTime::from(epoch.with_timezone(&FixedOffset::west_opt(28800).unwrap())),
        UNIX_EPOCH
    );
}

#[test]
#[cfg(target_os = "windows")]
fn test_from_system_time() {
    use std::time::Duration;

    let nanos = 999_999_000;

    let epoch = Utc.with_ymd_and_hms(1970, 1, 1, 0, 0, 0).unwrap();

    // SystemTime -> DateTime<Utc>
    assert_eq!(DateTime::<Utc>::from(UNIX_EPOCH), epoch);
    assert_eq!(
        DateTime::<Utc>::from(UNIX_EPOCH + Duration::new(999_999_999, nanos)),
        Utc.from_local_datetime(
            &NaiveDate::from_ymd_opt(2001, 9, 9)
                .unwrap()
                .and_hms_nano_opt(1, 46, 39, nanos)
                .unwrap()
        )
        .unwrap()
    );
    assert_eq!(
        DateTime::<Utc>::from(UNIX_EPOCH - Duration::new(999_999_999, nanos)),
        Utc.from_local_datetime(
            &NaiveDate::from_ymd_opt(1938, 4, 24)
                .unwrap()
                .and_hms_nano_opt(22, 13, 20, 1_000)
                .unwrap()
        )
        .unwrap()
    );

    // DateTime<Utc> -> SystemTime
    assert_eq!(SystemTime::from(epoch), UNIX_EPOCH);
    assert_eq!(
        SystemTime::from(
            Utc.from_local_datetime(
                &NaiveDate::from_ymd_opt(2001, 9, 9)
                    .unwrap()
                    .and_hms_nano_opt(1, 46, 39, nanos)
                    .unwrap()
            )
            .unwrap()
        ),
        UNIX_EPOCH + Duration::new(999_999_999, nanos)
    );
    assert_eq!(
        SystemTime::from(
            Utc.from_local_datetime(
                &NaiveDate::from_ymd_opt(1938, 4, 24)
                    .unwrap()
                    .and_hms_nano_opt(22, 13, 20, 1_000)
                    .unwrap()
            )
            .unwrap()
        ),
        UNIX_EPOCH - Duration::new(999_999_999, nanos)
    );

    // DateTime<any tz> -> SystemTime (via `with_timezone`)
    #[cfg(feature = "clock")]
    {
        assert_eq!(SystemTime::from(epoch.with_timezone(&Local)), UNIX_EPOCH);
    }
    assert_eq!(
        SystemTime::from(epoch.with_timezone(&FixedOffset::east_opt(32400).unwrap())),
        UNIX_EPOCH
    );
    assert_eq!(
        SystemTime::from(epoch.with_timezone(&FixedOffset::west_opt(28800).unwrap())),
        UNIX_EPOCH
    );
}

#[test]
fn test_datetime_format_alignment() {
    let datetime = Utc.with_ymd_and_hms(2007, 1, 2, 0, 0, 0).unwrap();

    // Item::Literal
    let percent = datetime.format("%%");
    assert_eq!("  %", format!("{:>3}", percent));
    assert_eq!("%  ", format!("{:<3}", percent));
    assert_eq!(" % ", format!("{:^3}", percent));

    // Item::Numeric
    let year = datetime.format("%Y");
    assert_eq!("  2007", format!("{:>6}", year));
    assert_eq!("2007  ", format!("{:<6}", year));
    assert_eq!(" 2007 ", format!("{:^6}", year));

    // Item::Fixed
    let tz = datetime.format("%Z");
    assert_eq!("  UTC", format!("{:>5}", tz));
    assert_eq!("UTC  ", format!("{:<5}", tz));
    assert_eq!(" UTC ", format!("{:^5}", tz));

    // [Item::Numeric, Item::Space, Item::Literal, Item::Space, Item::Numeric]
    let ymd = datetime.format("%Y %B %d");
    let ymd_formatted = "2007 January 02";
    assert_eq!(format!("  {}", ymd_formatted), format!("{:>17}", ymd));
    assert_eq!(format!("{}  ", ymd_formatted), format!("{:<17}", ymd));
    assert_eq!(format!(" {} ", ymd_formatted), format!("{:^17}", ymd));
}

#[test]
fn test_datetime_from_local() {
    // 2000-01-12T02:00:00Z
    let naivedatetime_utc =
        NaiveDate::from_ymd_opt(2000, 1, 12).unwrap().and_hms_opt(2, 0, 0).unwrap();
    let datetime_utc = DateTime::<Utc>::from_utc(naivedatetime_utc, Utc);

    // 2000-01-12T10:00:00+8:00:00
    let timezone_east = FixedOffset::east_opt(8 * 60 * 60).unwrap();
    let naivedatetime_east =
        NaiveDate::from_ymd_opt(2000, 1, 12).unwrap().and_hms_opt(10, 0, 0).unwrap();
    let datetime_east = DateTime::<FixedOffset>::from_local(naivedatetime_east, timezone_east);

    // 2000-01-11T19:00:00-7:00:00
    let timezone_west = FixedOffset::west_opt(7 * 60 * 60).unwrap();
    let naivedatetime_west =
        NaiveDate::from_ymd_opt(2000, 1, 11).unwrap().and_hms_opt(19, 0, 0).unwrap();
    let datetime_west = DateTime::<FixedOffset>::from_local(naivedatetime_west, timezone_west);

    assert_eq!(datetime_east, datetime_utc.with_timezone(&timezone_east));
    assert_eq!(datetime_west, datetime_utc.with_timezone(&timezone_west));
}

#[test]
#[cfg(feature = "clock")]
fn test_years_elapsed() {
    const WEEKS_PER_YEAR: f32 = 52.1775;

    // This is always at least one year because 1 year = 52.1775 weeks.
    let one_year_ago =
        Utc::now().date_naive() - Duration::weeks((WEEKS_PER_YEAR * 1.5).ceil() as i64);
    // A bit more than 2 years.
    let two_year_ago =
        Utc::now().date_naive() - Duration::weeks((WEEKS_PER_YEAR * 2.5).ceil() as i64);

    assert_eq!(Utc::now().date_naive().years_since(one_year_ago), Some(1));
    assert_eq!(Utc::now().date_naive().years_since(two_year_ago), Some(2));

    // If the given DateTime is later than now, the function will always return 0.
    let future = Utc::now().date_naive() + Duration::weeks(12);
    assert_eq!(Utc::now().date_naive().years_since(future), None);
}

#[test]
fn test_datetime_add_assign() {
    let naivedatetime = NaiveDate::from_ymd_opt(2000, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();
    let datetime = DateTime::<Utc>::from_utc(naivedatetime, Utc);
    let mut datetime_add = datetime;

    datetime_add += Duration::seconds(60);
    assert_eq!(datetime_add, datetime + Duration::seconds(60));

    let timezone = FixedOffset::east_opt(60 * 60).unwrap();
    let datetime = datetime.with_timezone(&timezone);
    let datetime_add = datetime_add.with_timezone(&timezone);

    assert_eq!(datetime_add, datetime + Duration::seconds(60));

    let timezone = FixedOffset::west_opt(2 * 60 * 60).unwrap();
    let datetime = datetime.with_timezone(&timezone);
    let datetime_add = datetime_add.with_timezone(&timezone);

    assert_eq!(datetime_add, datetime + Duration::seconds(60));
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_add_assign_local() {
    let naivedatetime = NaiveDate::from_ymd_opt(2022, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();

    let datetime = Local.from_utc_datetime(&naivedatetime);
    let mut datetime_add = Local.from_utc_datetime(&naivedatetime);

    // ensure we cross a DST transition
    for i in 1..=365 {
        datetime_add += Duration::days(1);
        assert_eq!(datetime_add, datetime + Duration::days(i))
    }
}

#[test]
fn test_datetime_sub_assign() {
    let naivedatetime = NaiveDate::from_ymd_opt(2000, 1, 1).unwrap().and_hms_opt(12, 0, 0).unwrap();
    let datetime = DateTime::<Utc>::from_utc(naivedatetime, Utc);
    let mut datetime_sub = datetime;

    datetime_sub -= Duration::minutes(90);
    assert_eq!(datetime_sub, datetime - Duration::minutes(90));

    let timezone = FixedOffset::east_opt(60 * 60).unwrap();
    let datetime = datetime.with_timezone(&timezone);
    let datetime_sub = datetime_sub.with_timezone(&timezone);

    assert_eq!(datetime_sub, datetime - Duration::minutes(90));

    let timezone = FixedOffset::west_opt(2 * 60 * 60).unwrap();
    let datetime = datetime.with_timezone(&timezone);
    let datetime_sub = datetime_sub.with_timezone(&timezone);

    assert_eq!(datetime_sub, datetime - Duration::minutes(90));
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_sub_assign_local() {
    let naivedatetime = NaiveDate::from_ymd_opt(2022, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();

    let datetime = Local.from_utc_datetime(&naivedatetime);
    let mut datetime_sub = Local.from_utc_datetime(&naivedatetime);

    // ensure we cross a DST transition
    for i in 1..=365 {
        datetime_sub -= Duration::days(1);
        assert_eq!(datetime_sub, datetime - Duration::days(i))
    }
}

#[test]
#[cfg(all(target_os = "windows", feature = "clock"))]
fn test_from_naive_date_time_windows() {
    let min_year = NaiveDate::from_ymd_opt(1601, 1, 3).unwrap().and_hms_opt(0, 0, 0).unwrap();

    let max_year = NaiveDate::from_ymd_opt(30827, 12, 29).unwrap().and_hms_opt(23, 59, 59).unwrap();

    let too_low_year =
        NaiveDate::from_ymd_opt(1600, 12, 29).unwrap().and_hms_opt(23, 59, 59).unwrap();

    let too_high_year = NaiveDate::from_ymd_opt(30829, 1, 3).unwrap().and_hms_opt(0, 0, 0).unwrap();

    let _ = Local.from_utc_datetime(&min_year);
    let _ = Local.from_utc_datetime(&max_year);

    let _ = Local.from_local_datetime(&min_year);
    let _ = Local.from_local_datetime(&max_year);

    let local_too_low = Local.from_local_datetime(&too_low_year);
    let local_too_high = Local.from_local_datetime(&too_high_year);

    assert_eq!(local_too_low, LocalResult::None);
    assert_eq!(local_too_high, LocalResult::None);

    let err = std::panic::catch_unwind(|| {
        Local.from_utc_datetime(&too_low_year);
    });
    assert!(err.is_err());

    let err = std::panic::catch_unwind(|| {
        Local.from_utc_datetime(&too_high_year);
    });
    assert!(err.is_err());
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_local_from_preserves_offset() {
    let naivedatetime = NaiveDate::from_ymd_opt(2023, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();

    let datetime = Local.from_utc_datetime(&naivedatetime);
    let offset = datetime.offset().fix();

    let datetime_fixed: DateTime<FixedOffset> = datetime.into();
    assert_eq!(&offset, datetime_fixed.offset());
    assert_eq!(datetime.fixed_offset(), datetime_fixed);
}

#[test]
fn test_datetime_fixed_offset() {
    let naivedatetime = NaiveDate::from_ymd_opt(2023, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();

    let datetime = Utc.from_utc_datetime(&naivedatetime);
    let fixed_utc = FixedOffset::east_opt(0).unwrap();
    assert_eq!(datetime.fixed_offset(), fixed_utc.from_local_datetime(&naivedatetime).unwrap());

    let fixed_offset = FixedOffset::east_opt(3600).unwrap();
    let datetime_fixed = fixed_offset.from_local_datetime(&naivedatetime).unwrap();
    assert_eq!(datetime_fixed.fixed_offset(), datetime_fixed);
}
