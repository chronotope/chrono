use std::time::{SystemTime, UNIX_EPOCH};

use super::DateTime;
#[cfg(feature = "clock")]
use crate::offset::Local;
use crate::offset::{FixedOffset, TimeZone, Utc};
#[cfg(feature = "clock")]
use crate::Datelike;
use crate::{
    naive::{NaiveDate, NaiveTime},
    TimeDelta,
};
use crate::{Days, LocalResult, Months, NaiveDateTime};

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
    ) -> Result<crate::LocalResult<Self::Offset>, Error> {
        let local_to_winter_transition_start = NaiveDate::from_ymd(
            local.year(),
            DstTester::TO_WINTER_MONTH_DAY.0,
            DstTester::TO_WINTER_MONTH_DAY.1,
        )?
        .and_time(DstTester::transition_start_local());

        let local_to_winter_transition_end = NaiveDate::from_ymd(
            local.year(),
            DstTester::TO_WINTER_MONTH_DAY.0,
            DstTester::TO_WINTER_MONTH_DAY.1,
        )?
        .and_time(DstTester::transition_start_local() - TimeDelta::hours(1));

        let local_to_summer_transition_start = NaiveDate::from_ymd(
            local.year(),
            DstTester::TO_SUMMER_MONTH_DAY.0,
            DstTester::TO_SUMMER_MONTH_DAY.1,
        )?
        .and_time(DstTester::transition_start_local());

        let local_to_summer_transition_end = NaiveDate::from_ymd(
            local.year(),
            DstTester::TO_SUMMER_MONTH_DAY.0,
            DstTester::TO_SUMMER_MONTH_DAY.1,
        )?
        .and_time(DstTester::transition_start_local() + TimeDelta::hours(1));

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
fn test_datetime_add_days() -> Result<(), Error> {
    let est = FixedOffset::west(5 * 60 * 60)?;
    let kst = FixedOffset::east(9 * 60 * 60)?;

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
    Ok(())
}

#[test]
fn test_datetime_sub_days() -> Result<(), Error> {
    let est = FixedOffset::west(5 * 60 * 60).unwrap();
    let kst = FixedOffset::east(9 * 60 * 60).unwrap();

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
    Ok(())
}

#[test]
fn test_datetime_add_months() -> Result<(), Error> {
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
    Ok(())
}

#[test]
fn test_datetime_sub_months() -> Result<(), Error> {
    let est = FixedOffset::west(5 * 60 * 60)?;
    let kst = FixedOffset::east(9 * 60 * 60)?;

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
    Ok(())
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
) -> Result<DateTime<FixedOffset>, Error> {
    fixedoffset.with_ymd_and_hms(year, month, day, hour, min, sec)
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
) -> Result<DateTime<FixedOffset>, Error> {
    fixedoffset
        .with_ymd_and_hms(year, month, day, hour, min, sec)?
        .checked_add_signed(TimeDelta::milliseconds(milli))?
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
) -> Result<DateTime<FixedOffset>, Error> {
    fixedoffset
        .with_ymd_and_hms(year, month, day, hour, min, sec)?
        .checked_add_signed(TimeDelta::microseconds(micro))?
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
) -> Result<DateTime<FixedOffset>, Error> {
    fixedoffset
        .with_ymd_and_hms(year, month, day, hour, min, sec)?
        .checked_add_signed(TimeDelta::nanoseconds(nano))?
}

// local helper function to easily create a DateTime<Utc>
fn ymdhms_utc(year: i32, month: u32, day: u32, hour: u32, min: u32, sec: u32) -> Result<DateTime<Utc>, Error> {
    Utc.with_ymd_and_hms(year, month, day, hour, min, sec)?
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
) -> Result<DateTime<Utc>, Error> {
    Utc.with_ymd_and_hms(year, month, day, hour, min, sec)?
        .checked_add_signed(TimeDelta::milliseconds(milli))?
}

#[test]
fn test_datetime_offset() -> Result<(), Error> {
    let est = FixedOffset::west(5 * 60 * 60)?;
    let edt = FixedOffset::west(4 * 60 * 60)?;
    let kst = FixedOffset::east(9 * 60 * 60)?;

    assert_eq!(
        format!("{}", Utc.with_ymd_and_hms(2014, 5, 6, 7, 8, 9)?),
        "2014-05-06 07:08:09 UTC"
    );
    assert_eq!(
        format!("{}", edt.with_ymd_and_hms(2014, 5, 6, 7, 8, 9)?),
        "2014-05-06 07:08:09 -04:00"
    );
    assert_eq!(
        format!("{}", kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9)?),
        "2014-05-06 07:08:09 +09:00"
    );
    assert_eq!(
        format!("{:?}", Utc.with_ymd_and_hms(2014, 5, 6, 7, 8, 9)?),
        "2014-05-06T07:08:09Z"
    );
    assert_eq!(
        format!("{:?}", edt.with_ymd_and_hms(2014, 5, 6, 7, 8, 9)?),
        "2014-05-06T07:08:09-04:00"
    );
    assert_eq!(
        format!("{:?}", kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9)?),
        "2014-05-06T07:08:09+09:00"
    );

    // edge cases
    assert_eq!(
        format!("{:?}", Utc.with_ymd_and_hms(2014, 5, 6, 0, 0, 0)?),
        "2014-05-06T00:00:00Z"
    );
    assert_eq!(
        format!("{:?}", edt.with_ymd_and_hms(2014, 5, 6, 0, 0, 0)?),
        "2014-05-06T00:00:00-04:00"
    );
    assert_eq!(
        format!("{:?}", kst.with_ymd_and_hms(2014, 5, 6, 0, 0, 0)?),
        "2014-05-06T00:00:00+09:00"
    );
    assert_eq!(
        format!("{:?}", Utc.with_ymd_and_hms(2014, 5, 6, 23, 59, 59)?),
        "2014-05-06T23:59:59Z"
    );
    assert_eq!(
        format!("{:?}", edt.with_ymd_and_hms(2014, 5, 6, 23, 59, 59)?),
        "2014-05-06T23:59:59-04:00"
    );
    assert_eq!(
        format!("{:?}", kst.with_ymd_and_hms(2014, 5, 6, 23, 59, 59)?),
        "2014-05-06T23:59:59+09:00"
    );

    let dt = Utc.with_ymd_and_hms(2014, 5, 6, 7, 8, 9)?;
    assert_eq!(dt, edt.with_ymd_and_hms(2014, 5, 6, 3, 8, 9)?);
    assert_eq!(
        dt + TimeDelta::seconds(3600 + 60 + 1),
        Utc.with_ymd_and_hms(2014, 5, 6, 8, 9, 10)?
    );
    assert_eq!(
        dt.signed_duration_since(edt.ymd(2014, 5, 6).unwrap().and_hms(10, 11, 12).unwrap()),
        TimeDelta::seconds(-7 * 3600 - 3 * 60 - 3)
    );

    assert_eq!(*Utc.ymd(2014, 5, 6).unwrap().and_hms(7, 8, 9).unwrap().offset(), Utc);
    assert_eq!(*edt.ymd(2014, 5, 6).unwrap().and_hms(7, 8, 9).unwrap().offset(), edt);
    assert!(*edt.ymd(2014, 5, 6).unwrap().and_hms(7, 8, 9).unwrap().offset() != est);
}

#[test]
fn test_datetime_date_and_time() {
    let tz = FixedOffset::east(5 * 60 * 60).unwrap();
    let d = tz.ymd(2014, 5, 6).unwrap().and_hms(7, 8, 9).unwrap();
    assert_eq!(d.time(), NaiveTime::from_hms(7, 8, 9).unwrap());
    assert_eq!(d.date(), tz.ymd(2014, 5, 6).unwrap().unwrap());
    assert_eq!(d.date().naive_local(), ymd!(2014, 5, 6));
    assert_eq!(d.date().and_time(d.time()), Ok(d));

    let tz = FixedOffset::east(4 * 60 * 60).unwrap();
    let d = tz.ymd(2016, 5, 4).unwrap().and_hms(3, 2, 1).unwrap();
    assert_eq!(d.time(), NaiveTime::from_hms(3, 2, 1).unwrap());
    assert_eq!(d.date(), tz.ymd(2016, 5, 4).unwrap().unwrap());
    assert_eq!(d.date().naive_local(), ymd!(2016, 5, 4));
    assert_eq!(d.date().and_time(d.time()), Ok(d));

    let tz = FixedOffset::west(13 * 60 * 60).unwrap();
    let d = tz.ymd(2017, 8, 9).unwrap().and_hms(12, 34, 56).unwrap();
    assert_eq!(d.time(), NaiveTime::from_hms(12, 34, 56).unwrap());
    assert_eq!(d.date(), tz.ymd(2017, 8, 9).unwrap().unwrap());
    assert_eq!(d.date().naive_local(), ymd!(2017, 8, 9));
    assert_eq!(d.date().and_time(d.time()), Ok(d));

    let utc_d = Utc.ymd(2017, 8, 9).unwrap().and_hms(12, 34, 56).unwrap();
    assert!(utc_d < d);
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_with_timezone() -> Result<(), Error> {
    let local_now = Local::now()?;
    let utc_now = local_now.with_timezone(&Utc)?;
    let local_now2 = utc_now.with_timezone(&Local)?;
    assert_eq!(local_now, local_now2);
    Ok(())
}

#[test]
fn test_datetime_rfc2822_and_rfc3339() -> Result<(), Error> {
    let edt = FixedOffset::east(5 * 60 * 60)?;
    assert_eq!(
        Utc.with_ymd_and_hms(2015, 2, 18, 23, 16, 9)?.to_rfc2822(),
        "Wed, 18 Feb 2015 23:16:09 +0000"
    );
    assert_eq!(
        Utc.with_ymd_and_hms(2015, 2, 18, 23, 16, 9)?.to_rfc3339(),
        "2015-02-18T23:16:09+00:00"
    );
    assert_eq!(
        edt.ymd(2015, 2, 18).unwrap().and_hms_milli(23, 16, 9, 150).unwrap().to_rfc2822(),
        "Wed, 18 Feb 2015 23:16:09 +0500"
    );
    assert_eq!(
        edt.ymd(2015, 2, 18).unwrap().and_hms_milli(23, 16, 9, 150).unwrap().to_rfc3339(),
        "2015-02-18T23:16:09.150+05:00"
    );
    assert_eq!(
        edt.ymd(2015, 2, 18).unwrap().and_hms_micro(23, 59, 59, 1_234_567).unwrap().to_rfc2822(),
        "Wed, 18 Feb 2015 23:59:60 +0500"
    );
    assert_eq!(
        edt.ymd(2015, 2, 18).unwrap().and_hms_micro(23, 59, 59, 1_234_567).unwrap().to_rfc3339(),
        "2015-02-18T23:59:60.234567+05:00"
    );

    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc2822("Wed, 18 Feb 2015 23:16:09 +0000"),
        Ok(FixedOffset::east(0).unwrap().ymd(2015, 2, 18).unwrap().and_hms(23, 16, 9).unwrap())
    );
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc2822("Wed, 18 Feb 2015 23:16:09 -0000"),
        Ok(FixedOffset::east(0).unwrap().ymd(2015, 2, 18).unwrap().and_hms(23, 16, 9).unwrap())
    );
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:16:09Z"),
        Ok(FixedOffset::east(0).unwrap().ymd(2015, 2, 18).unwrap().and_hms(23, 16, 9).?)
    );
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc2822("Wed, 18 Feb 2015 23:59:60 +0500"),
        Ok(edt.ymd(2015, 2, 18).unwrap().and_hms_milli(23, 59, 59, 1_000)?)
    );
    assert!(DateTime::<FixedOffset>::parse_from_rfc2822("31 DEC 262143 23:59 -2359").is_err());
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_rfc3339("2015-02-18T23:59:60.234567+05:00"),
        Ok(edt.ymd(2015, 2, 18).unwrap().and_hms_micro(23, 59, 59, 1_234_567)?)
    );
    Ok(())
}

#[test]
fn test_rfc3339_opts() {
    use crate::SecondsFormat::*;
    let pst = FixedOffset::east(8 * 60 * 60).unwrap();
    let dt = pst.ymd(2018, 1, 11).unwrap().and_hms_nano(10, 5, 13, 84_660_000).unwrap();
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
    let dt = Utc.ymd(1999, 10, 9).unwrap().and_hms(1, 2, 3).unwrap();
    dt.to_rfc3339_opts(SecondsFormat::__NonExhaustive, true);
}

#[test]
fn test_datetime_from_str() {
    assert_eq!(
        "2015-02-18T23:16:9.15Z".parse::<DateTime<FixedOffset>>(),
        Ok(FixedOffset::east(0)
            .unwrap()
            .ymd(2015, 2, 18)
            .unwrap()
            .and_hms_milli(23, 16, 9, 150)
            .unwrap())
    );
    assert_eq!(
        "2015-02-18T23:16:9.15Z".parse::<DateTime<Utc>>(),
        Ok(Utc.ymd(2015, 2, 18).unwrap().and_hms_milli(23, 16, 9, 150).unwrap())
    );
    assert_eq!(
        "2015-02-18T23:16:9.15 UTC".parse::<DateTime<Utc>>(),
        Ok(Utc.ymd(2015, 2, 18).unwrap().and_hms_milli(23, 16, 9, 150).unwrap())
    );
    assert_eq!(
        "2015-02-18T23:16:9.15UTC".parse::<DateTime<Utc>>(),
        Ok(Utc.ymd(2015, 2, 18).unwrap().and_hms_milli(23, 16, 9, 150).unwrap())
    );

    assert_eq!(
        "2015-2-18T23:16:9.15Z".parse::<DateTime<FixedOffset>>(),
        Ok(FixedOffset::east(0)
            .unwrap()
            .ymd(2015, 2, 18)
            .unwrap()
            .and_hms_milli(23, 16, 9, 150)
            .unwrap())
    );
    assert_eq!(
        "2015-2-18T13:16:9.15-10:00".parse::<DateTime<FixedOffset>>(),
        Ok(FixedOffset::west(10 * 3600)
            .unwrap()
            .ymd(2015, 2, 18)
            .unwrap()
            .and_hms_milli(13, 16, 9, 150)
            .unwrap())
    );
    assert!("2015-2-18T23:16:9.15".parse::<DateTime<FixedOffset>>().is_err());

    assert_eq!(
        "2015-2-18T23:16:9.15Z".parse::<DateTime<Utc>>(),
        Ok(Utc.ymd(2015, 2, 18).unwrap().and_hms_milli(23, 16, 9, 150).unwrap())
    );
    assert_eq!(
        "2015-2-18T13:16:9.15-10:00".parse::<DateTime<Utc>>(),
        Ok(Utc.ymd(2015, 2, 18).unwrap().and_hms_milli(23, 16, 9, 150).unwrap())
    );
    assert!("2015-2-18T23:16:9.15".parse::<DateTime<Utc>>().is_err());

    // no test for `DateTime<Local>`, we cannot verify that much.
}

#[test]
fn test_datetime_parse_from_str() {
    let ymdhms = |y, m, d, h, n, s, off| {
        FixedOffset::east(off).unwrap().ymd(y, m, d).unwrap().and_hms(h, n, s).unwrap()
    };
    assert_eq!(
        DateTime::<FixedOffset>::parse_from_str("2014-5-7T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z"),
        Ok(ymdhms(2014, 5, 7, 12, 34, 56, 570 * 60))
    ); // ignore offset
    assert!(DateTime::<FixedOffset>::parse_from_str("20140507000000", "%Y%m%d%H%M%S").is_err()); // no offset
    assert!(DateTime::<FixedOffset>::parse_from_str(
        "Fri, 09 Aug 2013 23:54:35 GMT",
        "%a, %d %b %Y %H:%M:%S GMT"
    )
    .is_err());
    assert_eq!(
        Utc.datetime_from_str("Fri, 09 Aug 2013 23:54:35 GMT", "%a, %d %b %Y %H:%M:%S GMT"),
        Ok(Utc.ymd(2013, 8, 9).unwrap().and_hms(23, 54, 35).unwrap())
    );
    // bad timezone data
    assert!(DateTime::<FixedOffset>::parse_from_str(
        "Aug 09 2013 23:54:35 -09:00:00",
        "%b %d %Y %H:%M:%S %#z"
    )
    .is_err());
    // bad timezone data (partial minutes)
    assert!(DateTime::<FixedOffset>::parse_from_str(
        "Aug 09 2013 23:54:35 -090",
        "%b %d %Y %H:%M:%S %#z"
    )
    .is_err());
    // bad timezone data (partial minutes) with trailing space
    assert!(DateTime::<FixedOffset>::parse_from_str(
        "Aug 09 2013 23:54:35 -090 ",
        "%b %d %Y %H:%M:%S %#z "
    )
    .is_err());
    // bad timezone data (partial minutes) mid-string
    assert!(DateTime::<FixedOffset>::parse_from_str(
        "Aug 09 2013 -090 23:54:35",
        "%b %d %Y %#z %H:%M:%S"
    )
    .is_err());
    // bad timezone data
    assert!(DateTime::<FixedOffset>::parse_from_str(
        "Aug 09 2013 -09:00:00 23:54:35",
        "%b %d %Y %#z %H:%M:%S"
    )
    .is_err());
    // timezone data ambiguous with hours
    assert!(DateTime::<FixedOffset>::parse_from_str(
        "Aug 09 2013 -09:00:23:54:35",
        "%b %d %Y %#z%H:%M:%S"
    )
    .is_err());
}

#[test]
fn test_to_string_round_trip() {
    let dt = Utc.ymd(2000, 1, 1).unwrap().and_hms(0, 0, 0).unwrap();
    let _dt: DateTime<Utc> = dt.to_string().parse().unwrap();

    let ndt_fixed = dt.with_fixed_timezone(&FixedOffset::east(3600).unwrap());
    let _dt: DateTime<FixedOffset> = ndt_fixed.to_string().parse().unwrap();

    let ndt_fixed = dt.with_fixed_timezone(&FixedOffset::east(0).unwrap());
    let _dt: DateTime<FixedOffset> = ndt_fixed.to_string().parse().unwrap();
}

#[test]
#[cfg(feature = "clock")]
fn test_to_string_round_trip_with_local() {
    let ndt = Local::now().unwrap();
    let _dt: DateTime<FixedOffset> = ndt.to_string().parse().unwrap();
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_format_with_local() {
    // if we are not around the year boundary, local and UTC date should have the same year
    let dt = Local::now().unwrap().with_month(5).unwrap();
    assert_eq!(dt.format("%Y").to_string(), dt.with_fixed_timezone(&Utc).format("%Y").to_string());
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_is_copy() {
    // UTC is known to be `Copy`.
    let a = Utc::now().unwrap();
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
    let datetime = Utc.ymd(2014, 7, 8).unwrap().and_hms_nano(9, 10, 11, 1234567).unwrap();

    assert_eq!(1, datetime.timestamp_subsec_millis());
    assert_eq!(1234, datetime.timestamp_subsec_micros());
    assert_eq!(1234567, datetime.timestamp_subsec_nanos());
}

#[test]
#[cfg(not(target_os = "windows"))]
fn test_from_system_time() {
    use std::time::Duration;

    let epoch = Utc.ymd(1970, 1, 1).unwrap().and_hms(0, 0, 0).unwrap();
    let nanos = 999_999_999;

    // SystemTime -> DateTime<Utc>
    assert_eq!(DateTime::<Utc>::from(UNIX_EPOCH), epoch);
    assert_eq!(
        DateTime::<Utc>::from(UNIX_EPOCH + Duration::new(999_999_999, nanos)),
        Utc.ymd(2001, 9, 9).unwrap().and_hms_nano(1, 46, 39, nanos).unwrap()
    );
    assert_eq!(
        DateTime::<Utc>::from(UNIX_EPOCH - Duration::new(999_999_999, nanos)),
        Utc.ymd(1938, 4, 24).unwrap().and_hms_nano(22, 13, 20, 1).unwrap()
    );

    // DateTime<Utc> -> SystemTime
    assert_eq!(SystemTime::from(epoch), UNIX_EPOCH);
    assert_eq!(
        SystemTime::from(Utc.ymd(2001, 9, 9).unwrap().and_hms_nano(1, 46, 39, nanos).unwrap()),
        UNIX_EPOCH + Duration::new(999_999_999, nanos)
    );
    assert_eq!(
        SystemTime::from(Utc.ymd(1938, 4, 24).unwrap().and_hms_nano(22, 13, 20, 1).unwrap()),
        UNIX_EPOCH - Duration::new(999_999_999, 999_999_999)
    );

    // DateTime<any tz> -> SystemTime (via `with_timezone`)
    #[cfg(feature = "clock")]
    {
        assert_eq!(SystemTime::from(epoch.with_timezone(&Local).unwrap()), UNIX_EPOCH);
    }
    assert_eq!(
        SystemTime::from(epoch.with_fixed_timezone(&FixedOffset::east(32400).unwrap())),
        UNIX_EPOCH
    );
    assert_eq!(
        SystemTime::from(epoch.with_fixed_timezone(&FixedOffset::west(28800).unwrap())),
        UNIX_EPOCH
    );
}

#[test]
#[cfg(target_os = "windows")]
fn test_from_system_time() {
    use std::convert::TryFrom;
    use std::time::Duration;

    let nanos = 999_999_000;

    let epoch = Utc.ymd(1970, 1, 1).unwrap().and_hms(0, 0, 0).unwrap();

    // SystemTime -> DateTime<Utc>
    assert_eq!(DateTime::<Utc>::from(UNIX_EPOCH), epoch);
    assert_eq!(
        DateTime::<Utc>::from(UNIX_EPOCH + Duration::new(999_999_999, nanos)),
        Utc.ymd(2001, 9, 9).unwrap().and_hms_nano(1, 46, 39, nanos).unwrap()
    );
    assert_eq!(
        DateTime::<Utc>::from(UNIX_EPOCH - Duration::new(999_999_999, nanos)),
        Utc.ymd(1938, 4, 24).unwrap().and_hms_nano(22, 13, 20, 1_000).unwrap()
    );

    // DateTime<Utc> -> SystemTime
    assert_eq!(SystemTime::try_from(epoch).unwrap(), UNIX_EPOCH);
    assert_eq!(
        SystemTime::try_from(Utc.ymd(2001, 9, 9).unwrap().and_hms_nano(1, 46, 39, nanos).unwrap())
            .unwrap(),
        UNIX_EPOCH + Duration::new(999_999_999, nanos)
    );
    assert_eq!(
        SystemTime::try_from(
            Utc.ymd(1938, 4, 24).unwrap().and_hms_nano(22, 13, 20, 1_000).unwrap()
        )
        .unwrap(),
        UNIX_EPOCH - Duration::new(999_999_999, nanos)
    );

    // DateTime<any tz> -> SystemTime (via `with_timezone`)
    #[cfg(feature = "clock")]
    {
        assert_eq!(SystemTime::try_from(epoch.with_timezone(&Local).unwrap()).unwrap(), UNIX_EPOCH);
    }
    assert_eq!(
        SystemTime::try_from(epoch.with_fixed_timezone(&FixedOffset::east(32400).unwrap()))
            .unwrap(),
        UNIX_EPOCH
    );
    assert_eq!(
        SystemTime::try_from(epoch.with_fixed_timezone(&FixedOffset::west(28800).unwrap()))
            .unwrap(),
        UNIX_EPOCH
    );
}

#[test]
fn test_datetime_format_alignment() {
    let datetime = Utc.ymd(2007, 1, 2).unwrap().unwrap();

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
    let naivedatetime_utc = ymd!(2000, 1, 12).and_hms(2, 0, 0).unwrap();
    let datetime_utc = DateTime::<Utc>::from_utc(naivedatetime_utc, Utc);

    // 2000-01-12T10:00:00+8:00:00
    let timezone_east = FixedOffset::east(8 * 60 * 60).unwrap();
    let naivedatetime_east = ymd!(2000, 1, 12).and_hms(10, 0, 0).unwrap();
    let datetime_east = DateTime::<FixedOffset>::from_local(naivedatetime_east, timezone_east);

    // 2000-01-11T19:00:00-7:00:00
    let timezone_west = FixedOffset::west(7 * 60 * 60).unwrap();
    let naivedatetime_west = ymd!(2000, 1, 11).and_hms(19, 0, 0).unwrap();
    let datetime_west = DateTime::<FixedOffset>::from_local(naivedatetime_west, timezone_west);

    assert_eq!(datetime_east, datetime_utc.with_fixed_timezone(&timezone_east));
    assert_eq!(datetime_west, datetime_utc.with_fixed_timezone(&timezone_west));
}

#[test]
#[cfg(feature = "clock")]
fn test_years_elapsed() {
    const WEEKS_PER_YEAR: f32 = 52.1775;

    // This is always at least one year because 1 year = 52.1775 weeks.
    let one_year_ago =
        Utc::today().unwrap() - TimeDelta::weeks((WEEKS_PER_YEAR * 1.5).ceil() as i64);
    // A bit more than 2 years.
    let two_year_ago =
        Utc::today().unwrap() - TimeDelta::weeks((WEEKS_PER_YEAR * 2.5).ceil() as i64);

    assert_eq!(Utc::today().unwrap().years_since(one_year_ago), Some(1));
    assert_eq!(Utc::today().unwrap().years_since(two_year_ago), Some(2));

    // If the given DateTime is later than now, the function will always return 0.
    let future = Utc::today().unwrap() + TimeDelta::weeks(12);
    assert_eq!(Utc::today().unwrap().years_since(future), None);
}

#[test]
fn test_datetime_add_assign() {
    let naivedatetime = ymd!(2000, 1, 1).and_hms(0, 0, 0).unwrap();
    let datetime = DateTime::<Utc>::from_utc(naivedatetime, Utc);
    let mut datetime_add = datetime;

    datetime_add += TimeDelta::seconds(60);
    assert_eq!(datetime_add, datetime + TimeDelta::seconds(60));

    let timezone = FixedOffset::east(60 * 60).unwrap();
    let datetime = datetime.with_timezone(&timezone).unwrap();
    let datetime_add = datetime_add.with_timezone(&timezone).unwrap();

    assert_eq!(datetime_add, datetime + TimeDelta::seconds(60));

    let timezone = FixedOffset::west(2 * 60 * 60).unwrap();
    let datetime = datetime.with_timezone(&timezone).unwrap();
    let datetime_add = datetime_add.with_timezone(&timezone).unwrap();

    assert_eq!(datetime_add, datetime + TimeDelta::seconds(60));
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_add_assign_local() {
    let naivedatetime = ymd!(2022, 1, 1).and_hms(0, 0, 0).unwrap();

    let datetime = Local.from_utc_datetime(&naivedatetime).unwrap();
    let mut datetime_add = Local.from_utc_datetime(&naivedatetime).unwrap();

    // ensure we cross a DST transition
    for i in 1..=365 {
        datetime_add += TimeDelta::days(1);
        assert_eq!(datetime_add, datetime + TimeDelta::days(i))
    }
}

#[test]
fn test_datetime_sub_assign() {
    let naivedatetime = ymd!(2000, 1, 1).and_hms(12, 0, 0).unwrap();
    let datetime = DateTime::<Utc>::from_utc(naivedatetime, Utc);
    let mut datetime_sub = datetime;

    datetime_sub -= TimeDelta::minutes(90);
    assert_eq!(datetime_sub, datetime - TimeDelta::minutes(90));

    let timezone = FixedOffset::east(60 * 60).unwrap();
    let datetime = datetime.with_timezone(&timezone).unwrap();
    let datetime_sub = datetime_sub.with_timezone(&timezone).unwrap();

    assert_eq!(datetime_sub, datetime - TimeDelta::minutes(90));

    let timezone = FixedOffset::west(2 * 60 * 60).unwrap();
    let datetime = datetime.with_timezone(&timezone).unwrap();
    let datetime_sub = datetime_sub.with_timezone(&timezone).unwrap();

    assert_eq!(datetime_sub, datetime - TimeDelta::minutes(90));
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_sub_assign_local() {
    let naivedatetime = ymd!(2022, 1, 1).and_hms(0, 0, 0).unwrap();

    let datetime = Local.from_utc_datetime(&naivedatetime).unwrap();
    let mut datetime_sub = Local.from_utc_datetime(&naivedatetime).unwrap();

    // ensure we cross a DST transition
    for i in 1..=365 {
        datetime_sub -= TimeDelta::days(1);
        assert_eq!(datetime_sub, datetime - TimeDelta::days(i))
    }
}
