use crate::NaiveDateTime;
use core_foundation::date::{kCFAbsoluteTimeIntervalSince1970, CFDate};

impl From<CFDate> for NaiveDateTime {
    fn from(d: CFDate) -> NaiveDateTime {
        naive_utc(d)
    }
}

/// Convert a `CFDate` into a `NaiveDateTime`
pub fn naive_utc(date: CFDate) -> NaiveDateTime {
    let ts = unsafe { date.abs_time() + kCFAbsoluteTimeIntervalSince1970 };
    let (secs, nanos) = if ts.is_sign_positive() {
        (ts.trunc() as i64, ts.fract())
    } else {
        // nanoseconds can't be negative in NaiveDateTime
        (ts.trunc() as i64 - 1, 1.0 - ts.fract().abs())
    };
    NaiveDateTime::from_timestamp(secs, (nanos * 1e9).floor() as u32)
}

impl From<NaiveDateTime> for CFDate {
    fn from(d: NaiveDateTime) -> CFDate {
        from_naive_utc(d)
    }
}

/// Convert a `NaiveDateTime` into a `CFDate`
pub fn from_naive_utc(time: NaiveDateTime) -> CFDate {
    let secs = time.timestamp();
    let nanos = time.timestamp_subsec_nanos();
    let ts = unsafe { secs as f64 + (nanos as f64 / 1e9) - kCFAbsoluteTimeIntervalSince1970 };
    CFDate::new(ts)
}

#[cfg(test)]
mod test {
    use super::*;

    fn approx_eq(a: f64, b: f64) -> bool {
        use std::f64;

        let same_sign = a.is_sign_positive() == b.is_sign_positive();
        let equal = ((a - b).abs() / f64::min(a.abs() + b.abs(), f64::MAX)) < f64::EPSILON;
        same_sign && equal
    }

    #[test]
    fn date_chrono_conversion_positive() {
        let date = CFDate::now();
        let datetime = naive_utc(date.clone());
        let converted = from_naive_utc(datetime);
        assert!(approx_eq(date.abs_time(), converted.abs_time()));
    }

    #[test]
    fn date_chrono_conversion_negative() {
        let ts = unsafe { kCFAbsoluteTimeIntervalSince1970 - 420.0 };
        let date = CFDate::new(ts);
        let datetime: NaiveDateTime = naive_utc(date.clone());
        let converted = from_naive_utc(datetime);
        assert!(approx_eq(date.abs_time(), converted.abs_time()));
    }
}
