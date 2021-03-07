use crate::offset::{FixedOffset, Utc};
use crate::{DateTime, Datelike, NaiveDate, NaiveDateTime, NaiveTime, Offset, TimeZone, Timelike};
use pyo3::conversion::{FromPyObject, IntoPy, PyTryFrom, ToPyObject};
use pyo3::exceptions::PyTypeError;
use pyo3::types::{PyDateAccess, PyDateTime, PyTimeAccess, PyTzInfoAccess};

impl<Tz: TimeZone> ToPyObject for DateTime<Tz> {
    fn to_object(&self, py: pyo3::Python) -> pyo3::PyObject {
        let (date, time) = (self.datetime.date(), self.datetime.time());
        let mdf = date.mdf();
        let (yy, mm, dd) = (date.year(), mdf.month(), mdf.day());
        let (h, m, s) = time.hms();
        let ns = time.nanosecond();
        let (ms, fold) = match ns.checked_sub(1_000_000_000) {
            Some(ns) => (ns / 1000, true),
            None => (ns / 1000, false),
        };
        let tz = self.offset().fix().to_object(py);
        let datetime = PyDateTime::new_with_fold(
            py,
            yy,
            mm as u8,
            dd as u8,
            h as u8,
            m as u8,
            s as u8,
            ms,
            Some(&tz),
            fold,
        )
        .expect("Failed to construct datetime");
        datetime.into()
    }
}

impl<Tz: TimeZone> IntoPy<pyo3::PyObject> for DateTime<Tz> {
    fn into_py(self, py: pyo3::Python) -> pyo3::PyObject {
        ToPyObject::to_object(&self, py)
    }
}

impl FromPyObject<'_> for DateTime<FixedOffset> {
    fn extract(ob: &pyo3::PyAny) -> pyo3::PyResult<DateTime<FixedOffset>> {
        let dt = <PyDateTime as PyTryFrom>::try_from(ob)?;
        let ms = dt.get_fold() as u32 * 1_000_000 + dt.get_microsecond();
        let (h, m, s) = (dt.get_hour(), dt.get_minute(), dt.get_second());
        let tz = if let Some(tzinfo) = dt.get_tzinfo() {
            tzinfo.extract()?
        } else {
            return Err(PyTypeError::new_err("Not datetime.timezone.tzinfo"));
        };
        let dt = NaiveDateTime::new(
            NaiveDate::from_ymd(dt.get_year(), dt.get_month() as u32, dt.get_day() as u32),
            NaiveTime::from_hms_micro(h as u32, m as u32, s as u32, ms),
        );
        Ok(DateTime::from_utc(dt, tz))
    }
}

impl FromPyObject<'_> for DateTime<Utc> {
    fn extract(ob: &pyo3::PyAny) -> pyo3::PyResult<DateTime<Utc>> {
        let dt = <PyDateTime as PyTryFrom>::try_from(ob)?;
        let ms = dt.get_fold() as u32 * 1_000_000 + dt.get_microsecond();
        let (h, m, s) = (dt.get_hour(), dt.get_minute(), dt.get_second());
        let tz = if let Some(tzinfo) = dt.get_tzinfo() {
            tzinfo.extract()?
        } else {
            return Err(PyTypeError::new_err("Not datetime.timezone.utc"));
        };
        let dt = NaiveDateTime::new(
            NaiveDate::from_ymd(dt.get_year(), dt.get_month() as u32, dt.get_day() as u32),
            NaiveTime::from_hms_micro(h as u32, m as u32, s as u32, ms),
        );
        Ok(DateTime::from_utc(dt, tz))
    }
}

#[test]
fn test_pyo3_topyobject() {
    use crate::{FixedOffset, NaiveDate, Utc};
    use std::cmp::Ordering;

    let gil = pyo3::Python::acquire_gil();
    let py = gil.python();
    let check = |y, mo, d, h, m, s, ms, py_ms, f| {
        let datetime = NaiveDate::from_ymd(y, mo, d).and_hms_micro(h, m, s, ms);
        let datetime = DateTime::<Utc>::from_utc(datetime, Utc).to_object(py);
        let datetime: &PyDateTime = datetime.extract(py).unwrap();
        let py_tz = Utc.to_object(py);
        let py_datetime = PyDateTime::new_with_fold(
            py,
            y,
            mo as u8,
            d as u8,
            h as u8,
            m as u8,
            s as u8,
            py_ms,
            Some(&py_tz),
            f,
        )
        .unwrap();
        assert_eq!(datetime.compare(py_datetime).unwrap(), Ordering::Equal);
    };

    check(2014, 5, 6, 7, 8, 9, 1_999_999, 999_999, true);
    check(2014, 5, 6, 7, 8, 9, 999_999, 999_999, false);

    let check = |y, mo, d, h, m, s, ms, py_ms, f| {
        let offset = FixedOffset::east(3600);
        let datetime = NaiveDate::from_ymd(y, mo, d).and_hms_micro(h, m, s, ms);
        let datetime = DateTime::<FixedOffset>::from_utc(datetime, offset).to_object(py);
        let datetime: &PyDateTime = datetime.extract(py).unwrap();
        let py_tz = offset.to_object(py);
        let py_datetime = PyDateTime::new_with_fold(
            py,
            y,
            mo as u8,
            d as u8,
            h as u8,
            m as u8,
            s as u8,
            py_ms,
            Some(&py_tz),
            f,
        )
        .unwrap();
        assert_eq!(datetime.compare(py_datetime).unwrap(), Ordering::Equal);
    };

    check(2014, 5, 6, 7, 8, 9, 1_999_999, 999_999, true);
    check(2014, 5, 6, 7, 8, 9, 999_999, 999_999, false);
}

#[test]
fn test_pyo3_frompyobject() {
    let gil = pyo3::Python::acquire_gil();
    let py = gil.python();
    let check = |y, mo, d, h, m, s, ms, py_ms, f| {
        let py_tz = Utc.to_object(py);
        let py_datetime = PyDateTime::new_with_fold(
            py,
            y as i32,
            mo as u8,
            d as u8,
            h as u8,
            m as u8,
            s as u8,
            py_ms,
            Some(&py_tz),
            f,
        )
        .unwrap();
        let py_datetime: DateTime<Utc> = py_datetime.extract().unwrap();
        let datetime = NaiveDate::from_ymd(y, mo, d).and_hms_micro(h, m, s, ms);
        let datetime = DateTime::<Utc>::from_utc(datetime, Utc);
        assert_eq!(py_datetime, datetime);
    };

    check(2014, 5, 6, 7, 8, 9, 1_999_999, 999_999, true);
    check(2014, 5, 6, 7, 8, 9, 999_999, 999_999, false);

    let check = |y, mo, d, h, m, s, ms, py_ms, f| {
        let offset = FixedOffset::east(3600);
        let py_tz = offset.to_object(py);
        let py_datetime = PyDateTime::new_with_fold(
            py,
            y as i32,
            mo as u8,
            d as u8,
            h as u8,
            m as u8,
            s as u8,
            py_ms,
            Some(&py_tz),
            f,
        )
        .unwrap();
        let py_datetime: DateTime<FixedOffset> = py_datetime.extract().unwrap();
        let datetime = NaiveDate::from_ymd(y, mo, d).and_hms_micro(h, m, s, ms);
        let datetime = DateTime::<FixedOffset>::from_utc(datetime, offset);
        assert_eq!(py_datetime, datetime);
    };

    check(2014, 5, 6, 7, 8, 9, 1_999_999, 999_999, true);
    check(2014, 5, 6, 7, 8, 9, 999_999, 999_999, false);

    // extract utc with fixedoffset should fail
    // but fixedoffset from utc seemed to work, maybe because it is also considered fixedoffset?
    let py_tz = Utc.to_object(py);
    let py_datetime =
        PyDateTime::new_with_fold(py, 2014, 5, 6, 7, 8, 9, 999_999, Some(&py_tz), false).unwrap();
    assert!(py_datetime.extract::<DateTime<FixedOffset>>().is_ok());
    let offset = FixedOffset::east(3600);
    let py_tz = offset.to_object(py);
    let py_datetime =
        PyDateTime::new_with_fold(py, 2014, 5, 6, 7, 8, 9, 999_999, Some(&py_tz), false).unwrap();
    assert!(py_datetime.extract::<DateTime<Utc>>().is_err());
}
