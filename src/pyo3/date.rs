use crate::{Datelike, NaiveDate};
use pyo3::conversion::{FromPyObject, IntoPy, PyTryFrom, ToPyObject};
use pyo3::types::{PyDate, PyDateAccess};

impl ToPyObject for NaiveDate {
    fn to_object(&self, py: pyo3::Python) -> pyo3::PyObject {
        let mdf = self.mdf();
        let date = PyDate::new(py, self.year(), mdf.month() as u8, mdf.day() as u8)
            .expect("Failed to construct date");
        date.into()
    }
}

impl IntoPy<pyo3::PyObject> for NaiveDate {
    fn into_py(self, py: pyo3::Python) -> pyo3::PyObject {
        ToPyObject::to_object(&self, py)
    }
}

impl FromPyObject<'_> for NaiveDate {
    fn extract(ob: &pyo3::PyAny) -> pyo3::PyResult<NaiveDate> {
        let date = <PyDate as PyTryFrom>::try_from(ob)?;
        Ok(NaiveDate::from_ymd(date.get_year(), date.get_month() as u32, date.get_day() as u32))
    }
}

#[test]
fn test_pyo3_topyobject() {
    use std::cmp::Ordering;

    let gil = pyo3::Python::acquire_gil();
    let py = gil.python();
    let eq_ymd = |y, m, d| {
        let date = NaiveDate::from_ymd(y, m, d).to_object(py);
        let date: &PyDate = date.extract(py).unwrap();
        let py_date = PyDate::new(py, y, m as u8, d as u8).unwrap();
        assert_eq!(date.compare(py_date).unwrap(), Ordering::Equal);
    };

    eq_ymd(2012, 2, 29);
    eq_ymd(1, 1, 1); // min
    eq_ymd(3000, 6, 5); // future
    eq_ymd(9999, 12, 31); // max
}

#[test]
fn test_pyo3_frompyobject() {
    let gil = pyo3::Python::acquire_gil();
    let py = gil.python();
    let eq_ymd = |y, m, d| {
        let py_date = PyDate::new(py, y, m as u8, d as u8).unwrap();
        let py_date: NaiveDate = py_date.extract().unwrap();
        let date = NaiveDate::from_ymd(y, m, d);
        assert_eq!(py_date, date);
    };

    eq_ymd(2012, 2, 29);
    eq_ymd(1, 1, 1); // min
    eq_ymd(3000, 6, 5); // future
    eq_ymd(9999, 12, 31); // max
}
