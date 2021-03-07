use crate::{NaiveTime, Timelike};
use pyo3::conversion::{FromPyObject, IntoPy, PyTryFrom, ToPyObject};
use pyo3::types::{PyTime, PyTimeAccess};

impl ToPyObject for NaiveTime {
    fn to_object(&self, py: pyo3::Python) -> pyo3::PyObject {
        let (h, m, s) = self.hms();
        let ns = self.nanosecond();
        let (ms, fold) = match ns.checked_sub(1_000_000_000) {
            Some(ns) => (ns / 1000, true),
            None => (ns / 1000, false),
        };
        let time = PyTime::new_with_fold(py, h as u8, m as u8, s as u8, ms, None, fold)
            .expect("Failed to construct time");
        time.into()
    }
}

impl IntoPy<pyo3::PyObject> for NaiveTime {
    fn into_py(self, py: pyo3::Python) -> pyo3::PyObject {
        ToPyObject::to_object(&self, py)
    }
}

impl FromPyObject<'_> for NaiveTime {
    fn extract(ob: &pyo3::PyAny) -> pyo3::PyResult<NaiveTime> {
        let time = <PyTime as PyTryFrom>::try_from(ob)?;
        let ms = time.get_fold() as u32 * 1_000_000 + time.get_microsecond();
        let (h, m, s) = (time.get_hour(), time.get_minute(), time.get_second());
        Ok(NaiveTime::from_hms_micro(h as u32, m as u32, s as u32, ms))
    }
}

#[test]
fn test_pyo3_topyobject() {
    use std::cmp::Ordering;

    let gil = pyo3::Python::acquire_gil();
    let py = gil.python();
    let hmsm = |h, m, s, ms, py_ms, f| {
        let time = NaiveTime::from_hms_micro(h, m, s, ms).to_object(py);
        let time: &PyTime = time.extract(py).unwrap();
        let py_time = PyTime::new_with_fold(py, h as u8, m as u8, s as u8, py_ms, None, f).unwrap();
        assert_eq!(time.compare(py_time).unwrap(), Ordering::Equal);
    };

    hmsm(3, 5, 7, 1_999_999, 999_999, true);
    hmsm(3, 5, 7, 999_999, 999_999, false);
}

#[test]
fn test_pyo3_frompyobject() {
    let gil = pyo3::Python::acquire_gil();
    let py = gil.python();
    let hmsm = |h, m, s, ms, py_ms, f| {
        let py_time = PyTime::new_with_fold(py, h as u8, m as u8, s as u8, py_ms, None, f).unwrap();
        let py_time: NaiveTime = py_time.extract().unwrap();
        let time = NaiveTime::from_hms_micro(h, m, s, ms);
        assert_eq!(py_time, time);
    };

    hmsm(3, 5, 7, 1_999_999, 999_999, true);
    hmsm(3, 5, 7, 999_999, 999_999, false);
}
