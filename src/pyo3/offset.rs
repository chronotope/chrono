use crate::offset::{FixedOffset, Utc};
use pyo3::conversion::{AsPyPointer, FromPyObject, IntoPy, PyTryFrom, ToPyObject};
use pyo3::exceptions::PyTypeError;
use pyo3::ffi::{PyDateTime_IMPORT, PyDateTime_TimeZone_UTC};
use pyo3::types::{PyDelta, PyDeltaAccess, PyTzInfo};
use pyo3::PyObject;

impl ToPyObject for FixedOffset {
    fn to_object(&self, py: pyo3::Python) -> pyo3::PyObject {
        let dt_module = py.import("datetime").expect("Failed to import datetime");
        let dt_timezone = dt_module.getattr("timezone").expect("Failed to getattr timezone");
        let seconds_offset = self.local_minus_utc();
        let td =
            PyDelta::new(py, 0, seconds_offset, 0, true).expect("Failed to contruct timedelta");
        let offset = dt_timezone.call1((td,)).expect("Failed to call timezone with timedelta");
        offset.into()
    }
}

impl IntoPy<pyo3::PyObject> for FixedOffset {
    fn into_py(self, py: pyo3::Python) -> pyo3::PyObject {
        ToPyObject::to_object(&self, py)
    }
}

impl FromPyObject<'_> for FixedOffset {
    /// Convert python tzinfo to rust [`FixedOffset`].
    ///
    /// Note that the conversion will result in precision lost in microseconds as chrono offset
    /// does not supports microseconds.
    fn extract(ob: &pyo3::PyAny) -> pyo3::PyResult<FixedOffset> {
        let py_tzinfo = <PyTzInfo as PyTryFrom>::try_from(ob)?;
        let py_timedelta = py_tzinfo.call_method1("utcoffset", (ob.py().None(),))?;
        let py_timedelta = <PyDelta as PyTryFrom>::try_from(py_timedelta)?;
        Ok(FixedOffset::east(py_timedelta.get_seconds()))
    }
}

#[test]
fn test_fixed_pyo3_topyobject() {
    let gil = pyo3::Python::acquire_gil();
    let py = gil.python();
    let py_module = py.import("datetime").unwrap();
    let py_timezone = py_module.getattr("timezone").unwrap();
    let offset = FixedOffset::east(3600).to_object(py);
    let py_timedelta = PyDelta::new(py, 0, 3600, 0, true).unwrap();
    let py_timedelta = py_timezone.call1((py_timedelta,)).unwrap();
    assert!(offset.as_ref(py).eq(py_timedelta).unwrap());
    let offset = FixedOffset::east(-3600).to_object(py);
    let py_timedelta = PyDelta::new(py, 0, -3600, 0, true).unwrap();
    let py_timedelta = py_timezone.call1((py_timedelta,)).unwrap();
    assert!(offset.as_ref(py).eq(py_timedelta).unwrap());
}

#[test]
fn test_fixed_pyo3_frompyobject() {
    let gil = pyo3::Python::acquire_gil();
    let py = gil.python();
    let py_module = py.import("datetime").unwrap();
    let py_timezone = py_module.getattr("timezone").unwrap();
    let py_timedelta = PyDelta::new(py, 0, 3600, 0, true).unwrap();
    let py_tzinfo = py_timezone.call1((py_timedelta,)).unwrap();
    let offset: FixedOffset = py_tzinfo.extract().unwrap();
    assert_eq!(FixedOffset::east(3600), offset);
}

impl ToPyObject for Utc {
    fn to_object(&self, py: pyo3::Python) -> pyo3::PyObject {
        unsafe {
            // XXX: not sure if there is a better way to only call this once
            PyDateTime_IMPORT();
            PyObject::from_borrowed_ptr(py, PyDateTime_TimeZone_UTC())
        }
    }
}

impl IntoPy<pyo3::PyObject> for Utc {
    fn into_py(self, py: pyo3::Python) -> pyo3::PyObject {
        ToPyObject::to_object(&self, py)
    }
}

impl FromPyObject<'_> for Utc {
    fn extract(ob: &pyo3::PyAny) -> pyo3::PyResult<Utc> {
        let py_tzinfo = <PyTzInfo as PyTryFrom>::try_from(ob)?;
        let py_utc = unsafe {
            PyDateTime_IMPORT();
            PyDateTime_TimeZone_UTC()
        };
        if py_tzinfo.as_ptr() == py_utc {
            Ok(Utc)
        } else {
            Err(PyTypeError::new_err("Not datetime.timezone.utc"))
        }
    }
}

#[test]
fn test_utc_pyo3_topyobject() {
    let gil = pyo3::Python::acquire_gil();
    let py = gil.python();
    let utc = Utc.to_object(py);
    let py_module = py.import("datetime").unwrap();
    let py_timezone = py_module.getattr("timezone").unwrap();
    let py_utc = py_timezone.getattr("utc").unwrap();
    assert!(utc.as_ref(py).is(py_utc));
}

#[test]
fn test_utc_pyo3_frompyobject() {
    let gil = pyo3::Python::acquire_gil();
    let py = gil.python();
    let py_module = py.import("datetime").unwrap();
    let py_timezone = py_module.getattr("timezone").unwrap();
    let py_utc = py_timezone.getattr("utc").unwrap();
    let py_utc: Utc = py_utc.extract().unwrap();
    assert_eq!(Utc, py_utc);
    let py_timedelta = PyDelta::new(py, 0, 0, 0, false).unwrap();
    let py_timezone_utc = py_timezone.call1((py_timedelta,)).unwrap();
    let py_timezone_utc: Utc = py_timezone_utc.extract().unwrap();
    assert_eq!(Utc, py_timezone_utc);
    let py_timedelta = PyDelta::new(py, 0, 3600, 0, false).unwrap();
    let py_timezone = py_timezone.call1((py_timedelta,)).unwrap();
    assert!(py_timezone.extract::<Utc>().is_err());
}
