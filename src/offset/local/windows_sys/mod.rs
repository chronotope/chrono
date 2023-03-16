mod file_time;
mod system_time;

pub(crate) use file_time::WinFileTime;
pub(crate) use system_time::WinSystemTime;

/// This macro calls a Windows API FFI and checks whether the function errored with the provided error_id. If an error returns,
/// the macro will return an `Error::last_os_error()`.
///
/// # Safety
///
/// This macro can only check one idea, and provided error ID must be the corresponding error ID.
#[macro_export]
macro_rules! windows_sys_call {
    ($name:ident($($arg:expr),*), $error_id:expr) => {
        if $name($($arg),*) == $error_id {
            return Err(Error::last_os_error());
        }
    }
}
