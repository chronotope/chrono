#[cfg(feature = "locales")]
mod with_locales {
    use super::super::{FormatError, FormatErrorKind, FormatResult};

    macro_rules! locale_match {
        ($locale:expr => $($item:ident)::+) => {{
            match $locale {
                "en_US" => Ok(pure_rust_locales::en_US::$($item)::+),
                "fr_BE" => Ok(pure_rust_locales::fr_BE::$($item)::+),
                // TODO: all the locales are available
                _ => Err(FormatError(FormatErrorKind::UnknownLocale)),
            }
        }}
    }

    pub(crate) fn short_months(locale: &str) -> FormatResult<&[&'static str]> {
        locale_match!(locale => LC_TIME::ABMON)
    }

    pub(crate) fn long_months(locale: &str) -> FormatResult<&[&'static str]> {
        locale_match!(locale => LC_TIME::MON)
    }

    pub(crate) fn short_weekdays(locale: &str) -> FormatResult<&[&'static str]> {
        locale_match!(locale => LC_TIME::ABDAY)
    }

    pub(crate) fn long_weekdays(locale: &str) -> FormatResult<&[&'static str]> {
        locale_match!(locale => LC_TIME::DAY)
    }
}

#[cfg(not(feature = "locales"))]
mod without_locales {
    use super::super::FormatResult;

    pub(crate) fn short_months(_locale: &str) -> FormatResult<&[&'static str]> {
        Ok(pure_rust_locales::en_US::LC_TIME::ABMON)
    }

    pub(crate) fn long_months(_locale: &str) -> FormatResult<&[&'static str]> {
        Ok(pure_rust_locales::en_US::LC_TIME::MON)
    }

    pub(crate) fn short_weekdays(_locale: &str) -> FormatResult<&[&'static str]> {
        Ok(pure_rust_locales::en_US::LC_TIME::ABDAY)
    }

    pub(crate) fn long_weekdays(_locale: &str) -> FormatResult<&[&'static str]> {
        Ok(pure_rust_locales::en_US::LC_TIME::DAY)
    }
}

#[cfg(feature = "locales")]
pub(crate) use self::with_locales::*;

#[cfg(not(feature = "locales"))]
pub(crate) use self::without_locales::*;
