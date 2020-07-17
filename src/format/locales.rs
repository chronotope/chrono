use pure_rust_locales::{locale_match, Locale};

pub(crate) fn short_months(locale: Locale) -> &'static [&'static str] {
    locale_match!(locale => LC_TIME::ABMON)
}

pub(crate) fn long_months(locale: Locale) -> &'static [&'static str] {
    locale_match!(locale => LC_TIME::MON)
}

pub(crate) fn short_weekdays(locale: Locale) -> &'static [&'static str] {
    locale_match!(locale => LC_TIME::ABDAY)
}

pub(crate) fn long_weekdays(locale: Locale) -> &'static [&'static str] {
    locale_match!(locale => LC_TIME::DAY)
}
