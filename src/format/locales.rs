#[cfg(feature = "unstable-locales")]
mod localized {
    use icu_calendar::types::MonthCode;
    use icu_datetime::provider::calendar::{GregorianDateSymbolsV1Marker, TimeSymbolsV1Marker};
    use icu_decimal::provider::DecimalSymbolsV1Marker;
    use icu_locid_transform::LocaleExpander;
    use icu_provider::{
        DataError, DataLocale, DataPayload, DataProvider, DataRequest, DataResponse,
        KeyedDataMarker,
    };
    use pure_rust_locales::locale_match;

    struct BakedProvider;
    #[allow(unreachable_pub)]
    mod baked {
        include!(concat!(env!("OUT_DIR"), "/baked_data/mod.rs"));
        impl_data_provider!(super::BakedProvider);
    }

    pub(crate) fn default_locale() -> pure_rust_locales::Locale {
        pure_rust_locales::Locale::POSIX
    }

    fn get_payload<M>(locale: pure_rust_locales::Locale) -> Result<DataPayload<M>, DataError>
    where
        M: KeyedDataMarker,
        BakedProvider: icu_provider::DataProvider<M>,
    {
        // Convert pure_rust_locales::Locale -> String
        // POSIX doesn't exist in icu4, falling back to English
        let locale_string = match locale {
            pure_rust_locales::Locale::POSIX => "en".to_string(),
            _ => format!("{:?}", locale),
        };

        // Continue converting the locale_string in to a icu_locid::Locale
        let mut locale = icu_locid::Locale::try_from_bytes(locale_string.as_bytes())
            .expect("Could not create Locale");

        // Minimize icu_locid::Locale to make the locale as generic as it can be without losing anything
        // Ex. en-US -> en, but en-CA stays en-CA
        let lc = LocaleExpander::try_new_unstable(&BakedProvider)
            .expect("Failed to create LocaleExpander");
        lc.minimize(&mut locale);

        BakedProvider
            .load(DataRequest { locale: &DataLocale::from(locale), metadata: Default::default() })
            .or_else(|_| BakedProvider.load(DataRequest::default()))
            .and_then(|response: DataResponse<M>| response.take_payload())
    }

    pub(crate) fn short_months(locale: pure_rust_locales::Locale) -> [String; 12] {
        get_payload::<GregorianDateSymbolsV1Marker>(locale).map_or(
            [
                "Jan".to_string(),
                "Feb".to_string(),
                "Mar".to_string(),
                "Apr".to_string(),
                "May".to_string(),
                "Jun".to_string(),
                "Jul".to_string(),
                "Aug".to_string(),
                "Sep".to_string(),
                "Oct".to_string(),
                "Nov".to_string(),
                "Dec".to_string(),
            ],
            |payload| {
                let format_abbreviated = &payload.get().months.format.abbreviated;
                [
                    format_abbreviated
                        .get(MonthCode("M01".parse().unwrap()))
                        .map_or("Jan".to_string(), ToString::to_string),
                    format_abbreviated
                        .get(MonthCode("M02".parse().unwrap()))
                        .map_or("Feb".to_string(), ToString::to_string),
                    format_abbreviated
                        .get(MonthCode("M03".parse().unwrap()))
                        .map_or("Mar".to_string(), ToString::to_string),
                    format_abbreviated
                        .get(MonthCode("M04".parse().unwrap()))
                        .map_or("Apr".to_string(), ToString::to_string),
                    format_abbreviated
                        .get(MonthCode("M05".parse().unwrap()))
                        .map_or("May".to_string(), ToString::to_string),
                    format_abbreviated
                        .get(MonthCode("M06".parse().unwrap()))
                        .map_or("Jun".to_string(), ToString::to_string),
                    format_abbreviated
                        .get(MonthCode("M07".parse().unwrap()))
                        .map_or("Jul".to_string(), ToString::to_string),
                    format_abbreviated
                        .get(MonthCode("M08".parse().unwrap()))
                        .map_or("Aug".to_string(), ToString::to_string),
                    format_abbreviated
                        .get(MonthCode("M09".parse().unwrap()))
                        .map_or("Sep".to_string(), ToString::to_string),
                    format_abbreviated
                        .get(MonthCode("M10".parse().unwrap()))
                        .map_or("Oct".to_string(), ToString::to_string),
                    format_abbreviated
                        .get(MonthCode("M11".parse().unwrap()))
                        .map_or("Nov".to_string(), ToString::to_string),
                    format_abbreviated
                        .get(MonthCode("M12".parse().unwrap()))
                        .map_or("Dec".to_string(), ToString::to_string),
                ]
            },
        )
    }

    pub(crate) fn long_months(locale: pure_rust_locales::Locale) -> [String; 12] {
        get_payload::<GregorianDateSymbolsV1Marker>(locale).map_or(
            [
                "January".to_string(),
                "February".to_string(),
                "March".to_string(),
                "April".to_string(),
                "May".to_string(),
                "June".to_string(),
                "July".to_string(),
                "August".to_string(),
                "September".to_string(),
                "October".to_string(),
                "November".to_string(),
                "December".to_string(),
            ],
            |payload| {
                let format_wide = &payload.get().months.format.wide;
                [
                    format_wide
                        .get(MonthCode("M01".parse().unwrap()))
                        .map_or("January".to_string(), ToString::to_string),
                    format_wide
                        .get(MonthCode("M02".parse().unwrap()))
                        .map_or("February".to_string(), ToString::to_string),
                    format_wide
                        .get(MonthCode("M03".parse().unwrap()))
                        .map_or("March".to_string(), ToString::to_string),
                    format_wide
                        .get(MonthCode("M04".parse().unwrap()))
                        .map_or("April".to_string(), ToString::to_string),
                    format_wide
                        .get(MonthCode("M05".parse().unwrap()))
                        .map_or("May".to_string(), ToString::to_string),
                    format_wide
                        .get(MonthCode("M06".parse().unwrap()))
                        .map_or("June".to_string(), ToString::to_string),
                    format_wide
                        .get(MonthCode("M07".parse().unwrap()))
                        .map_or("July".to_string(), ToString::to_string),
                    format_wide
                        .get(MonthCode("M08".parse().unwrap()))
                        .map_or("August".to_string(), ToString::to_string),
                    format_wide
                        .get(MonthCode("M09".parse().unwrap()))
                        .map_or("September".to_string(), ToString::to_string),
                    format_wide
                        .get(MonthCode("M10".parse().unwrap()))
                        .map_or("October".to_string(), ToString::to_string),
                    format_wide
                        .get(MonthCode("M11".parse().unwrap()))
                        .map_or("November".to_string(), ToString::to_string),
                    format_wide
                        .get(MonthCode("M12".parse().unwrap()))
                        .map_or("December".to_string(), ToString::to_string),
                ]
            },
        )
    }

    pub(crate) fn short_weekdays(locale: pure_rust_locales::Locale) -> [String; 7] {
        get_payload::<GregorianDateSymbolsV1Marker>(locale).map_or(
            [
                "Sun".to_string(),
                "Mon".to_string(),
                "Tue".to_string(),
                "Wed".to_string(),
                "Thu".to_string(),
                "Fri".to_string(),
                "Sat".to_string(),
            ],
            |payload| {
                let format_abbreviated = &payload.get().weekdays.format.abbreviated.0;
                [
                    format_abbreviated[0].to_string(),
                    format_abbreviated[1].to_string(),
                    format_abbreviated[2].to_string(),
                    format_abbreviated[3].to_string(),
                    format_abbreviated[4].to_string(),
                    format_abbreviated[5].to_string(),
                    format_abbreviated[6].to_string(),
                ]
            },
        )
    }

    pub(crate) fn long_weekdays(locale: pure_rust_locales::Locale) -> [String; 7] {
        get_payload::<GregorianDateSymbolsV1Marker>(locale).map_or(
            [
                "Sunday".to_string(),
                "Monday".to_string(),
                "Tuesday".to_string(),
                "Wednesday".to_string(),
                "Thursday".to_string(),
                "Friday".to_string(),
                "Saturday".to_string(),
            ],
            |payload| {
                let format_wide = &payload.get().weekdays.format.wide.0;
                [
                    format_wide[0].to_string(),
                    format_wide[1].to_string(),
                    format_wide[2].to_string(),
                    format_wide[3].to_string(),
                    format_wide[4].to_string(),
                    format_wide[5].to_string(),
                    format_wide[6].to_string(),
                ]
            },
        )
    }

    pub(crate) fn am_pm(locale: pure_rust_locales::Locale) -> [String; 2] {
        get_payload::<TimeSymbolsV1Marker>(locale).map_or(
            ["AM".to_string(), "PM".to_string()],
            |payload| {
                let format_wide = &payload.get().day_periods.format.wide;
                [format_wide.am.to_string(), format_wide.pm.to_string()]
            },
        )
    }

    pub(crate) fn decimal_point(locale: pure_rust_locales::Locale) -> String {
        get_payload::<DecimalSymbolsV1Marker>(locale)
            .map_or(".".to_string(), |payload| payload.get().decimal_separator.to_string())
    }

    pub(crate) fn d_fmt(locale: pure_rust_locales::Locale) -> &'static str {
        locale_match!(locale => LC_TIME::D_FMT)
    }

    pub(crate) fn d_t_fmt(locale: pure_rust_locales::Locale) -> &'static str {
        locale_match!(locale => LC_TIME::D_T_FMT)
    }

    pub(crate) fn t_fmt(locale: pure_rust_locales::Locale) -> &'static str {
        locale_match!(locale => LC_TIME::T_FMT)
    }

    pub(crate) fn t_fmt_ampm(locale: pure_rust_locales::Locale) -> &'static str {
        locale_match!(locale => LC_TIME::T_FMT_AMPM)
    }
}

#[cfg(feature = "unstable-locales")]
pub(crate) use localized::*;
#[cfg(feature = "unstable-locales")]
pub use pure_rust_locales::Locale;

#[cfg(not(feature = "unstable-locales"))]
mod unlocalized {
    #[derive(Copy, Clone, Debug)]
    pub(crate) struct Locale;

    pub(crate) const fn default_locale() -> Locale {
        Locale
    }

    pub(crate) const fn short_months(_locale: Locale) -> &'static [&'static str] {
        &["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
    }

    pub(crate) const fn long_months(_locale: Locale) -> &'static [&'static str] {
        &[
            "January",
            "February",
            "March",
            "April",
            "May",
            "June",
            "July",
            "August",
            "September",
            "October",
            "November",
            "December",
        ]
    }

    pub(crate) const fn short_weekdays(_locale: Locale) -> &'static [&'static str] {
        &["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]
    }

    pub(crate) const fn long_weekdays(_locale: Locale) -> &'static [&'static str] {
        &["Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"]
    }

    pub(crate) const fn am_pm(_locale: Locale) -> &'static [&'static str] {
        &["AM", "PM"]
    }

    pub(crate) const fn decimal_point(_locale: Locale) -> &'static str {
        "."
    }
}

#[cfg(not(feature = "unstable-locales"))]
pub(crate) use unlocalized::*;
