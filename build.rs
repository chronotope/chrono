// This file is part of ICU4X. For terms of use, please see the file
// called LICENSE at the top level of the ICU4X source tree
// (online at: https://github.com/unicode-org/icu4x/blob/main/LICENSE ).

#[cfg(feature = "unstable-locales")]
fn main() {
    use icu_datagen::prelude::*;
    use std::path::PathBuf;
    println!("cargo:rerun-if-changed=build.rs");

    let out_dir = std::env::var_os("OUT_DIR").unwrap();
    let mod_directory = PathBuf::from(out_dir).join("baked_data");

    let mut options = BakedOptions::default();
    // Whether to overwrite existing data. By default, errors if it is present.
    options.overwrite = true;
    // Whether to use separate crates to name types instead of the `icu` metacrate
    options.use_separate_crates = true;

    icu_datagen::datagen(
        None,
        // Note: These are the keys required by `PluralRules::try_new_cardinal_unstable`
        &[
            icu_decimal::provider::DecimalSymbolsV1Marker::KEY,
            icu_datetime::provider::calendar::TimeSymbolsV1Marker::KEY,
            icu_datetime::provider::calendar::GregorianDateSymbolsV1Marker::KEY,
            icu_locid_transform::provider::LikelySubtagsForLanguageV1Marker::KEY,
            icu_locid_transform::provider::LikelySubtagsForScriptRegionV1Marker::KEY,
        ],
        &SourceData::default()
            .with_cldr_for_tag(SourceData::LATEST_TESTED_CLDR_TAG, CldrLocaleSubset::Modern)
            .expect("Infallible"),
        vec![icu_datagen::Out::Baked { mod_directory, options }],
    )
    .expect("Datagen should be successful");
}
#[cfg(not(feature = "unstable-locales"))]
fn main() {}
