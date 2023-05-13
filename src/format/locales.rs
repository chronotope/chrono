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

pub(crate) fn am_pm(locale: Locale) -> &'static [&'static str] {
    locale_match!(locale => LC_TIME::AM_PM)
}

pub(crate) fn d_fmt(locale: Locale) -> &'static str {
    locale_match!(locale => LC_TIME::D_FMT)
}

pub(crate) fn d_t_fmt(locale: Locale) -> &'static str {
    locale_match!(locale => LC_TIME::D_T_FMT)
}

pub(crate) fn t_fmt(locale: Locale) -> &'static str {
    locale_match!(locale => LC_TIME::T_FMT)
}

macro_rules! expand_ampm {
    ($item:ident) => {
        pure_rust_locales::$item::LC_TIME::T_FMT_AMPM
    };
}

/// Hardcoded `locale_match!` fallback for `T_FMT_AMPM`.
///
/// `local_match_ampm` takes variable number of possible locales that have `LC_TIME::T_FMT_AMPM` field.
/// It will then match the locale and return its `LC_TIME::T_FMT_AMPM` field.
/// It will fallback to `en_US` if the field is an empty string.
///
/// ```rust,ignore
/// // usage:
/// locale => ( Locale::POSIX, Locale::aa_DJ, ...)
/// // expands into:
/// match locale {
///     Locale::POSIX => {
///         let ampm = pure_rust_locales::POSIX::LC_TIME::T_FMT_AMPM;
///
///         if ampm.is_empty() { pure_rust_locales::en_US::LC_TIME::T_FMT_AMPM } else { ampm }
///     },
///     Locale::aa_DJ => // ...
///     // ...
///     _ => pure_rust_locales::en_US::LC_TIME::T_FMT_AMPM,
/// }
/// ```
macro_rules! locale_match_ampm {
    ($locale:expr => ( $($item:ident),* $(,)? )) => {
        match $locale {
            $(Locale::$item => {
                let ampm = expand_ampm!($item);

                if ampm.is_empty() { expand_ampm!(en_US) } else { ampm }
            },)*

            // default fallback is en_US
            _ => expand_ampm!(en_US),
        }
    }
}

/// Finds a locale's time format in 12 hour AM/PM.
///
/// `t_fmt_ampm` uses [`locale_match_ampm`] macro to find `LC_TIME::T_FMT_AMPM` field in `locale`.
///
/// ## Why `locale_match` will not work
///
/// [locale_match] assumes every single locale module to have same field.
/// however, due to issues in [pure-rust-locales][Issue #4],
/// three locales (ff_SN, km_KH, ug_CN) are missing `LC_TIME::T_FMT_AMPM` field,
/// causing a compile error.
///
/// example:
/// ```rust,ignore
/// locale_match!(locale => LC_TIME::T_FMT_AMPM)
///
/// error[E0425]: cannot find value `T_FMT_AMPM` in module `$crate::ff_SN::LC_TIME`
///   --> src/format/locales.rs:72:45
///    |
/// 72 | ...le => LC_TIME::T_FMT_AMPM);
///    |                   ^^^^^^^^^^ not found in `$crate::ff_SN::LC_TIME`
///    |
/// help: consider importing one of these items
///    |
/// 1  | use pure_rust_locales::POSIX::LC_TIME::T_FMT_AMPM;
///    |
/// 1  | use pure_rust_locales::aa_DJ::LC_TIME::T_FMT_AMPM;
///    |
/// 1  | use pure_rust_locales::aa_ER::LC_TIME::T_FMT_AMPM;
///    |
/// 1  | use pure_rust_locales::aa_ER_saaho::LC_TIME::T_FMT_AMPM;
///    |
///      and 285 other candidates
/// ```
///
/// [Issue #4]: https://github.com/cecton/pure-rust-locales/issues/4
pub(crate) fn t_fmt_ampm(locale: Locale) -> &'static str {
    #[allow(unused_imports)]
    use pure_rust_locales::Locale::*;

    locale_match_ampm!(locale => (
        POSIX,
        aa_DJ, aa_ER, aa_ER_saaho, aa_ET, af_ZA, agr_PE, ak_GH, am_ET, an_ES, anp_IN, ar_AE, ar_BH, ar_DZ, ar_EG, ar_IN, ar_IQ, ar_JO, ar_KW, ar_LB, ar_LY, ar_MA, ar_OM, ar_QA, ar_SA, ar_SD, ar_SS, ar_SY, ar_TN, ar_YE, as_IN, ast_ES, ayc_PE, az_AZ, az_IR,
        be_BY, be_BY_latin, bem_ZM, ber_DZ, ber_MA, bg_BG, bhb_IN, bho_IN, bho_NP, bi_VU, bn_BD, bn_IN, bo_CN, bo_IN, br_FR, br_FR_euro, brx_IN, bs_BA, byn_ER,
        ca_AD, ca_ES, ca_ES_euro, ca_ES_valencia, ca_FR, ca_IT, ce_RU, chr_US, cmn_TW, crh_UA, cs_CZ, csb_PL, cv_RU, cy_GB,
        da_DK, de_AT, de_AT_euro, de_BE, de_BE_euro, de_CH, de_DE, de_DE_euro, de_IT, de_LI, de_LU, de_LU_euro, doi_IN, dsb_DE, dv_MV, dz_BT,
        el_CY, el_GR, el_GR_euro, en_AG, en_AU, en_BW, en_CA, en_DK, en_GB, en_HK, en_IE, en_IE_euro, en_IL, en_IN, en_NG, en_NZ, en_PH, en_SC, en_SG, en_US, en_ZA, en_ZM, en_ZW, eo, es_AR, es_BO, es_CL, es_CO, es_CR, es_CU, es_DO, es_EC, es_ES, es_ES_euro, es_GT, es_HN, es_MX, es_NI, es_PA, es_PE, es_PR, es_PY, es_SV, es_US, es_UY, es_VE, et_EE, eu_ES, eu_ES_euro,
        fa_IR, /* ff_SN, */ fi_FI, fi_FI_euro, fil_PH, fo_FO, fr_BE, fr_BE_euro, fr_CA, fr_CH, fr_FR, fr_FR_euro, fr_LU, fr_LU_euro, fur_IT, fy_DE, fy_NL,
        ga_IE, ga_IE_euro, gd_GB, gez_ER, gez_ER_abegede, gez_ET, gez_ET_abegede, gl_ES, gl_ES_euro, gu_IN, gv_GB,
        ha_NG, hak_TW, he_IL, hi_IN, hif_FJ, hne_IN, hr_HR, hsb_DE, ht_HT, hu_HU, hy_AM,
        ia_FR, id_ID, ig_NG, ik_CA, is_IS, it_CH, it_IT, it_IT_euro, iu_CA,
        ja_JP,
        ka_GE, kab_DZ, kk_KZ, kl_GL, /* km_KH, */ kn_IN, ko_KR, kok_IN, ks_IN, ks_IN_devanagari, ku_TR, kw_GB, ky_KG,
        lb_LU, lg_UG, li_BE, li_NL, lij_IT, ln_CD, lo_LA, lt_LT, lv_LV, lzh_TW,
        mag_IN, mai_IN, mai_NP, mfe_MU, mg_MG, mhr_RU, mi_NZ, miq_NI, mjw_IN, mk_MK, ml_IN, mn_MN, mni_IN, mnw_MM, mr_IN, ms_MY, mt_MT, my_MM,
        nan_TW, nan_TW_latin, nb_NO, nds_DE, nds_NL, ne_NP, nhn_MX, niu_NU, niu_NZ, nl_AW, nl_BE, nl_BE_euro, nl_NL, nl_NL_euro, nn_NO, nr_ZA, nso_ZA,
        oc_FR, om_ET, om_KE, or_IN, os_RU,
        pa_IN, pa_PK, pap_AW, pap_CW, pl_PL, ps_AF, pt_BR, pt_PT, pt_PT_euro,
        quz_PE,
        raj_IN, ro_RO, ru_RU, ru_UA, rw_RW,
        sa_IN, sah_RU, sat_IN, sc_IT, sd_IN, sd_IN_devanagari, se_NO, sgs_LT, shn_MM, shs_CA, si_LK, sid_ET, sk_SK, sl_SI, sm_WS, so_DJ, so_ET, so_KE, so_SO, sq_AL, sq_MK, sr_ME, sr_RS, sr_RS_latin, ss_ZA, st_ZA, sv_FI, sv_FI_euro, sv_SE, sw_KE, sw_TZ, szl_PL,
        ta_IN, ta_LK, tcy_IN, te_IN, tg_TJ, th_TH, the_NP, ti_ER, ti_ET, tig_ER, tk_TM, tl_PH, tn_ZA, to_TO, tpi_PG, tr_CY, tr_TR, ts_ZA, tt_RU, tt_RU_iqtelif,
        /* ug_CN, */ uk_UA, unm_US, ur_IN, ur_PK, uz_UZ, uz_UZ_cyrillic,
        ve_ZA, vi_VN,
        wa_BE, wa_BE_euro, wae_CH, wal_ET, wo_SN,
        xh_ZA,
        yi_US, yo_NG, yue_HK, yuw_PG,
        zh_CN, zh_HK, zh_SG, zh_TW, zu_ZA,
    ))
}
