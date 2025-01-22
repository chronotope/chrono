//! Benchmarks for chrono that just depend on std

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use chrono::format::StrftimeItems;
use chrono::prelude::*;
#[cfg(feature = "unstable-locales")]
use chrono::Locale;
use chrono::{DateTime, FixedOffset, Local, TimeDelta, Utc, __BenchYearFlags};

fn bench_date_from_ymd(c: &mut Criterion) {
    c.bench_function("bench_date_from_ymd", |b| {
        let expected = NaiveDate::from_ymd_opt(2024, 2, 12);
        b.iter(|| {
            let (y, m, d) = black_box((2024, 2, 12));
            assert_eq!(NaiveDate::from_ymd_opt(y, m, d), expected)
        })
    });
}

fn bench_datetime_parse_from_rfc2822(c: &mut Criterion) {
    c.bench_function("bench_datetime_parse_from_rfc2822", |b| {
        b.iter(|| {
            let str = black_box("Wed, 18 Feb 2015 23:16:09 +0000");
            DateTime::parse_from_rfc2822(str).unwrap()
        })
    });
}

fn bench_datetime_parse_from_rfc3339(c: &mut Criterion) {
    c.bench_function("bench_datetime_parse_from_rfc3339", |b| {
        b.iter(|| {
            let str = black_box("2015-02-18T23:59:60.234567+05:00");
            DateTime::parse_from_rfc3339(str).unwrap()
        })
    });
}

fn bench_datetime_from_str(c: &mut Criterion) {
    c.bench_function("bench_datetime_from_str", |b| {
        b.iter(|| {
            use std::str::FromStr;
            let str = black_box("2019-03-30T18:46:57.193Z");
            DateTime::<Utc>::from_str(str).unwrap()
        })
    });
}

fn bench_datetime_to_rfc2822(c: &mut Criterion) {
    let pst = FixedOffset::east_opt(8 * 60 * 60).unwrap();
    let dt = pst
        .from_local_datetime(
            &NaiveDate::from_ymd_opt(2018, 1, 11)
                .unwrap()
                .and_hms_nano_opt(10, 5, 13, 84_660_000)
                .unwrap(),
        )
        .unwrap();
    c.bench_function("bench_datetime_to_rfc2822", |b| b.iter(|| black_box(dt).to_rfc2822()));
}

fn bench_datetime_to_rfc3339(c: &mut Criterion) {
    let pst = FixedOffset::east_opt(8 * 60 * 60).unwrap();
    let dt = pst
        .from_local_datetime(
            &NaiveDate::from_ymd_opt(2018, 1, 11)
                .unwrap()
                .and_hms_nano_opt(10, 5, 13, 84_660_000)
                .unwrap(),
        )
        .unwrap();
    c.bench_function("bench_datetime_to_rfc3339", |b| b.iter(|| black_box(dt).to_rfc3339()));
}

fn bench_datetime_to_rfc3339_opts(c: &mut Criterion) {
    let pst = FixedOffset::east_opt(8 * 60 * 60).unwrap();
    let dt = pst
        .from_local_datetime(
            &NaiveDate::from_ymd_opt(2018, 1, 11)
                .unwrap()
                .and_hms_nano_opt(10, 5, 13, 84_660_000)
                .unwrap(),
        )
        .unwrap();
    c.bench_function("bench_datetime_to_rfc3339_opts", |b| {
        b.iter(|| black_box(dt).to_rfc3339_opts(SecondsFormat::Nanos, true))
    });
}

fn bench_year_flags_from_year(c: &mut Criterion) {
    c.bench_function("bench_year_flags_from_year", |b| {
        b.iter(|| {
            for year in -999i32..1000 {
                let _ = __BenchYearFlags::from_year(black_box(year));
            }
        })
    });
}

fn bench_get_local_time(c: &mut Criterion) {
    c.bench_function("bench_get_local_time", |b| {
        b.iter(|| {
            let _ = Local::now();
        })
    });
}

/// Returns the number of multiples of `div` in the range `start..end`.
///
/// If the range `start..end` is back-to-front, i.e. `start` is greater than `end`, the
/// behaviour is defined by the following equation:
/// `in_between(start, end, div) == - in_between(end, start, div)`.
///
/// When `div` is 1, this is equivalent to `end - start`, i.e. the length of `start..end`.
///
/// # Panics
///
/// Panics if `div` is not positive.
fn in_between(start: i32, end: i32, div: i32) -> i32 {
    assert!(div > 0, "in_between: nonpositive div = {}", div);
    let start = (start.div_euclid(div), start.rem_euclid(div));
    let end = (end.div_euclid(div), end.rem_euclid(div));
    // The lowest multiple of `div` greater than or equal to `start`, divided.
    let start = start.0 + (start.1 != 0) as i32;
    // The lowest multiple of `div` greater than or equal to   `end`, divided.
    let end = end.0 + (end.1 != 0) as i32;
    end - start
}

/// Alternative implementation to `Datelike::num_days_from_ce`
fn num_days_from_ce_alt<Date: Datelike>(date: &Date) -> i32 {
    let year = date.year();
    let diff = move |div| in_between(1, year, div);
    // 365 days a year, one more in leap years. In the gregorian calendar, leap years are all
    // the multiples of 4 except multiples of 100 but including multiples of 400.
    date.ordinal() as i32 + 365 * diff(1) + diff(4) - diff(100) + diff(400)
}

fn bench_num_days_from_ce(c: &mut Criterion) {
    let mut group = c.benchmark_group("num_days_from_ce");
    for year in &[1, 500, 2000, 2019] {
        let d = NaiveDate::from_ymd_opt(*year, 1, 1).unwrap();
        group.bench_with_input(BenchmarkId::new("new", year), &d, |b, y| {
            b.iter(|| num_days_from_ce_alt(y))
        });
        group.bench_with_input(BenchmarkId::new("classic", year), &d, |b, y| {
            b.iter(|| y.num_days_from_ce())
        });
    }
}

fn bench_parse_strftime(c: &mut Criterion) {
    c.bench_function("bench_parse_strftime", |b| {
        b.iter(|| {
            let str = black_box("%a, %d %b %Y %H:%M:%S GMT");
            let items = StrftimeItems::new(str);
            black_box(items.collect::<Vec<_>>());
        })
    });
}

#[cfg(feature = "unstable-locales")]
fn bench_parse_strftime_localized(c: &mut Criterion) {
    c.bench_function("bench_parse_strftime_localized", |b| {
        b.iter(|| {
            let str = black_box("%a, %d %b %Y %H:%M:%S GMT");
            let items = StrftimeItems::new_with_locale(str, Locale::nl_NL);
            black_box(items.collect::<Vec<_>>());
        })
    });
}

fn bench_format(c: &mut Criterion) {
    let dt = Local::now();
    c.bench_function("bench_format", |b| {
        b.iter(|| format!("{}", black_box(dt).format("%Y-%m-%dT%H:%M:%S%.f%:z")))
    });
}

fn bench_format_with_items(c: &mut Criterion) {
    let dt = Local::now();
    let items: Vec<_> = StrftimeItems::new("%Y-%m-%dT%H:%M:%S%.f%:z").collect();
    c.bench_function("bench_format_with_items", |b| {
        b.iter(|| format!("{}", black_box(dt).format_with_items(items.iter())))
    });
}

fn benches_delayed_format(c: &mut Criterion) {
    let mut group = c.benchmark_group("delayed_format");
    let dt = Local::now();
    group.bench_function(BenchmarkId::new("with_display", dt), |b| {
        b.iter_batched(
            || dt.format("%Y-%m-%dT%H:%M:%S%.f%:z"),
            |df| black_box(df).to_string(),
            criterion::BatchSize::SmallInput,
        )
    });
    group.bench_function(BenchmarkId::new("with_string_buffer", dt), |b| {
        b.iter_batched(
            || (dt.format("%Y-%m-%dT%H:%M:%S%.f%:z"), String::with_capacity(256)),
            |(df, string)| black_box(df).write_to(&mut black_box(string)),
            criterion::BatchSize::SmallInput,
        )
    });
}

fn bench_format_manual(c: &mut Criterion) {
    let dt = Local::now();
    c.bench_function("bench_format_manual", |b| {
        b.iter(|| {
            black_box(dt);
            format!(
                "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}.{:09}{:+02}:{:02}",
                dt.year(),
                dt.month(),
                dt.day(),
                dt.hour(),
                dt.minute(),
                dt.second(),
                dt.nanosecond(),
                dt.offset().fix().local_minus_utc() / 3600,
                dt.offset().fix().local_minus_utc() / 60,
            )
        })
    });
}

fn bench_naivedate_add_signed(c: &mut Criterion) {
    let date = NaiveDate::from_ymd_opt(2023, 7, 29).unwrap();
    let extra = TimeDelta::try_days(25).unwrap();
    c.bench_function("bench_naivedate_add_signed", |b| {
        b.iter(|| black_box(date).checked_add_signed(extra).unwrap())
    });
}

fn bench_datetime_with(c: &mut Criterion) {
    let dt = FixedOffset::east_opt(3600).unwrap().with_ymd_and_hms(2023, 9, 23, 7, 36, 0).unwrap();
    c.bench_function("bench_datetime_with", |b| {
        b.iter(|| black_box(black_box(dt).with_hour(12)).unwrap())
    });
}

criterion_group!(
    benches,
    bench_date_from_ymd,
    bench_datetime_parse_from_rfc2822,
    bench_datetime_parse_from_rfc3339,
    bench_datetime_from_str,
    bench_datetime_to_rfc2822,
    bench_datetime_to_rfc3339,
    bench_datetime_to_rfc3339_opts,
    bench_year_flags_from_year,
    bench_num_days_from_ce,
    bench_get_local_time,
    bench_parse_strftime,
    bench_format,
    bench_format_with_items,
    bench_format_manual,
    benches_delayed_format,
    bench_naivedate_add_signed,
    bench_datetime_with,
);

#[cfg(feature = "unstable-locales")]
criterion_group!(unstable_locales, bench_parse_strftime_localized,);

#[cfg(not(feature = "unstable-locales"))]
criterion_main!(benches);
#[cfg(feature = "unstable-locales")]
criterion_main!(benches, unstable_locales);
