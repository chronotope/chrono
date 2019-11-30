//! Benchmarks for chrono that just depend on std

extern crate chrono;
extern crate criterion;

use criterion::{black_box, criterion_group, criterion_main, Criterion};

use chrono::prelude::*;
use chrono::{Utc, FixedOffset, DateTime, YearFlags};

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
    let pst = FixedOffset::east(8 * 60 * 60);
    let dt = pst.ymd(2018, 1, 11).and_hms_nano(10, 5, 13, 084_660_000);
    c.bench_function("bench_datetime_to_rfc2822", |b| {
        b.iter(|| black_box(dt).to_rfc2822())
    });
}

fn bench_datetime_to_rfc3339(c: &mut Criterion) {
    let pst = FixedOffset::east(8 * 60 * 60);
    let dt = pst.ymd(2018, 1, 11).and_hms_nano(10, 5, 13, 084_660_000);
    c.bench_function("bench_datetime_to_rfc3339", |b| {
        b.iter(|| black_box(dt).to_rfc3339())
    });
}

fn bench_year_flags_from_year(c: &mut Criterion) {
    c.bench_function("bench_year_flags_from_year", |b|
                     b.iter(|| {
        for year in -999i32..1000 {
            YearFlags::from_year(year);
        }
    }));
}

criterion_group!(
    benches,
    bench_datetime_parse_from_rfc2822,
    bench_datetime_parse_from_rfc3339,
    bench_datetime_from_str,
    bench_datetime_to_rfc2822,
    bench_datetime_to_rfc3339,
    bench_year_flags_from_year,
);

criterion_main!(benches);
