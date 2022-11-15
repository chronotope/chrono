#![cfg(feature = "__internal_bench")]

use criterion::{black_box, criterion_group, criterion_main, Criterion};

use chrono::{NaiveDate, NaiveDateTime};

fn bench_ser_naivedatetime_string(c: &mut Criterion) {
    c.bench_function("bench_ser_naivedatetime_string", |b| {
        let dt: NaiveDateTime = "2000-01-01T00:00:00".parse().unwrap();
        b.iter(|| {
            black_box(serde_json::to_string(&dt)).unwrap();
        });
    });
}

fn bench_ser_naivedatetime_writer(c: &mut Criterion) {
    c.bench_function("bench_ser_naivedatetime_writer", |b| {
        let mut s: Vec<u8> = Vec::with_capacity(20);
        let dt: NaiveDateTime = "2000-01-01T00:00:00".parse().unwrap();
        b.iter(|| {
            let s = &mut s;
            s.clear();
            black_box(serde_json::to_writer(s, &dt)).unwrap();
        });
    });
}

fn bench_ser_naivedate_string(c: &mut Criterion) {
    c.bench_function("bench_ser_naivedate_string", |b| {
        let dt: NaiveDate = "1999-11-11".parse().unwrap();
        b.iter(|| {
            black_box(serde_json::to_string(&dt)).unwrap();
        });
    });
}

fn bench_ser_naivedate_writer(c: &mut Criterion) {
    c.bench_function("bench_ser_naivedate_writer", |b| {
        let mut s: Vec<u8> = Vec::with_capacity(20);
        let dt: NaiveDate = "1999-11-11".parse().unwrap();
        b.iter(|| {
            let s = &mut s;
            s.clear();
            black_box(serde_json::to_writer(s, &dt)).unwrap();
        });
    });
}

criterion_group!(
    benches,
    bench_ser_naivedatetime_writer,
    bench_ser_naivedatetime_string,
    bench_ser_naivedate_writer,
    bench_ser_naivedate_string
);
criterion_main!(benches);
