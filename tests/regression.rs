#[cfg(all(test, feature = "clock"))]
mod test {

    #[test]
    fn verify_regression() {
        let current_utc_base = chrono::Utc::now();

        for diff in (-400000..400000).filter(|d| d % 25 == 0) {
            let current_utc = current_utc_base + chrono::Duration::days(diff);

            let old_utc =
                old_chrono::DateTime::parse_from_rfc3339(&current_utc.to_rfc3339()).unwrap();

            assert_eq!(current_utc.timestamp_millis(), old_utc.timestamp_millis());

            let old_from_utc: old_chrono::DateTime<old_chrono::Local> =
                old_chrono::TimeZone::from_utc_datetime(&old_chrono::Local, &old_utc.naive_local());
            let current_from_utc: chrono::DateTime<chrono::Local> =
                chrono::TimeZone::from_utc_datetime(&chrono::Local, &current_utc.naive_local());

            assert_eq!(current_from_utc.timestamp_millis(), old_from_utc.timestamp_millis());

            let old_from_local: old_chrono::DateTime<old_chrono::Local> =
                old_chrono::TimeZone::from_local_datetime(
                    &old_chrono::Local,
                    &old_utc.naive_local(),
                )
                .unwrap();
            let current_from_local: chrono::DateTime<chrono::Local> =
                chrono::TimeZone::from_local_datetime(&chrono::Local, &current_utc.naive_local())
                    .unwrap();

            assert_eq!(current_from_local.timestamp_millis(), old_from_local.timestamp_millis());
        }
    }
}
