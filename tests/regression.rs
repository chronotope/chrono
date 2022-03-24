#[cfg(all(test, feature = "clock"))]
mod test {

    #[test]
    fn verify_regression() {
        let current_utc = chrono::Utc::now();

        let old_utc = old_chrono::DateTime::parse_from_rfc3339(&current_utc.to_rfc3339()).unwrap();

        assert_eq!(current_utc.timestamp_millis(), old_utc.timestamp_millis());

        let old_from_utc: old_chrono::DateTime<old_chrono::Local> =
            old_chrono::TimeZone::from_utc_datetime(&old_chrono::Local, &old_utc.naive_local());
        let current_from_utc: chrono::DateTime<chrono::Local> =
            chrono::TimeZone::from_utc_datetime(&chrono::Local, &current_utc.naive_local());

        assert_eq!(current_from_utc.timestamp_millis(), old_from_utc.timestamp_millis());

        let old_from_local: old_chrono::DateTime<old_chrono::Local> =
            old_chrono::TimeZone::from_local_datetime(&old_chrono::Local, &old_utc.naive_local())
                .unwrap();
        let current_from_local: chrono::DateTime<chrono::Local> =
            chrono::TimeZone::from_local_datetime(&chrono::Local, &current_utc.naive_local())
                .unwrap();

        assert_eq!(current_from_local.timestamp_millis(), old_from_local.timestamp_millis());
    }

    #[test]
    fn verify_regression_distant_future() {
        let distant_future_utc = chrono::Utc::now() + chrono::Duration::days(365 * 1000);

        let old_utc =
            old_chrono::DateTime::parse_from_rfc3339(&distant_future_utc.to_rfc3339()).unwrap();

        assert_eq!(distant_future_utc.timestamp_millis(), old_utc.timestamp_millis());

        let old_from_utc: old_chrono::DateTime<old_chrono::Local> =
            old_chrono::TimeZone::from_utc_datetime(&old_chrono::Local, &old_utc.naive_local());
        let current_from_utc: chrono::DateTime<chrono::Local> =
            chrono::TimeZone::from_utc_datetime(&chrono::Local, &distant_future_utc.naive_local());

        assert_eq!(current_from_utc.timestamp_millis(), old_from_utc.timestamp_millis());

        let old_from_local: old_chrono::DateTime<old_chrono::Local> =
            old_chrono::TimeZone::from_local_datetime(&old_chrono::Local, &old_utc.naive_local())
                .unwrap();
        let current_from_local: chrono::DateTime<chrono::Local> =
            chrono::TimeZone::from_local_datetime(
                &chrono::Local,
                &distant_future_utc.naive_local(),
            )
            .unwrap();

        assert_eq!(current_from_local.timestamp_millis(), old_from_local.timestamp_millis());
    }

    #[test]
    fn verify_regression_distant_past() {
        let distant_past_utc = chrono::Utc::now() - chrono::Duration::days(365 * 1000);

        let old_utc =
            old_chrono::DateTime::parse_from_rfc3339(&distant_past_utc.to_rfc3339()).unwrap();

        assert_eq!(distant_past_utc.timestamp_millis(), old_utc.timestamp_millis());

        let old_from_utc: old_chrono::DateTime<old_chrono::Local> =
            old_chrono::TimeZone::from_utc_datetime(&old_chrono::Local, &old_utc.naive_local());
        let current_from_utc: chrono::DateTime<chrono::Local> =
            chrono::TimeZone::from_utc_datetime(&chrono::Local, &distant_past_utc.naive_local());

        assert_eq!(current_from_utc.timestamp_millis(), old_from_utc.timestamp_millis());

        let old_from_local: old_chrono::DateTime<old_chrono::Local> =
            old_chrono::TimeZone::from_local_datetime(&old_chrono::Local, &old_utc.naive_local())
                .unwrap();
        let current_from_local: chrono::DateTime<chrono::Local> =
            chrono::TimeZone::from_local_datetime(&chrono::Local, &distant_past_utc.naive_local())
                .unwrap();

        assert_eq!(current_from_local.timestamp_millis(), old_from_local.timestamp_millis());
    }
}
