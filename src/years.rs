// I usually develop with this clippy flags
// but I can remove once the this module is done
#![warn(clippy::all,
/*#![warn(*/clippy::pedantic,
		clippy::perf,
        clippy::nursery,
        // clippy::cargo,
        clippy::unwrap_used,
        clippy::expect_used)]

/// TODO
#[derive(Debug)]
pub struct Years(pub(crate) u32); // I believe the fields of the struct should be private

impl Years {
    /// TODO
    pub fn new(num_years: u32) -> Years {
        Self(num_years)
    }
}

#[cfg(test)]
mod tests {
    use crate::NaiveDate;
    use crate::Years;

    #[test]
    fn checked_adding_years() {
        assert_eq!(
            NaiveDate::from_ymd_opt(2023, 2, 28).unwrap(),
            NaiveDate::from_ymd_opt(2020, 2, 28).unwrap().checked_add_years(Years::new(3)).unwrap()
        );
    }

    #[test]
    fn using_add_operator() {
        assert_eq!(
            NaiveDate::from_ymd_opt(2023, 2, 28).unwrap(),
            NaiveDate::from_ymd_opt(2020, 2, 28).unwrap() + Years::new(3)
        );
    }

    #[test]
    fn checked_subtracting_years() {
        assert_eq!(
            NaiveDate::from_ymd_opt(2017, 2, 28).unwrap(),
            NaiveDate::from_ymd_opt(2020, 2, 28).unwrap().checked_sub_years(Years::new(3)).unwrap()
        );
    }

    #[test]
    fn using_sub_operator() {
        assert_eq!(
            NaiveDate::from_ymd_opt(2017, 2, 28).unwrap(),
            NaiveDate::from_ymd_opt(2020, 2, 28).unwrap() - Years::new(3)
        );
    }
}
