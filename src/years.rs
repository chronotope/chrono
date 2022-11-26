// I usually develop with this clippy flags
// but I can remove once the this module is done
#![warn(clippy::all,
/*#![warn(*/clippy::pedantic,
		clippy::perf,
        clippy::nursery,
        // clippy::cargo,
        clippy::unwrap_used,
        clippy::expect_used)]

use num_integer::Integer;

use super::{datetime::DateTime, NaiveDate, NaiveDateTime};
use crate::traits::Datelike;
use crate::TimeZone;

struct Years(u32); // I believe the fields of the struct should be private

impl Years {
    fn new(num_years: u32) -> Years {
        Self(num_years)
    }
}

// would to the same for all the others
impl<Tz: TimeZone> DateTime<Tz> {
    pub fn checked_add_years(self, num_years: Years) -> Option<DateTime<Tz>> {}

    pub fn checked_sub_years(self, num_years: Years) -> Option<DateTime<Tz>> {}
}

impl NaiveDateTime {
    pub fn checked_add_years(self, num_years: Years) -> Option<NaiveDateTime> {}

    pub fn checked_sub_years(self, num_years: Years) -> Option<NaiveDateTime> {}
}

// think about a better logic to use `checked_add`
// currently trying to finish a simple implementation
// is it ok to assum it'll only receive positive numbers? I think so
fn get_current_or_next_leap_year(year: u32) -> u32 {
    if !year.is_even() {
        year += 1;
    }
    while !is_leap_year(year) {
        year += 1;
    }
    year
}

// almost surely there is a more precise way to implement this
fn is_leap_year(year: i32) -> bool {
    if (year % 4) == 0 {
        if (year % 100) != 0 {
            true
        } else {
            // if divisible by 100 but also divisible by 400 than is leap year
            (year % 400) == 0
        }
    } else {
        false
    }
}

impl NaiveDate {
    pub fn checked_add_years(self, years: Years) -> Option<NaiveDate> {
        if years.0 == 0 {
            return Some(self);
        }
        let current_year = self.year();
        let current_month = self.month();
        let next_leap_year = get_current_or_next_leap_year(current_year);
        let total_amount_of_days;
        if years.0 < (next_leap_year - current_year) {
            total_amount_of_days = years.0 * 365;
            //use this to transform a years addition into the proper addition of days
            // not sure this is the best implementation
            // but seems robust since it would rely on the top level implementation
        }
    }

    pub fn checked_sub_years(self, num_years: Years) -> Option<NaiveDate> {}
}

// impl Add<Years> for NaiveDate {}
//
// impl Add<Years> for NaiveDateTime {}
//
// impl Add<Years, Tz: TimeZone> for DateTime<Tz> {}
//
// impl Sub<Years> For NaiveDate {}
//
// impl Sub<Years> for NaiveDateTime {}
//
// impl Sub<Years, Tz: TimeZone> For DateTime<Tz> {}

#[cfg(test)]
mod tests {
    use super::is_leap_year;

    #[test]
    fn not_leap_year() {
        assert!(is_leap_year(2022) == false)
    }

    #[test]
    fn leap_year() {
        assert!(is_leap_year(2020) == true)
    }

    #[test]
    fn leap_year_mod_400() {
        assert!(is_leap_year(2400) == true);
    }
}
