// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

use Timelike;
use std::ops::{Add, Sub};
use oldtime::Duration;

/// Extension trait for subsecond rounding or truncation to a maximum number
/// of digits. Rounding can be used to decrease the error variance when
/// serializing/persisting to lower precision. Truncation is the default
/// behavior in Chrono display formatting.  Either can be used to guarantee
/// equality (e.g. for testing) when round-tripping through a lower precision
/// format.
pub trait SubSecondRound {
    /// Return a copy rounded to the specified number of subsecond digits. With
    /// 9 or more digits, self is returned unmodified. Halfway values are
    /// rounded up (away from zero).
    fn round(self, digits: u16) -> Self;

    /// Return a copy truncated to the specified number of subsecond
    /// digits. With 9 or more digits, self is returned unmodified.
    fn trunc(self, digits: u16) -> Self;
}

impl<T> SubSecondRound for T
where T: Timelike + Add<Duration, Output=T> + Sub<Duration, Output=T>
{
    fn round(self, digits: u16) -> T {
        let span = span_for_digits(digits);
        let rem = self.nanosecond() % span;
        if rem > 0 {
            let rev = span - rem;
            if rev <= rem {
                self + Duration::nanoseconds(rev.into()) // up
            } else {
                self - Duration::nanoseconds(rem.into()) // down
            }
        } else {
            self // unchanged
        }
    }

    fn trunc(self, digits: u16) -> T {
        let span = span_for_digits(digits);
        let rem = self.nanosecond() % span;
        if rem > 0 {
            self - Duration::nanoseconds(rem.into()) // truncate
        } else {
            self // unchanged
        }
    }
}

// Return the maximum span in nanoseconds for the target number of digits.
fn span_for_digits(digits: u16) -> u32 {
    // fast lookup form of: 10^(9-min(9,digits))
    match digits {
        0 => 1_000_000_000,
        1 =>   100_000_000,
        2 =>    10_000_000,
        3 =>     1_000_000,
        4 =>       100_000,
        5 =>        10_000,
        6 =>         1_000,
        7 =>           100,
        8 =>            10,
        _ =>             1
    }
}

#[cfg(test)]
mod tests {
    use Timelike;
    use offset::{FixedOffset, TimeZone, Utc};
    use super::SubSecondRound;

    #[test]
    fn test_round() {
        let pst = FixedOffset::east(8 * 60 * 60);
        let dt = pst.ymd(2018, 1, 11).and_hms_nano(10, 5, 13, 084_660_684);

        assert_eq!(dt.round(10), dt);
        assert_eq!(dt.round(9), dt);
        assert_eq!(dt.round(8).nanosecond(), 084_660_680);
        assert_eq!(dt.round(7).nanosecond(), 084_660_700);
        assert_eq!(dt.round(6).nanosecond(), 084_661_000);
        assert_eq!(dt.round(5).nanosecond(), 084_660_000);
        assert_eq!(dt.round(4).nanosecond(), 084_700_000);
        assert_eq!(dt.round(3).nanosecond(), 085_000_000);
        assert_eq!(dt.round(2).nanosecond(), 080_000_000);
        assert_eq!(dt.round(1).nanosecond(), 100_000_000);

        assert_eq!(dt.round(0).nanosecond(), 0);
        assert_eq!(dt.round(0).second(), 13);

        let dt = Utc.ymd(2018, 1, 11).and_hms_nano(10, 5, 27, 750_500_000);
        assert_eq!(dt.round(9), dt);
        assert_eq!(dt.round(4), dt);
        assert_eq!(dt.round(3).nanosecond(), 751_000_000);
        assert_eq!(dt.round(2).nanosecond(), 750_000_000);
        assert_eq!(dt.round(1).nanosecond(), 800_000_000);

        assert_eq!(dt.round(0).nanosecond(), 0);
        assert_eq!(dt.round(0).second(), 28);
    }

    #[test]
    fn test_round_leap_nanos() {
        let dt = Utc.ymd(2016, 12, 31).and_hms_nano(23, 59, 59, 1_750_500_000);
        assert_eq!(dt.round(9), dt);
        assert_eq!(dt.round(4), dt);
        assert_eq!(dt.round(2).nanosecond(), 1_750_000_000);
        assert_eq!(dt.round(1).nanosecond(), 1_800_000_000);
        assert_eq!(dt.round(1).second(), 59);

        assert_eq!(dt.round(0).nanosecond(), 0);
        assert_eq!(dt.round(0).second(), 0);
    }

    #[test]
    fn test_trunc() {
        let pst = FixedOffset::east(8 * 60 * 60);
        let dt = pst.ymd(2018, 1, 11).and_hms_nano(10, 5, 13, 084_660_684);

        assert_eq!(dt.trunc(10), dt);
        assert_eq!(dt.trunc(9), dt);
        assert_eq!(dt.trunc(8).nanosecond(), 084_660_680);
        assert_eq!(dt.trunc(7).nanosecond(), 084_660_600);
        assert_eq!(dt.trunc(6).nanosecond(), 084_660_000);
        assert_eq!(dt.trunc(5).nanosecond(), 084_660_000);
        assert_eq!(dt.trunc(4).nanosecond(), 084_600_000);
        assert_eq!(dt.trunc(3).nanosecond(), 084_000_000);
        assert_eq!(dt.trunc(2).nanosecond(), 080_000_000);
        assert_eq!(dt.trunc(1).nanosecond(), 0);

        assert_eq!(dt.trunc(0).nanosecond(), 0);
        assert_eq!(dt.trunc(0).second(), 13);

        let dt = pst.ymd(2018, 1, 11).and_hms_nano(10, 5, 27, 750_500_000);
        assert_eq!(dt.trunc(9), dt);
        assert_eq!(dt.trunc(4), dt);
        assert_eq!(dt.trunc(3).nanosecond(), 750_000_000);
        assert_eq!(dt.trunc(2).nanosecond(), 750_000_000);
        assert_eq!(dt.trunc(1).nanosecond(), 700_000_000);

        assert_eq!(dt.trunc(0).nanosecond(), 0);
        assert_eq!(dt.trunc(0).second(), 27);
    }

    #[test]
    fn test_trunc_leap_nanos() {
        let dt = Utc.ymd(2016, 12, 31).and_hms_nano(23, 59, 59, 1_750_500_000);
        assert_eq!(dt.trunc(9), dt);
        assert_eq!(dt.trunc(4), dt);
        assert_eq!(dt.trunc(2).nanosecond(), 1_750_000_000);
        assert_eq!(dt.trunc(1).nanosecond(), 1_700_000_000);
        assert_eq!(dt.trunc(1).second(), 59);

        assert_eq!(dt.trunc(0).nanosecond(), 1_000_000_000);
        assert_eq!(dt.trunc(0).second(), 59);
    }
}
