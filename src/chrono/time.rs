/*!
 * ISO 8601 time.
 */

use std::fmt;

/// ISO 8601 time. Allows for the nanosecond precision and optional leap second representation.
#[deriving(Eq, TotalEq, Ord, TotalOrd, Hash)]
pub struct Time {
    priv hour: u8,
    priv min: u8,
    priv sec: u8,
    priv frac: u32,
}

impl Time {
    /// Makes a new `Time` from hour, minute and second.
    ///
    /// Returns `None` on invalid hour, minute and/or second.
    #[inline]
    pub fn from_hms(hour: uint, min: uint, sec: uint) -> Option<Time> {
        Time::from_hms_nano(hour, min, sec, 0)
    }

    /// Makes a new `Time` from hour, minute, second and millisecond.
    /// The millisecond part can exceed 1,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or millisecond.
    #[inline]
    pub fn from_hms_milli(hour: uint, min: uint, sec: uint, milli: uint) -> Option<Time> {
        Time::from_hms_nano(hour, min, sec, milli * 1_000_000)
    }

    /// Makes a new `Time` from hour, minute, second and microsecond.
    /// The microsecond part can exceed 1,000,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or microsecond.
    #[inline]
    pub fn from_hms_micro(hour: uint, min: uint, sec: uint, micro: uint) -> Option<Time> {
        Time::from_hms_nano(hour, min, sec, micro * 1_000)
    }

    /// Makes a new `Time` from hour, minute, second and nanosecond.
    /// The nanosecond part can exceed 1,000,000,000 in order to represent the leap second.
    ///
    /// Returns `None` on invalid hour, minute, second and/or nanosecond.
    pub fn from_hms_nano(hour: uint, min: uint, sec: uint, nano: uint) -> Option<Time> {
        if hour >= 24 || min >= 60 || sec >= 60 || nano >= 2_000_000_000 { return None; }
        Some(Time { hour: hour as u8, min: min as u8, sec: sec as u8, frac: nano as u32 })
    }

    /// Returns the hour number from 0 to 23.
    #[inline]
    pub fn hour(&self) -> uint {
        self.hour as uint
    }

    /// Returns the hour number from 1 to 12 with a boolean flag,
    /// which is false for AM and true for PM.
    #[inline]
    pub fn hour12(&self) -> (bool, uint) {
        let mut hour12 = self.hour % 12;
        if hour12 == 0 { hour12 = 12; }
        (self.hour >= 12, hour12 as uint)
    }

    /// Returns the minute number from 0 to 59.
    #[inline]
    pub fn minute(&self) -> uint {
        self.min as uint
    }

    /// Returns the second number from 0 to 59.
    #[inline]
    pub fn second(&self) -> uint {
        self.sec as uint
    }

    /// Returns the number of nanoseconds since the whole non-leap second.
    /// The range from 1,000,000,000 to 1,999,999,999 represents the leap second.
    #[inline]
    pub fn nanosecond(&self) -> uint {
        self.frac as uint
    }

    /// Makes a new `Time` with the hour number changed.
    ///
    /// Returns `None` when the resulting `Time` would be invalid.
    #[inline]
    pub fn with_hour(&self, hour: uint) -> Option<Time> {
        if hour >= 24 { return None; }
        Some(Time { hour: hour as u8, ..*self })
    }

    /// Makes a new `Time` with the minute number changed.
    ///
    /// Returns `None` when the resulting `Time` would be invalid.
    #[inline]
    pub fn with_minute(&self, min: uint) -> Option<Time> {
        if min >= 60 { return None; }
        Some(Time { min: min as u8, ..*self })
    }

    /// Makes a new `Time` with the second number changed.
    ///
    /// Returns `None` when the resulting `Time` would be invalid.
    #[inline]
    pub fn with_second(&self, sec: uint) -> Option<Time> {
        if sec >= 60 { return None; }
        Some(Time { sec: sec as u8, ..*self })
    }

    /// Makes a new `Time` with nanoseconds since the whole non-leap second changed.
    ///
    /// Returns `None` when the resulting `Time` would be invalid.
    #[inline]
    pub fn with_nanosecond(&self, nano: uint) -> Option<Time> {
        if nano >= 2_000_000_000 { return None; }
        Some(Time { frac: nano as u32, ..*self })
    }

    /// Returns the number of non-leap seconds past the last midnight.
    #[inline]
    pub fn nseconds_from_midnight(&self) -> uint {
        self.hour as uint * 3600 + self.min as uint * 60 + self.sec as uint
    }
}

impl fmt::Show for Time {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (sec, nano) = if self.frac >= 1_000_000_000 {
            (self.sec + 1, self.frac - 1_000_000_000)
        } else {
            (self.sec, self.frac)
        };

        try!(write!(f.buf, "{:02}:{:02}:{:02}", self.hour, self.min, sec));
        if nano == 0 {
            Ok(())
        } else if nano % 1_000_000 == 0 {
            write!(f.buf, ",{:03}", nano / 1_000_000)
        } else if nano % 1_000 == 0 {
            write!(f.buf, ",{:06}", nano / 1_000)
        } else {
            write!(f.buf, ",{:09}", nano)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_time_fmt() {
        assert_eq!(Time::from_hms_milli(23, 59, 59,   999).unwrap().to_str(), ~"23:59:59,999");
        assert_eq!(Time::from_hms_milli(23, 59, 59, 1_000).unwrap().to_str(), ~"23:59:60");
        assert_eq!(Time::from_hms_milli(23, 59, 59, 1_001).unwrap().to_str(), ~"23:59:60,001");
    }
}

