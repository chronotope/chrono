use core::{
    fmt,
    iter::FusedIterator,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not},
};

use enumflags2::BitFlags;

use crate::Weekday;

/// A set of `Weekday`s.
#[derive(Debug, Clone, Copy, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Weekdays(BitFlags<InnerWeekday>);

impl Weekdays {
    /// An empty `Weekdays`.
    pub const EMPTY: Self = Self(BitFlags::EMPTY);
    /// A `Weekdays` containing all seven `Weekday`s.
    pub const ALL: Self = Self(BitFlags::ALL);

    /// A `Weekdays` containing only Monday.
    pub const MON: Self = Self::from_bits_truncate(InnerWeekday::Mon as u8);
    /// A `Weekdays` containing only Tuesday.
    pub const TUE: Self = Self::from_bits_truncate(InnerWeekday::Tue as u8);
    /// A `Weekdays` containing only Wednesday.
    pub const WED: Self = Self::from_bits_truncate(InnerWeekday::Wed as u8);
    /// A `Weekdays` containing only Thursday.
    pub const THU: Self = Self::from_bits_truncate(InnerWeekday::Thu as u8);
    /// A `Weekdays` containing only Friday.
    pub const FRI: Self = Self::from_bits_truncate(InnerWeekday::Fri as u8);
    /// A `Weekdays` containing only Saturday.
    pub const SAT: Self = Self::from_bits_truncate(InnerWeekday::Sat as u8);
    /// A `Weekdays` containing only Sunday.
    pub const SUN: Self = Self::from_bits_truncate(InnerWeekday::Sun as u8);

    /// Create a `Weekdays` from a bit pattern.
    ///
    /// If present, the 8-th bit is ignored.
    ///
    /// # Example
    ///
    /// ```
    /// # use chrono::Weekdays;
    /// assert_eq!(Weekdays::EMPTY, Weekdays::from_bits_truncate(0));
    /// assert_eq!(Weekdays::MON, Weekdays::from_bits_truncate(0b1));
    /// assert_eq!(Weekdays::TUE, Weekdays::from_bits_truncate(0b10));
    /// assert_eq!(Weekdays::MON | Weekdays::WED, Weekdays::from_bits_truncate(0b101));
    /// assert_eq!(Weekdays::ALL, Weekdays::from_bits_truncate(0b111_1111));
    /// assert_eq!(Weekdays::MON, Weekdays::from_bits_truncate(0b1000_0001));
    /// ```
    #[must_use]
    pub const fn from_bits_truncate(bits: u8) -> Self {
        Self(BitFlags::<InnerWeekday>::from_bits_truncate_c(
            bits,
            BitFlags::<InnerWeekday>::CONST_TOKEN,
        ))
    }

    /// Returns the number of days in the set.
    pub const fn len(self) -> usize {
        self.0.bits_c().count_ones() as usize
    }
    /// Returns `true` if the set is empty.
    pub const fn is_empty(self) -> bool {
        self.0.bits_c() == 0
    }

    /// Iterate over the `Weekday`s in the set.
    ///
    /// Starting from Monday, in ascending order.
    ///
    /// # Example
    /// ```
    /// # use chrono::{Weekday, Weekdays};
    /// let weekdays = Weekdays::MON | Weekdays::WED | Weekdays::FRI;
    /// let mut iter = weekdays.iter();
    /// assert_eq!(iter.next(), Some(Weekday::Mon));
    /// assert_eq!(iter.next(), Some(Weekday::Wed));
    /// assert_eq!(iter.next(), Some(Weekday::Fri));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(self) -> WeekdaysIter {
        WeekdaysIter(self.0.iter())
    }
}

#[derive(Debug, Clone)]
pub struct WeekdaysIter(enumflags2::Iter<InnerWeekday>);
impl Iterator for WeekdaysIter {
    type Item = Weekday;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Weekday::from)
    }
}
impl ExactSizeIterator for WeekdaysIter {
    fn len(&self) -> usize {
        self.0.len()
    }
}
impl FusedIterator for WeekdaysIter {}

impl fmt::Display for Weekdays {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut iter = self.iter();
        if let Some(first) = iter.next() {
            write!(f, "{first}")?;
            for weekday in iter {
                write!(f, " | {weekday}")?;
            }
            Ok(())
        } else {
            write!(f, "<empty>")
        }
    }
}

// impl Bit* for Weekdays
impl BitOr for Weekdays {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}
impl BitAnd for Weekdays {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}
impl BitXor for Weekdays {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}

// impl Bit*Assign for Weekdays
impl BitOrAssign for Weekdays {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}
impl BitAndAssign for Weekdays {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}
impl BitXorAssign for Weekdays {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0;
    }
}

impl Not for Weekdays {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

#[enumflags2::bitflags]
#[repr(u8)]
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum InnerWeekday {
    Mon = 1 << Weekday::Mon as u8,
    Tue = 1 << Weekday::Tue as u8,
    Wed = 1 << Weekday::Wed as u8,
    Thu = 1 << Weekday::Thu as u8,
    Fri = 1 << Weekday::Fri as u8,
    Sat = 1 << Weekday::Sat as u8,
    Sun = 1 << Weekday::Sun as u8,
}

impl From<Weekday> for InnerWeekday {
    fn from(weekday: Weekday) -> Self {
        match weekday {
            Weekday::Mon => Self::Mon,
            Weekday::Tue => Self::Tue,
            Weekday::Wed => Self::Wed,
            Weekday::Thu => Self::Thu,
            Weekday::Fri => Self::Fri,
            Weekday::Sat => Self::Sat,
            Weekday::Sun => Self::Sun,
        }
    }
}
impl From<InnerWeekday> for Weekday {
    fn from(value: InnerWeekday) -> Self {
        match value {
            InnerWeekday::Mon => Self::Mon,
            InnerWeekday::Tue => Self::Tue,
            InnerWeekday::Wed => Self::Wed,
            InnerWeekday::Thu => Self::Thu,
            InnerWeekday::Fri => Self::Fri,
            InnerWeekday::Sat => Self::Sat,
            InnerWeekday::Sun => Self::Sun,
        }
    }
}

impl From<Weekday> for Weekdays {
    fn from(weekday: Weekday) -> Self {
        Weekdays(InnerWeekday::from(weekday).into())
    }
}
impl Extend<Weekday> for Weekdays {
    fn extend<T: IntoIterator<Item = Weekday>>(&mut self, iter: T) {
        for weekday in iter {
            self.0.insert(InnerWeekday::from(weekday));
        }
    }
}
impl FromIterator<Weekday> for Weekdays {
    fn from_iter<T: IntoIterator<Item = Weekday>>(iter: T) -> Self {
        let mut weekdays = Self::EMPTY;
        weekdays.extend(iter);
        weekdays
    }
}

impl IntoIterator for Weekdays {
    type Item = Weekday;
    type IntoIter = WeekdaysIter;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

// impl Bit*<Weekday> for Weekdays
impl BitOr<Weekday> for Weekdays {
    type Output = Self;

    fn bitor(self, rhs: Weekday) -> Self::Output {
        self | Self::from(rhs)
    }
}
impl BitAnd<Weekday> for Weekdays {
    type Output = Self;

    fn bitand(self, rhs: Weekday) -> Self::Output {
        self & Self::from(rhs)
    }
}
impl BitXor<Weekday> for Weekdays {
    type Output = Self;

    fn bitxor(self, rhs: Weekday) -> Self::Output {
        self ^ Self::from(rhs)
    }
}

// impl Bit*<Weekdays> for Weekday
impl BitOr<Weekdays> for Weekday {
    type Output = Weekdays;

    fn bitor(self, rhs: Weekdays) -> Self::Output {
        Weekdays::from(self) | rhs
    }
}
impl BitAnd<Weekdays> for Weekday {
    type Output = Weekdays;

    fn bitand(self, rhs: Weekdays) -> Self::Output {
        Weekdays::from(self) & rhs
    }
}
impl BitXor<Weekdays> for Weekday {
    type Output = Weekdays;

    fn bitxor(self, rhs: Weekdays) -> Self::Output {
        Weekdays::from(self) ^ rhs
    }
}

// impl Bit*Assign<Weekday> for Weekdays
impl BitOrAssign<Weekday> for Weekdays {
    fn bitor_assign(&mut self, rhs: Weekday) {
        *self |= Self::from(rhs);
    }
}
impl BitAndAssign<Weekday> for Weekdays {
    fn bitand_assign(&mut self, rhs: Weekday) {
        *self &= Self::from(rhs);
    }
}
impl BitXorAssign<Weekday> for Weekdays {
    fn bitxor_assign(&mut self, rhs: Weekday) {
        *self ^= Self::from(rhs);
    }
}

// impl Bit* for Weekday
impl BitOr for Weekday {
    type Output = Weekdays;

    fn bitor(self, rhs: Self) -> Self::Output {
        Weekdays::from(self) | Weekdays::from(rhs)
    }
}
impl BitAnd for Weekday {
    type Output = Weekdays;

    fn bitand(self, rhs: Self) -> Self::Output {
        Weekdays::from(self) & Weekdays::from(rhs)
    }
}
impl BitXor for Weekday {
    type Output = Weekdays;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Weekdays::from(self) ^ Weekdays::from(rhs)
    }
}

impl Not for Weekday {
    type Output = Weekdays;

    fn not(self) -> Self::Output {
        !Weekdays::from(self)
    }
}
