use core::{
    fmt::{self, Debug},
    iter::FusedIterator,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Index, Not},
};

use crate::Weekday;

/// A collection of `Weekday`s stored as a single byte.
///
/// This type is `Copy` and provides efficient set-like and slice-like operations.
/// Many operations are `const` as well.
///
/// Implemented as a bitmask where bits 1-7 correspond to Monday-Sunday.
#[derive(Clone, Copy, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Weekdays(
    // Invariant: the 8-th bit is always 0.
    u8,
);

/// Print the underlying bitmask, padded to 7 bits.
///
/// # Example
/// ```
/// # use chrono::Weekdays;
/// assert_eq!(format!("{:?}", Weekdays::MON), "Weekdays(0000001)");
/// assert_eq!(format!("{:?}", Weekdays::TUE), "Weekdays(0000010)");
/// assert_eq!(format!("{:?}", Weekdays::ALL), "Weekdays(1111111)");
/// ```
impl Debug for Weekdays {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Weekdays({:0>7b})", self.0)
    }
}
#[cfg(test)]
#[test]
fn debug_prints_8th_bit_if_not_zero() {
    assert_eq!(format!("{:?}", Weekdays(0b1000_0000)), "Weekdays(10000000)");
}

impl Weekdays {
    /// An empty `Weekdays`.
    pub const EMPTY: Self = Self(0b000_0000);
    /// A `Weekdays` containing all seven `Weekday`s.
    pub const ALL: Self = Self(0b111_1111);

    /// A `Weekdays` containing only Monday.
    pub const MON: Self = Self(0b000_0001);
    /// A `Weekdays` containing only Tuesday.
    pub const TUE: Self = Self(0b000_0010);
    /// A `Weekdays` containing only Wednesday.
    pub const WED: Self = Self(0b000_0100);
    /// A `Weekdays` containing only Thursday.
    pub const THU: Self = Self(0b000_1000);
    /// A `Weekdays` containing only Friday.
    pub const FRI: Self = Self(0b001_0000);
    /// A `Weekdays` containing only Saturday.
    pub const SAT: Self = Self(0b010_0000);
    /// A `Weekdays` containing only Sunday.
    pub const SUN: Self = Self(0b100_0000);

    /// Create a `Weekdays` from a bitmask.
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
        Self(bits & 0b111_1111)
    }

    /// Create a `Weekdays` from a single `Weekday`.
    ///
    /// # Example
    /// ```
    /// # use chrono::{Weekday, Weekdays};
    /// assert_eq!(Weekdays::MON, Weekdays::from_one(Weekday::Mon));
    /// ```
    pub const fn from_one(weekday: Weekday) -> Self {
        match weekday {
            Weekday::Mon => Self::MON,
            Weekday::Tue => Self::TUE,
            Weekday::Wed => Self::WED,
            Weekday::Thu => Self::THU,
            Weekday::Fri => Self::FRI,
            Weekday::Sat => Self::SAT,
            Weekday::Sun => Self::SUN,
        }
    }

    /// Returns the number of days in the collection.
    ///
    /// # Example
    /// ```
    /// # use chrono::Weekdays;
    /// assert_eq!(Weekdays::MON.len(), 1);
    /// assert_eq!((Weekdays::MON | Weekdays::WED | Weekdays::FRI).len(), 3);
    /// assert_eq!(Weekdays::ALL.len(), 7);
    /// ```
    pub const fn len(self) -> u8 {
        self.0.count_ones() as u8
    }
    /// Returns `true` if the collection is empty.
    ///
    /// # Example
    /// ```
    /// # use chrono::Weekdays;
    /// assert!(Weekdays::EMPTY.is_empty());
    /// assert!(!Weekdays::MON.is_empty());
    /// ```
    pub const fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Returns `Some(day)` if this collection contains exactly one day.
    ///
    /// Returns `None` otherwise.
    ///
    /// # Example
    /// ```
    /// # use chrono::{Weekday, Weekdays};
    /// assert_eq!(Weekdays::MON.single_day(), Some(Weekday::Mon));
    /// assert_eq!((Weekdays::MON | Weekdays::TUE).single_day(), None);
    /// assert_eq!(Weekdays::EMPTY.single_day(), None);
    /// assert_eq!(Weekdays::ALL.single_day(), None);
    /// ```
    pub const fn single_day(self) -> Option<Weekday> {
        match self {
            Self::MON => Some(Weekday::Mon),
            Self::TUE => Some(Weekday::Tue),
            Self::WED => Some(Weekday::Wed),
            Self::THU => Some(Weekday::Thu),
            Self::FRI => Some(Weekday::Fri),
            Self::SAT => Some(Weekday::Sat),
            Self::SUN => Some(Weekday::Sun),
            _ => None,
        }
    }

    /// Returns `true` if the collection contains the given day.
    ///
    /// # Example
    /// ```
    /// # use chrono::{Weekday, Weekdays};
    /// assert!(Weekdays::MON.contains(Weekday::Mon));
    /// assert!((Weekdays::MON | Weekdays::TUE).contains(Weekday::Tue));
    /// assert!(!Weekdays::MON.contains(Weekday::Tue));
    /// ```
    pub const fn contains(self, day: Weekday) -> bool {
        self.0 & Self::from_one(day).0 != 0
    }

    /// Returns the collection with all days inverted.
    ///
    /// # Example
    /// ```
    /// # use chrono::Weekdays;
    /// assert_eq!(Weekdays::MON.inverse(), Weekdays::ALL & !Weekdays::MON);
    /// assert_eq!(Weekdays::ALL.inverse(), Weekdays::EMPTY);
    /// assert_eq!(Weekdays::EMPTY.inverse(), Weekdays::ALL);
    /// ```
    pub const fn inverse(self) -> Self {
        Self(self.0 ^ 0b0111_1111)
    }

    /// Returns days that are in both `self` and `other`.
    ///
    /// # Example
    /// ```
    /// # use chrono::Weekdays;
    /// assert_eq!(Weekdays::MON.intersection(Weekdays::MON), Weekdays::MON);
    /// assert_eq!(Weekdays::MON.intersection(Weekdays::TUE), Weekdays::EMPTY);
    /// assert_eq!(Weekdays::ALL.intersection(Weekdays::MON), Weekdays::MON);
    /// assert_eq!(Weekdays::ALL.intersection(Weekdays::EMPTY), Weekdays::EMPTY);
    /// ```
    pub const fn intersection(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    /// Returns days that are in either `self` or `other`.
    ///
    /// # Example
    /// ```
    /// # use chrono::Weekdays;
    /// assert_eq!(Weekdays::MON.union(Weekdays::MON), Weekdays::MON);
    /// assert_eq!(Weekdays::MON.union(Weekdays::TUE), Weekdays::MON | Weekdays::TUE);
    /// assert_eq!(Weekdays::ALL.union(Weekdays::MON), Weekdays::ALL);
    /// assert_eq!(Weekdays::ALL.union(Weekdays::EMPTY), Weekdays::ALL);
    /// ```
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Returns days that are in `self` or `other` but not in both.
    ///
    /// # Example
    /// ```
    /// # use chrono::Weekdays;
    /// assert_eq!(Weekdays::MON.symmetric_difference(Weekdays::MON), Weekdays::EMPTY);
    /// assert_eq!(Weekdays::MON.symmetric_difference(Weekdays::TUE), Weekdays::MON | Weekdays::TUE);
    /// assert_eq!(Weekdays::ALL.symmetric_difference(Weekdays::MON), Weekdays::ALL & !Weekdays::MON);
    /// assert_eq!(Weekdays::ALL.symmetric_difference(Weekdays::EMPTY), Weekdays::ALL);
    /// ```
    pub const fn symmetric_difference(self, other: Self) -> Self {
        Self(self.0 ^ other.0)
    }

    /// Returns days that are in `self` but not in `other`.
    ///
    /// # Example
    /// ```
    /// # use chrono::Weekdays;
    /// assert_eq!(Weekdays::MON.difference(Weekdays::MON), Weekdays::EMPTY);
    /// assert_eq!(Weekdays::MON.difference(Weekdays::TUE), Weekdays::MON);
    /// assert_eq!(Weekdays::EMPTY.difference(Weekdays::MON), Weekdays::EMPTY);
    /// ```
    pub const fn difference(self, other: Self) -> Self {
        Self(self.0 & !other.0)
    }

    /// Adds a day to the collection.
    ///
    /// Returns `true` if the day was new to the collection.
    ///
    /// # Example
    /// ```
    /// # use chrono::{Weekday, Weekdays};
    /// let mut weekdays = Weekdays::MON;
    /// assert!(weekdays.insert(Weekday::Tue));
    /// assert!(!weekdays.insert(Weekday::Tue));
    /// ```
    pub fn insert(&mut self, day: Weekday) -> bool {
        if self.contains(day) {
            false
        } else {
            self.0 |= Self::from_one(day).0;
            true
        }
    }

    /// Removes a day from the collection.
    ///
    /// Returns `true` if the collection did contain the day.
    ///
    /// # Example
    /// ```
    /// # use chrono::{Weekday, Weekdays};
    /// let mut weekdays = Weekdays::MON;
    /// assert!(weekdays.remove(Weekday::Mon));
    /// assert!(!weekdays.remove(Weekday::Mon));
    /// ```
    pub fn remove(&mut self, day: Weekday) -> bool {
        if self.contains(day) {
            self.0 &= !Self::from_one(day).0;
            true
        } else {
            false
        }
    }

    /// Iterate over the `Weekday`s in the collection.
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
    pub const fn iter(self) -> WeekdaysIter {
        WeekdaysIter(self)
    }

    /// Get the first day in the collection, starting from Monday.
    ///
    /// Returns `None` if the collection is empty.
    ///
    /// # Example
    /// ```
    /// # use chrono::{Weekday, Weekdays};
    /// assert_eq!(Weekdays::MON.first(), Some(Weekday::Mon));
    /// assert_eq!(Weekdays::TUE.first(), Some(Weekday::Tue));
    /// assert_eq!(Weekdays::ALL.first(), Some(Weekday::Mon));
    /// assert_eq!(Weekdays::EMPTY.first(), None);
    /// ```
    pub const fn first(self) -> Option<Weekday> {
        if self.is_empty() {
            return None;
        }

        // Find the first non-zero bit.
        let bit = 1 << self.0.trailing_zeros();

        Self(bit).single_day()
    }

    /// Get the last day in the collection, starting from Sunday.
    ///
    /// Returns `None` if the collection is empty.
    ///
    /// # Example
    /// ```
    /// # use chrono::{Weekday, Weekdays};
    /// assert_eq!(Weekdays::MON.last(), Some(Weekday::Mon));
    /// assert_eq!(Weekdays::SUN.last(), Some(Weekday::Sun));
    /// assert_eq!((Weekdays::MON | Weekdays::TUE).last(), Some(Weekday::Tue));
    /// assert_eq!(Weekdays::EMPTY.last(), None);
    /// ```
    pub fn last(self) -> Option<Weekday> {
        if self.is_empty() {
            return None;
        }

        // Find the last non-zero bit.
        let bit = 1 << (7 - self.0.leading_zeros());

        Self(bit).single_day()
    }

    /// Split the collection in two at the given day.
    ///
    /// Returns a tuple `(before, after)`. `before` contains all days starting from Monday
    /// up to but __not__ including `weekday`. `after` contains all days starting from `weekday`
    /// up to and including Sunday.
    ///
    /// # Example
    /// ```
    /// # use chrono::{Weekday, Weekdays};
    /// let weekdays = Weekdays::MON | Weekdays::WED | Weekdays::FRI;
    /// let (before, after) = weekdays.split_at(Weekday::Wed);
    /// assert_eq!(before, Weekdays::MON);
    /// assert_eq!(after, Weekdays::WED | Weekdays::FRI);
    /// ```
    pub const fn split_at(self, weekday: Weekday) -> (Self, Self) {
        let days_after = Self(0b1000_0000 - Self::from_one(weekday).0);
        (self.intersection(days_after.inverse()), self.intersection(days_after))
    }

    /// Iterate over the `Weekday`s in the collection, starting from a given day
    /// and wrapping around from Sunday to Monday.
    ///
    /// # Example
    /// ```
    /// # use chrono::{Weekday, Weekdays};
    /// let weekdays = Weekdays::MON | Weekdays::WED | Weekdays::FRI;
    /// let mut iter = weekdays.iter_from(Weekday::Wed);
    /// assert_eq!(iter.next(), Some(Weekday::Wed));
    /// assert_eq!(iter.next(), Some(Weekday::Fri));
    /// assert_eq!(iter.next(), Some(Weekday::Mon));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub const fn iter_from(self, start: Weekday) -> WeekdaysIterFrom {
        WeekdaysIterFrom { days: self, start }
    }

    /// Iterate over all 128 possible sets, from `EMPTY` to `ALL`.
    pub fn iter_all() -> impl Iterator<Item = Self> {
        (0b0000_0000..0b1000_0000).map(Self)
    }

    /// Panics if the 8-th bit of `self` is not 0.
    #[cfg(test)]
    fn assert_8th_bit_invariant(self) {
        assert!(self.0 & 0b1000_0000 == 0, "the 8-th bit of {self:?} is not 0");
    }
}

/// An iterator over a collection of weekdays.
///
/// See `Weekdays::iter`.
#[derive(Debug, Clone)]
pub struct WeekdaysIter(pub Weekdays);
impl Iterator for WeekdaysIter {
    type Item = Weekday;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0.is_empty() {
            return None;
        }

        let next = self.0.first().expect("the collection is not empty");
        self.0.remove(next);
        Some(next)
    }
}
impl DoubleEndedIterator for WeekdaysIter {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.0.is_empty() {
            return None;
        }

        let next_back = self.0.last().expect("the collection is not empty");
        self.0.remove(next_back);
        Some(next_back)
    }
}
impl ExactSizeIterator for WeekdaysIter {
    fn len(&self) -> usize {
        self.0.len().into()
    }
}
impl FusedIterator for WeekdaysIter {}

/// An iterator over a collection of weekdays, starting from a given day.
///
/// See `Weekdays::iter_from`.
#[derive(Debug, Clone)]
pub struct WeekdaysIterFrom {
    pub days: Weekdays,
    pub start: Weekday,
}
impl Iterator for WeekdaysIterFrom {
    type Item = Weekday;

    fn next(&mut self) -> Option<Self::Item> {
        if self.days.is_empty() {
            return None;
        }

        // Split the collection in two at `start`.
        // Look for the first day among the days after `start` first, including `start` itself.
        // If there are no days after `start`, look for the first day among the days before `start`.
        let (before, after) = self.days.split_at(self.start);
        let days = if after.is_empty() { before } else { after };

        let next = days.first().expect("the collection is not empty");
        self.days.remove(next);
        Some(next)
    }
}
impl DoubleEndedIterator for WeekdaysIterFrom {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.days.is_empty() {
            return None;
        }

        // Split the collection in two at `start`.
        // Look for the last day among the days before `start` first, NOT including `start` itself.
        // If there are no days before `start`, look for the last day among the days after `start`.
        let (before, after) = self.days.split_at(self.start);
        let days = if before.is_empty() { after } else { before };

        let next_back = days.last().expect("the collection is not empty");
        self.days.remove(next_back);
        Some(next_back)
    }
}
impl ExactSizeIterator for WeekdaysIterFrom {
    fn len(&self) -> usize {
        self.days.len().into()
    }
}
impl FusedIterator for WeekdaysIterFrom {}

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
        self.union(rhs)
    }
}
impl BitAnd for Weekdays {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.intersection(rhs)
    }
}
impl BitXor for Weekdays {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.symmetric_difference(rhs)
    }
}
#[cfg(test)]
#[test]
fn bitwise_set_operations_preserve_8th_bit_invariant() {
    for set1 in Weekdays::iter_all() {
        for set2 in Weekdays::iter_all() {
            (set1 | set2).assert_8th_bit_invariant();
            (set1 & set2).assert_8th_bit_invariant();
            (set1 ^ set2).assert_8th_bit_invariant();
        }
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
        self.inverse()
    }
}
#[cfg(test)]
#[test]
fn not_operation_preserves_8th_bit_invariant() {
    for weekdays in Weekdays::iter_all() {
        (!weekdays).assert_8th_bit_invariant();
    }
}

impl From<Weekday> for Weekdays {
    fn from(weekday: Weekday) -> Self {
        Self::from_one(weekday)
    }
}

impl Extend<Weekday> for Weekdays {
    fn extend<T: IntoIterator<Item = Weekday>>(&mut self, iter: T) {
        for weekday in iter {
            self.insert(weekday);
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

/// Can be used to check the presence of a day in the collection.
///
/// # Example
/// ```
/// # use chrono::{Weekday, Weekdays};
/// assert!(Weekdays::MON[Weekday::Mon]);
/// assert!(Weekdays::ALL[Weekday::Mon]);
/// assert!(!Weekdays::EMPTY[Weekday::Mon]);
/// assert!(!Weekdays::TUE[Weekday::Mon]);
/// ```
impl Index<Weekday> for Weekdays {
    type Output = bool;

    fn index(&self, weekday: Weekday) -> &Self::Output {
        if self.contains(weekday) { &true } else { &false }
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
