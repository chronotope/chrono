#![allow(dead_code, unreachable_pub)]

use crate::offset::FixedOffset;
use crate::Days;
use crate::Months;
use crate::NaiveDateTime;
use crate::ParseResult;
use crate::TimeDelta;
use crate::Utc;

// when using fixed offsets, can just call this `DateTime`, in other cases, have to provide the type parameter.
#[derive(Clone, Copy)]
pub struct DateTime<O = FixedOffset>
where
    O: Offset,
{
    datetime: NaiveDateTime,
    offset: O,
}

pub trait Offset {
    fn fix(&self) -> FixedOffset;
    fn name(&self) -> Option<&str>;
}

impl Offset for FixedOffset {
    fn fix(&self) -> FixedOffset {
        *self
    }
    fn name(&self) -> Option<&str> {
        None
    }
}

// no add/sub methods, these require the timezone instance
impl<O> DateTime<O>
where
    O: Offset,
{
    fn naive_utc(&self) -> NaiveDateTime {
        self.datetime
    }
    fn fixed(&self) -> DateTime<FixedOffset> {
        DateTime { offset: self.offset.fix(), datetime: self.datetime }
    }
}

// can have add/sub methods and impls here as this doesn't
// require the timezone instance
impl DateTime<FixedOffset> {
    fn add_months(&self, months: Months) -> DateTime {
        let new_datetime = self.naive_utc() + months;
        DateTime { datetime: new_datetime, ..*self }
    }
    fn sub_months(&self, months: Months) -> DateTime {
        let new_datetime = self.naive_utc() - months;
        DateTime { datetime: new_datetime, ..*self }
    }
    fn add_days(&self, days: Days) -> DateTime {
        let new_datetime = self.naive_utc() + days;
        DateTime { datetime: new_datetime, ..*self }
    }
    fn sub_days(&self, days: Days) -> DateTime {
        let new_datetime = self.naive_utc() - days;
        DateTime { datetime: new_datetime, ..*self }
    }
    fn add(&self, duration: TimeDelta) -> DateTime {
        let new_datetime = self.naive_utc() + duration;
        DateTime { datetime: new_datetime, ..*self }
    }
    fn sub(&self, duration: TimeDelta) -> DateTime {
        let new_datetime = self.naive_utc() - duration;
        DateTime { datetime: new_datetime, ..*self }
    }
}

pub struct LocalTransition<O = FixedOffset>
where
    O: Offset,
{
    transition_start: (NaiveDateTime, O),
    transition_end: (NaiveDateTime, O),
}

pub struct Transition<O = FixedOffset>
where
    O: Offset,
{
    at: NaiveDateTime,
    from: O,
    to: O,
}

pub struct ClosestTransitions<O = FixedOffset>
where
    O: Offset,
{
    before: Transition<O>,
    after: Transition<O>,
}

impl Transition {
    fn current_offset(&self) -> FixedOffset {
        self.to
    }
}

pub struct InvalidLocalTimeInfo<O = FixedOffset>
where
    O: Offset,
{
    local_timestamp: NaiveDateTime,
    transition: LocalTransition<O>,
}

// the timezone is used to manage the DateTime, but the datetime never contains the timezone itself
// this is useful as the TimeZone might contain a bunch of information from a parsed tzinfo file
// and so it is useful that the user can control the caching of this
//
// this is also simpler as there is no longer a type parameter needed in the DateTime
//
// object safety is argurably less useful here as the `TimeZone` lives outside the `DateTime`, so
// some of the choices made to enable could be unwound if it is not deemed necessary
//
// This could offer a nice migration path by having `DateTime<Tz = FixedOffset>` and
// calling this trait `TimeZoneManager` or something better
pub trait TimeZoneManager {
    type Offset: Offset;

    fn add_months(&self, dt: DateTime, months: Months) -> DateTime<Self::Offset> {
        let new_datetime = dt.naive_utc() + months;
        DateTime { datetime: new_datetime, offset: self.offset_at(new_datetime) }
    }
    fn sub_months(&self, dt: DateTime, months: Months) -> DateTime<Self::Offset> {
        let new_datetime = dt.naive_utc() - months;
        DateTime { datetime: new_datetime, offset: self.offset_at(new_datetime) }
    }
    fn add_days(&self, dt: DateTime, days: Days) -> DateTime<Self::Offset> {
        let new_datetime = dt.naive_utc() + days;
        DateTime { datetime: new_datetime, offset: self.offset_at(new_datetime) }
    }
    fn sub_days(&self, dt: DateTime, days: Days) -> DateTime<Self::Offset> {
        let new_datetime = dt.naive_utc() - days;
        DateTime { datetime: new_datetime, offset: self.offset_at(new_datetime) }
    }
    fn add(&self, dt: DateTime, duration: TimeDelta) -> DateTime<Self::Offset> {
        let new_datetime = dt.naive_utc() + duration;
        DateTime { datetime: new_datetime, offset: self.offset_at(new_datetime) }
    }
    fn sub(&self, dt: DateTime, duration: TimeDelta) -> DateTime<Self::Offset> {
        let new_datetime = dt.naive_utc() - duration;
        DateTime { datetime: new_datetime, offset: self.offset_at(new_datetime) }
    }

    #[cfg(feature = "clock")]
    fn now(&self) -> DateTime<Self::Offset> {
        let now = Utc::now().naive_utc();
        DateTime { datetime: now, offset: self.offset_at(now) }
    }

    fn offset_at(&self, utc: NaiveDateTime) -> Self::Offset;

    fn offset_at_local(&self, local: NaiveDateTime) -> InvalidLocalTimeInfo;

    // we can likely avoid `from_local_datetime` and `from_utc_datetime` here
    // and point users towards `and_local_timezone()` and `.and_timezone()` instead.

    // potentially the `_transitions` functions should take a `local: bool` parameter
    // as it would be incorrect to implement one but leave the other with the default impl

    // this is not hugely useful as it will just be the
    // previous and next transitions, but it might be nice
    // to expose this in public API what is currently just in `tzinfo`.
    fn closest_transitions(&self, _utc: NaiveDateTime) -> Option<ClosestTransitions<Self::Offset>> {
        None
    }

    // if the local timestamp is valid, then these transitions will each be different
    // if the local timestamp is either ambiguous or invalid, then both fields of the
    // tuple will be the same
    fn closest_transitions_from_local(
        &self,
        _local: NaiveDateTime,
    ) -> Option<ClosestTransitions<Self::Offset>> {
        None
    }

    // to be used in %Z formatting
    fn name(&self) -> Option<&str> {
        None
    }

    fn parse_from_str(
        &self,
        input: &str,
        format: &str,
    ) -> ParseResult<InvalidLocalTimeInfo<Self::Offset>>;
}
