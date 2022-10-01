#![allow(dead_code, unreachable_pub)]

use crate::offset::FixedOffset;
use crate::Days;
use crate::Months;
use crate::NaiveDateTime;
use crate::ParseResult;
use crate::TimeDelta;
use crate::Utc;

// this is nice because it avoids the type paramter.
// alternatively the `TimeZoneManager` could have an assocaited `TimeZone` ZST or equivalent that this is parametized by
#[derive(Clone, Copy)]
pub struct DateTime {
    datetime: NaiveDateTime,
    offset: FixedOffset,
    // could potentially include some information on the timezone name here to allow `%Z` style formatting
}

impl DateTime {
    // keep this out of the `TimeZone` trait to avoid object safety problems
    fn parse_from_str_tz<Tz>(input: &str, format: &str, timezone: &Tz) -> ParseResult<LocalResult>
    where
        Tz: TimeZoneManager,
    {
        todo!()
    }

    fn naive_utc(&self) -> NaiveDateTime {
        self.datetime
    }
}

pub struct LocalTransition {
    transition_start: (NaiveDateTime, FixedOffset),
    transition_end: (NaiveDateTime, FixedOffset),
}

pub struct Transition {
    at: NaiveDateTime,
    from: FixedOffset,
    to: FixedOffset,
}

impl Transition {
    fn current_offset(&self) -> FixedOffset {
        self.to
    }
}

pub struct LocalResult {
    local_timestamp: NaiveDateTime,
    transition: LocalTransition,
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
    fn add_months(&self, dt: DateTime, months: Months) -> DateTime {
        let new_datetime = dt.naive_utc() + months;
        DateTime { datetime: new_datetime, offset: self.offset_at(new_datetime) }
    }
    fn sub_months(&self, dt: DateTime, months: Months) -> DateTime {
        let new_datetime = dt.naive_utc() - months;
        DateTime { datetime: new_datetime, offset: self.offset_at(new_datetime) }
    }
    fn add_days(&self, dt: DateTime, days: Days) -> DateTime {
        let new_datetime = dt.naive_utc() + days;
        DateTime { datetime: new_datetime, offset: self.offset_at(new_datetime) }
    }
    fn sub_days(&self, dt: DateTime, days: Days) -> DateTime {
        let new_datetime = dt.naive_utc() - days;
        DateTime { datetime: new_datetime, offset: self.offset_at(new_datetime) }
    }
    fn add(&self, dt: DateTime, duration: TimeDelta) -> DateTime {
        let new_datetime = dt.naive_utc() + duration;
        DateTime { datetime: new_datetime, offset: self.offset_at(new_datetime) }
    }
    fn sub(&self, dt: DateTime, duration: TimeDelta) -> DateTime {
        let new_datetime = dt.naive_utc() - duration;
        DateTime { datetime: new_datetime, offset: self.offset_at(new_datetime) }
    }

    #[cfg(feature = "clock")]
    fn now(&self) -> DateTime {
        let now = Utc::now().naive_utc();
        DateTime { datetime: now, offset: self.offset_at(now) }
    }

    fn offset_at(&self, utc: NaiveDateTime) -> FixedOffset;

    fn offset_at_local(&self, local: NaiveDateTime) -> LocalResult;

    // we can likely avoid `from_local_datetime` and `from_utc_datetime` here
    // and point users towards `and_local_timezone()` and `.and_timezone()` instead.

    // potentially the `_transitions` functions should take a `local: bool` parameter
    // as it would be incorrect to implement one but leave the other with the default impl

    // this is not hugely useful as it will just be the
    // previous and next transitions, but it might be nice
    // to expose this in public API what is currently just in `tzinfo`.
    fn closest_transitions(&self, utc: NaiveDateTime) -> Option<(Transition, Transition)> {
        None
    }

    // if the local timestamp is valid, then these transitions will each be different
    // if the local timestamp is either ambiguous or invalid, then both fields of the
    // tuple will be the same
    fn closest_transitions_from_local(
        &self,
        local: NaiveDateTime,
    ) -> Option<(Transition, Transition)> {
        None
    }

    // to be used in %Z formatting
    fn name(&self) -> Option<&str> {
        None
    }

    fn parse_from_str(&self, input: &str, format: &str) -> ParseResult<LocalResult>;
}

impl TimeZoneManager for Box<dyn TimeZoneManager> {
    fn add_months(&self, dt: DateTime, months: Months) -> DateTime {
        self.as_ref().add_months(dt, months)
    }
    fn sub_months(&self, dt: DateTime, months: Months) -> DateTime {
        self.as_ref().sub_months(dt, months)
    }
    fn add_days(&self, dt: DateTime, days: Days) -> DateTime {
        self.as_ref().add_days(dt, days)
    }
    fn sub_days(&self, dt: DateTime, days: Days) -> DateTime {
        self.as_ref().sub_days(dt, days)
    }
    fn add(&self, dt: DateTime, duration: TimeDelta) -> DateTime {
        self.as_ref().add(dt, duration)
    }
    fn sub(&self, dt: DateTime, duration: TimeDelta) -> DateTime {
        self.as_ref().sub(dt, duration)
    }

    fn now(&self) -> DateTime {
        self.as_ref().now()
    }

    fn offset_at(&self, utc: NaiveDateTime) -> FixedOffset {
        self.as_ref().offset_at(utc)
    }

    fn offset_at_local(&self, local: NaiveDateTime) -> LocalResult {
        self.as_ref().offset_at_local(local)
    }

    fn closest_transitions(&self, utc: NaiveDateTime) -> Option<(Transition, Transition)> {
        self.as_ref().closest_transitions(utc)
    }

    fn closest_transitions_from_local(
        &self,
        local: NaiveDateTime,
    ) -> Option<(Transition, Transition)> {
        self.as_ref().closest_transitions_from_local(local)
    }

    fn parse_from_str(&self, input: &str, format: &str) -> ParseResult<LocalResult> {
        self.as_ref().parse_from_str(input, format)
    }
}
