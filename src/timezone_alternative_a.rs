#![allow(dead_code, unreachable_pub)]

use crate::offset::FixedOffset;
use crate::NaiveDateTime;
use crate::ParseResult;
use crate::TimeDelta;
use crate::Utc;

pub struct DateTime<Tz: TimeZoneA> {
    datetime: NaiveDateTime,
    zone: Tz,
}

impl<Tz> DateTime<Tz>
where
    Tz: TimeZoneA + Clone,
{
    // keep this out of the `TimeZone` trait to avoid object safety problems
    fn parse_from_str_tz(
        input: &str,
        format: &str,
        timezone: &Tz,
    ) -> ParseResult<Result<DateTime<Tz>, InvalidLocalTimeInfoTz<Tz>>> {
        todo!()
    }
}

impl NaiveDateTime {
    fn and_local_timezone_2<Tz>(
        self,
        timezone: &Tz,
    ) -> Result<DateTime<Tz>, InvalidLocalTimeInfoTz<Tz>>
    where
        Tz: TimeZoneA + Clone,
    {
        match timezone.offset_at_local(self) {
            Ok(offset) => Ok(DateTime { datetime: self - offset, zone: timezone.clone() }),
            Err(e) => Err(InvalidLocalTimeInfoTz {
                local: e.local,
                transition: e.transition,
                tz: timezone.clone(),
            }),
        }
    }

    fn and_timezone_2<Tz>(self, timezone: &Tz) -> DateTime<Tz>
    where
        Tz: TimeZoneA + Clone,
    {
        DateTime { datetime: self, zone: timezone.clone() }
    }
}

impl<Tz> Clone for DateTime<Tz>
where
    Tz: TimeZoneA + Clone,
{
    fn clone(&self) -> Self {
        DateTime { datetime: self.datetime, zone: self.zone.clone() }
    }
}

impl<Tz> Copy for DateTime<Tz> where Tz: TimeZoneA + Copy {}

#[derive(Clone, PartialEq, Eq)]
pub struct Transition {
    at: NaiveDateTime,
    from: FixedOffset,
    to: FixedOffset,
}

impl Transition {
    fn current_offset(&self) -> FixedOffset {
        self.to
    }
    fn local_start(&self) -> NaiveDateTime {
        self.at + self.from
    }
    fn local_end(&self) -> NaiveDateTime {
        self.at + self.to
    }
}

pub struct InvalidLocalTimeInfo {
    local: NaiveDateTime,
    transition: Transition,
}

pub struct InvalidLocalTimeInfoTz<Tz> {
    local: NaiveDateTime,
    transition: Transition,
    tz: Tz,
}

// here the TimeZoneA should be something small or static, like an empty enum variant or an empty struct.
// potentially all the methods here should be fallible
//
// the implementor of TimeZoneA will usually store its current offset internally (if dynamic) or make it available as a
// const if static.
//
// where the TimeZoneA implemention handles daylight savings or other timezone that needs more data than just an offset
// it might store a `String` or enum variant which enables the `%Z` formatting, extracted via the `.name()` method.
//
// we move the `datetime_from_str` to the `DateTime<Tz>` impl
// we have to avoid `from_local_datetime` and `from_utc_datetime` here
// and point users towards `and_local_timezone()` and `.and_timezone()` instead.
// because there is no way to force the `TimeZoneA` to implement `Clone` but still keep object safety.
// for all practical purposes all `TimeZoneA` implementors should probably implement at least `Clone` and likely `Copy` as well.
pub trait TimeZoneA {
    // this could have a default implementation if there was a `from_fixed_offset` method
    // in the trait, but that would be problematic for object safety, so instead
    // the implemention is left to the user.
    #[cfg(feature = "clock")]
    fn offset_now(&self) -> FixedOffset {
        self.offset_at(Utc::now().naive_utc())
    }

    fn offset(&self) -> FixedOffset;

    fn offset_at_local(&self, local: NaiveDateTime) -> Result<FixedOffset, InvalidLocalTimeInfo> {
        match self.closest_transitions_from_local(local) {
            None => Ok(self.offset()),
            Some((previous, next)) if previous == next => {
                Err(InvalidLocalTimeInfo { local, transition: previous })
            }
            Some((previous, _)) => Ok(previous.to),
        }
    }

    fn offset_at(&self, utc: NaiveDateTime) -> FixedOffset {
        if let Some((from, _)) = self.closest_transitions(utc) {
            from.current_offset()
        } else {
            self.offset()
        }
    }

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
}

impl TimeZoneA for Box<dyn TimeZoneA> {
    fn offset_now(&self) -> FixedOffset {
        self.as_ref().offset_now()
    }

    fn offset(&self) -> FixedOffset {
        self.as_ref().offset()
    }

    fn offset_at_local(&self, local: NaiveDateTime) -> Result<FixedOffset, InvalidLocalTimeInfo>
    where
        Self: Sized,
    {
        self.as_ref().offset_at_local(local)
    }

    fn offset_at(&self, utc: NaiveDateTime) -> FixedOffset {
        self.as_ref().offset_at(utc)
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

    fn name(&self) -> Option<&str> {
        self.as_ref().name()
    }
}
