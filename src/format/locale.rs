//! Localized weekdays and months

/// WeekdaysList
pub type WeekdaysList = [&'static str; 7];

/// MonthsList
pub type MonthsList = [&'static str; 12];

/// Locale is a locale
#[derive(Debug, Clone, Copy)]
pub struct Locale {
    short_weekdays: WeekdaysList,
    long_weekdays: WeekdaysList,
    short_months: MonthsList,
    long_months: MonthsList,
}

impl Locale {
    /// Creates new locale
    pub fn new(days: Days, months: Months) -> Self {
        Self {
            short_weekdays: days.into_short_array(),
            long_weekdays: days.into_long_array(),
            short_months: months.into_short_array(),
            long_months: months.into_long_array(),
        }
    }

    /// Returns days
    #[inline]
    pub fn short_weekdays(&self) -> &WeekdaysList {
        &self.short_weekdays
    }

    /// Returns months
    #[inline]
    pub fn long_weekdays(&self) -> &WeekdaysList {
        &self.long_weekdays
    }

    /// Returns months
    #[inline]
    pub fn short_months(&self) -> &MonthsList {
        &self.short_months
    }

    /// Returns months
    #[inline]
    pub fn long_months(&self) -> &MonthsList {
        &self.long_months
    }
}

impl Default for Locale {
    fn default() -> Self {
        Self::new(Days::default(), Months::default())
    }
}

/// Days
#[derive(Debug, Clone, Copy)]
pub struct Days {
    monday: Ident,
    tuesday: Ident,
    wednesday: Ident,
    thursday: Ident,
    friday: Ident,
    saturday: Ident,
    sunday: Ident,
}

impl Days {
    /// Into long
    #[inline]
    pub fn into_long_array(self) -> WeekdaysList {
        [
            self.monday.long(),
            self.tuesday.long(),
            self.wednesday.long(),
            self.thursday.long(),
            self.friday.long(),
            self.saturday.long(),
            self.sunday.long(),
        ]
    }

    /// Into short
    #[inline]
    pub fn into_short_array(self) -> WeekdaysList {
        [
            self.monday.short(),
            self.tuesday.short(),
            self.wednesday.short(),
            self.thursday.short(),
            self.friday.short(),
            self.saturday.short(),
            self.sunday.short(),
        ]
    }
}

impl Default for Days {
    fn default() -> Self {
        Self {
            monday: Ident("Monday", "Mon"),
            tuesday: Ident("Tuesday", "Tue"),
            wednesday: Ident("Wednesday", "Wed"),
            thursday: Ident("Thursday", "Thu"),
            friday: Ident("Friday", "Fri"),
            saturday: Ident("Saturday", "Sat"),
            sunday: Ident("Sunday", "Sun"),
        }
    }
}

/// Months
#[derive(Debug, Clone, Copy)]
pub struct Months {
    january: Ident,
    february: Ident,
    march: Ident,
    april: Ident,
    may: Ident,
    june: Ident,
    july: Ident,
    august: Ident,
    september: Ident,
    october: Ident,
    november: Ident,
    december: Ident,
}

impl Months {
    /// Into long
    #[inline]
    pub fn into_long_array(self) -> MonthsList {
        [
            self.january.long(),
            self.february.long(),
            self.march.long(),
            self.april.long(),
            self.may.long(),
            self.june.long(),
            self.july.long(),
            self.august.long(),
            self.september.long(),
            self.october.long(),
            self.november.long(),
            self.december.long(),
        ]
    }

    /// Into short
    #[inline]
    pub fn into_short_array(self) -> MonthsList {
        [
            self.january.short(),
            self.february.short(),
            self.march.short(),
            self.april.short(),
            self.may.short(),
            self.june.short(),
            self.july.short(),
            self.august.short(),
            self.september.short(),
            self.october.short(),
            self.november.short(),
            self.december.short(),
        ]
    }
}

impl Default for Months {
    fn default() -> Self {
        Self {
            january: Ident("January", "Jan"),
            february: Ident("February", "Feb"),
            march: Ident("March", "Mar"),
            april: Ident("April", "Apr"),
            may: Ident("May", "May"),
            june: Ident("June", "Jun"),
            july: Ident("July", "Jul"),
            august: Ident("August", "Aug"),
            september: Ident("September", "Sep"),
            october: Ident("October", "Oct"),
            november: Ident("November", "Nov"),
            december: Ident("December", "Dec"),
        }
    }
}

/// Identifier
#[derive(Debug, Clone, Copy)]
pub struct Ident(&'static str, &'static str);

impl Ident {
    /// Returns long
    #[inline]
    pub fn long(self) -> &'static str {
        self.0
    }

    /// Returns short
    #[inline]
    pub fn short(self) -> &'static str {
        self.1
    }
}
