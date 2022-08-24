use std::cmp::Ordering;

use super::rule::RuleDay;
use super::timezone::LocalTimeType;
use super::{
    CUMUL_DAYS_IN_MONTHS_LEAP_YEAR, CUMUL_DAYS_IN_MONTHS_NORMAL_YEAR, DAYS_IN_MONTHS_NORMAL_YEAR,
    DAYS_PER_WEEK, MONTHS_PER_YEAR, SECONDS_PER_DAY, SECONDS_PER_LEAP_YEAR,
    SECONDS_PER_NORMAL_YEAR,
};

/// Informations needed for checking DST transition rules consistency, for a Julian day
#[derive(Debug, PartialEq, Eq)]
struct JulianDayCheckInfos {
    /// Offset in seconds from the start of a normal year
    start_normal_year_offset: i64,
    /// Offset in seconds from the end of a normal year
    end_normal_year_offset: i64,
    /// Offset in seconds from the start of a leap year
    start_leap_year_offset: i64,
    /// Offset in seconds from the end of a leap year
    end_leap_year_offset: i64,
}

impl JulianDayCheckInfos {
    /// Compute the informations needed for checking DST transition rules consistency, for a Julian day in `[1, 365]`
    fn from_julian_1(julian_day_1: u16, utc_day_time: i64) -> Self {
        let start_normal_year_offset = (julian_day_1 as i64 - 1) * SECONDS_PER_DAY + utc_day_time;
        let start_leap_year_offset = if julian_day_1 <= 59 {
            start_normal_year_offset
        } else {
            start_normal_year_offset + SECONDS_PER_DAY
        };

        JulianDayCheckInfos {
            start_normal_year_offset,
            end_normal_year_offset: start_normal_year_offset - SECONDS_PER_NORMAL_YEAR,
            start_leap_year_offset,
            end_leap_year_offset: start_leap_year_offset - SECONDS_PER_LEAP_YEAR,
        }
    }

    /// Compute the informations needed for checking DST transition rules consistency, for a zero-based Julian day in `[0, 365]`
    fn from_julian_0(julian_day_0: u16, utc_day_time: i64) -> Self {
        let start_year_offset = julian_day_0 as i64 * SECONDS_PER_DAY + utc_day_time;

        JulianDayCheckInfos {
            start_normal_year_offset: start_year_offset,
            end_normal_year_offset: start_year_offset - SECONDS_PER_NORMAL_YEAR,
            start_leap_year_offset: start_year_offset,
            end_leap_year_offset: start_year_offset - SECONDS_PER_LEAP_YEAR,
        }
    }
}

/// Informations needed for checking DST transition rules consistency, for a day represented by a month, a month week and a week day
#[derive(Debug, PartialEq, Eq)]
struct MonthWeekDayCheckInfos {
    /// Possible offset range in seconds from the start of a normal year
    start_normal_year_offset_range: (i64, i64),
    /// Possible offset range in seconds from the end of a normal year
    end_normal_year_offset_range: (i64, i64),
    /// Possible offset range in seconds from the start of a leap year
    start_leap_year_offset_range: (i64, i64),
    /// Possible offset range in seconds from the end of a leap year
    end_leap_year_offset_range: (i64, i64),
}

impl MonthWeekDayCheckInfos {
    /// Compute the informations needed for checking DST transition rules consistency, for a day represented by a month, a month week and a week day
    fn from_month_weekday(month: u8, week: u8, utc_day_time: i64) -> Self {
        let month = month as usize;
        let week = week as i64;

        let (normal_year_month_day_range, leap_year_month_day_range) = {
            if week == 5 {
                let normal_year_days_in_month = DAYS_IN_MONTHS_NORMAL_YEAR[month - 1];
                let leap_year_days_in_month = if month == 2 {
                    normal_year_days_in_month + 1
                } else {
                    normal_year_days_in_month
                };

                let normal_year_month_day_range =
                    (normal_year_days_in_month - 7, normal_year_days_in_month - 1);

                let leap_year_month_day_range =
                    (leap_year_days_in_month - 7, leap_year_days_in_month - 1);

                (normal_year_month_day_range, leap_year_month_day_range)
            } else {
                let month_day_range = (week * DAYS_PER_WEEK - 7, week * DAYS_PER_WEEK - 1);
                (month_day_range, month_day_range)
            }
        };

        let cumul_normal_year = CUMUL_DAYS_IN_MONTHS_NORMAL_YEAR[month - 1];
        let start_normal_year_offset_range = (
            (cumul_normal_year + normal_year_month_day_range.0) * SECONDS_PER_DAY + utc_day_time,
            (cumul_normal_year + normal_year_month_day_range.1) * SECONDS_PER_DAY + utc_day_time,
        );

        let cumul_leap_year = CUMUL_DAYS_IN_MONTHS_LEAP_YEAR[month - 1];
        let start_leap_year_offset_range = (
            (cumul_leap_year + leap_year_month_day_range.0) * SECONDS_PER_DAY + utc_day_time,
            (cumul_leap_year + leap_year_month_day_range.1) * SECONDS_PER_DAY + utc_day_time,
        );

        MonthWeekDayCheckInfos {
            start_normal_year_offset_range,
            end_normal_year_offset_range: (
                start_normal_year_offset_range.0 - SECONDS_PER_NORMAL_YEAR,
                start_normal_year_offset_range.1 - SECONDS_PER_NORMAL_YEAR,
            ),
            start_leap_year_offset_range,
            end_leap_year_offset_range: (
                start_leap_year_offset_range.0 - SECONDS_PER_LEAP_YEAR,
                start_leap_year_offset_range.1 - SECONDS_PER_LEAP_YEAR,
            ),
        }
    }
}

/// Check DST transition rules consistency, which ensures that the DST start and end time are always in the same order.
///
/// This prevents from having an additional transition at the year boundary, when the order of DST start and end time is different on consecutive years.
///
pub(super) fn check_dst_transition_rules_consistency(
    std: &LocalTimeType,
    dst: &LocalTimeType,
    dst_start: RuleDay,
    dst_start_time: i32,
    dst_end: RuleDay,
    dst_end_time: i32,
) -> bool {
    // Overflow is not possible
    let dst_start_time_in_utc = dst_start_time as i64 - std.ut_offset as i64;
    let dst_end_time_in_utc = dst_end_time as i64 - dst.ut_offset as i64;

    match (dst_start, dst_end) {
        (RuleDay::Julian1WithoutLeap(start_day), RuleDay::Julian1WithoutLeap(end_day)) => {
            check_two_julian_days(
                JulianDayCheckInfos::from_julian_1(start_day, dst_start_time_in_utc),
                JulianDayCheckInfos::from_julian_1(end_day, dst_end_time_in_utc),
            )
        }
        (RuleDay::Julian1WithoutLeap(start_day), RuleDay::Julian0WithLeap(end_day)) => {
            check_two_julian_days(
                JulianDayCheckInfos::from_julian_1(start_day, dst_start_time_in_utc),
                JulianDayCheckInfos::from_julian_0(end_day, dst_end_time_in_utc),
            )
        }
        (RuleDay::Julian0WithLeap(start_day), RuleDay::Julian1WithoutLeap(end_day)) => {
            check_two_julian_days(
                JulianDayCheckInfos::from_julian_0(start_day, dst_start_time_in_utc),
                JulianDayCheckInfos::from_julian_1(end_day, dst_end_time_in_utc),
            )
        }
        (RuleDay::Julian0WithLeap(start_day), RuleDay::Julian0WithLeap(end_day)) => {
            check_two_julian_days(
                JulianDayCheckInfos::from_julian_0(start_day, dst_start_time_in_utc),
                JulianDayCheckInfos::from_julian_0(end_day, dst_end_time_in_utc),
            )
        }
        (
            RuleDay::Julian1WithoutLeap(start_day),
            RuleDay::MonthWeekday { month: end_month, week: end_week, .. },
        ) => check_month_week_day_and_julian_day(
            MonthWeekDayCheckInfos::from_month_weekday(end_month, end_week, dst_end_time_in_utc),
            JulianDayCheckInfos::from_julian_1(start_day, dst_start_time_in_utc),
        ),
        (
            RuleDay::Julian0WithLeap(start_day),
            RuleDay::MonthWeekday { month: end_month, week: end_week, .. },
        ) => check_month_week_day_and_julian_day(
            MonthWeekDayCheckInfos::from_month_weekday(end_month, end_week, dst_end_time_in_utc),
            JulianDayCheckInfos::from_julian_0(start_day, dst_start_time_in_utc),
        ),
        (
            RuleDay::MonthWeekday { month: start_month, week: start_week, .. },
            RuleDay::Julian1WithoutLeap(end_day),
        ) => check_month_week_day_and_julian_day(
            MonthWeekDayCheckInfos::from_month_weekday(
                start_month,
                start_week,
                dst_start_time_in_utc,
            ),
            JulianDayCheckInfos::from_julian_1(end_day, dst_end_time_in_utc),
        ),
        (
            RuleDay::MonthWeekday { month: start_month, week: start_week, .. },
            RuleDay::Julian0WithLeap(end_day),
        ) => check_month_week_day_and_julian_day(
            MonthWeekDayCheckInfos::from_month_weekday(
                start_month,
                start_week,
                dst_start_time_in_utc,
            ),
            JulianDayCheckInfos::from_julian_0(end_day, dst_end_time_in_utc),
        ),
        (
            RuleDay::MonthWeekday {
                month: start_month,
                week: start_week,
                week_day: start_week_day,
            },
            RuleDay::MonthWeekday { month: end_month, week: end_week, week_day: end_week_day },
        ) => check_two_month_week_days(
            (start_month, start_week, start_week_day),
            dst_start_time_in_utc,
            (end_month, end_week, end_week_day),
            dst_end_time_in_utc,
        ),
    }
}

/// Check DST transition rules consistency for two Julian days
fn check_two_julian_days(
    check_infos_1: JulianDayCheckInfos,
    check_infos_2: JulianDayCheckInfos,
) -> bool {
    // Check in same year
    let (before, after) = if check_infos_1.start_normal_year_offset
        <= check_infos_2.start_normal_year_offset
        && check_infos_1.start_leap_year_offset <= check_infos_2.start_leap_year_offset
    {
        (&check_infos_1, &check_infos_2)
    } else if check_infos_2.start_normal_year_offset <= check_infos_1.start_normal_year_offset
        && check_infos_2.start_leap_year_offset <= check_infos_1.start_leap_year_offset
    {
        (&check_infos_2, &check_infos_1)
    } else {
        return false;
    };

    // Check in consecutive years
    if after.end_normal_year_offset <= before.start_normal_year_offset
        && after.end_normal_year_offset <= before.start_leap_year_offset
        && after.end_leap_year_offset <= before.start_normal_year_offset
    {
        return true;
    }

    if before.start_normal_year_offset <= after.end_normal_year_offset
        && before.start_leap_year_offset <= after.end_normal_year_offset
        && before.start_normal_year_offset <= after.end_leap_year_offset
    {
        return true;
    }

    false
}

/// Check DST transition rules consistency for a Julian day and a day represented by a month, a month week and a week day
fn check_month_week_day_and_julian_day(
    check_infos_1: MonthWeekDayCheckInfos,
    check_infos_2: JulianDayCheckInfos,
) -> bool {
    // Check in same year, then in consecutive years
    if check_infos_2.start_normal_year_offset <= check_infos_1.start_normal_year_offset_range.0
        && check_infos_2.start_leap_year_offset <= check_infos_1.start_leap_year_offset_range.0
    {
        let (before, after) = (&check_infos_2, &check_infos_1);

        if after.end_normal_year_offset_range.1 <= before.start_normal_year_offset
            && after.end_normal_year_offset_range.1 <= before.start_leap_year_offset
            && after.end_leap_year_offset_range.1 <= before.start_normal_year_offset
        {
            return true;
        };

        if before.start_normal_year_offset <= after.end_normal_year_offset_range.0
            && before.start_leap_year_offset <= after.end_normal_year_offset_range.0
            && before.start_normal_year_offset <= after.end_leap_year_offset_range.0
        {
            return true;
        };

        return false;
    }

    if check_infos_1.start_normal_year_offset_range.1 <= check_infos_2.start_normal_year_offset
        && check_infos_1.start_leap_year_offset_range.1 <= check_infos_2.start_leap_year_offset
    {
        let (before, after) = (&check_infos_1, &check_infos_2);

        if after.end_normal_year_offset <= before.start_normal_year_offset_range.0
            && after.end_normal_year_offset <= before.start_leap_year_offset_range.0
            && after.end_leap_year_offset <= before.start_normal_year_offset_range.0
        {
            return true;
        }

        if before.start_normal_year_offset_range.1 <= after.end_normal_year_offset
            && before.start_leap_year_offset_range.1 <= after.end_normal_year_offset
            && before.start_normal_year_offset_range.1 <= after.end_leap_year_offset
        {
            return true;
        }

        return false;
    }

    false
}

/// Check DST transition rules consistency for two days represented by a month, a month week and a week day
fn check_two_month_week_days(
    month_week_day_1: (u8, u8, u8),
    utc_day_time_1: i64,
    month_week_day_2: (u8, u8, u8),
    utc_day_time_2: i64,
) -> bool {
    let (month_1, week_1, _) = month_week_day_1;
    let (month_2, week_2, _) = month_week_day_2;

    // Sort rule days
    let (month_week_day_before, utc_day_time_before, month_week_day_after, utc_day_time_after) = {
        let rem = (month_2 as i64 - month_1 as i64).rem_euclid(MONTHS_PER_YEAR);

        if rem == 0 {
            if week_1 <= week_2 {
                (month_week_day_1, utc_day_time_1, month_week_day_2, utc_day_time_2)
            } else {
                (month_week_day_2, utc_day_time_2, month_week_day_1, utc_day_time_1)
            }
        } else if rem == 1 {
            (month_week_day_1, utc_day_time_1, month_week_day_2, utc_day_time_2)
        } else if rem == MONTHS_PER_YEAR - 1 {
            (month_week_day_2, utc_day_time_2, month_week_day_1, utc_day_time_1)
        } else {
            // Months are not equal or consecutive, so rule days are separated by more than 3 weeks and cannot swap their order
            return true;
        }
    };

    let month_before = month_week_day_before.0 as usize;
    let week_before = month_week_day_before.1 as i64;
    let week_day_before = month_week_day_before.2 as i64;

    let month_after = month_week_day_after.0 as usize;
    let week_after = month_week_day_after.1 as i64;
    let week_day_after = month_week_day_after.2 as i64;

    let (diff_days_min, diff_days_max) = if week_day_before == week_day_after {
        // Rule days are separated by a whole number of weeks
        let (diff_week_min, diff_week_max) = match (week_before, week_after) {
            // All months have more than 29 days on a leap year, so the 5th week is non-empty
            (1..=4, 5) if month_before == month_after => (4 - week_before, 5 - week_before),
            (1..=4, 1..=4) if month_before != month_after => {
                (4 - week_before + week_after, 5 - week_before + week_after)
            }
            _ => return true, // rule days are synchronized or separated by more than 3 weeks
        };

        (diff_week_min * DAYS_PER_WEEK, diff_week_max * DAYS_PER_WEEK)
    } else {
        // week_day_before != week_day_after
        let n = (week_day_after - week_day_before).rem_euclid(DAYS_PER_WEEK); // n >= 1

        if month_before == month_after {
            match (week_before, week_after) {
                (5, 5) => (n - DAYS_PER_WEEK, n),
                (1..=4, 1..=4) => (
                    n + DAYS_PER_WEEK * (week_after - week_before - 1),
                    n + DAYS_PER_WEEK * (week_after - week_before),
                ),
                (1..=4, 5) => {
                    // For February month:
                    //   * On a normal year, we have n > (days_in_month % DAYS_PER_WEEK).
                    //   * On a leap year, we have n >= (days_in_month % DAYS_PER_WEEK).
                    //
                    // Since we want to check all possible years at the same time, checking only non-leap year is enough.
                    let days_in_month = DAYS_IN_MONTHS_NORMAL_YEAR[month_before - 1];

                    match Ord::cmp(&n, &(days_in_month % DAYS_PER_WEEK)) {
                        Ordering::Less => (
                            n + DAYS_PER_WEEK * (4 - week_before),
                            n + DAYS_PER_WEEK * (5 - week_before),
                        ),
                        Ordering::Equal => return true, // rule days are synchronized
                        Ordering::Greater => (
                            n + DAYS_PER_WEEK * (3 - week_before),
                            n + DAYS_PER_WEEK * (4 - week_before),
                        ),
                    }
                }
                _ => unreachable!(),
            }
        } else {
            // month_before != month_after
            match (week_before, week_after) {
                (1..=4, 1..=4) => {
                    // Same as above
                    let days_in_month = DAYS_IN_MONTHS_NORMAL_YEAR[month_before - 1];

                    match Ord::cmp(&n, &(days_in_month % DAYS_PER_WEEK)) {
                        Ordering::Less => (
                            n + DAYS_PER_WEEK * (4 - week_before + week_after),
                            n + DAYS_PER_WEEK * (5 - week_before + week_after),
                        ),
                        Ordering::Equal => return true, // rule days are synchronized
                        Ordering::Greater => (
                            n + DAYS_PER_WEEK * (3 - week_before + week_after),
                            n + DAYS_PER_WEEK * (4 - week_before + week_after),
                        ),
                    }
                }
                (5, 1..=4) => {
                    (n + DAYS_PER_WEEK * (week_after - 1), n + DAYS_PER_WEEK * week_after)
                }
                _ => return true, // rule days are separated by more than 3 weeks
            }
        }
    };

    let diff_days_seconds_min = diff_days_min * SECONDS_PER_DAY;
    let diff_days_seconds_max = diff_days_max * SECONDS_PER_DAY;

    // Check possible order swap of rule days
    utc_day_time_before <= diff_days_seconds_min + utc_day_time_after
        || diff_days_seconds_max + utc_day_time_after <= utc_day_time_before
}

#[cfg(test)]
mod test {
    use super::super::Error;
    use super::*;

    fn check_julian_infos(
        check_infos: JulianDayCheckInfos,
        start_normal: i64,
        end_normal: i64,
        start_leap: i64,
        end_leap: i64,
    ) {
        assert_eq!(check_infos.start_normal_year_offset, start_normal);
        assert_eq!(check_infos.end_normal_year_offset, end_normal);
        assert_eq!(check_infos.start_leap_year_offset, start_leap);
        assert_eq!(check_infos.end_leap_year_offset, end_leap);
    }

    fn check_mwd_infos(
        check_infos: MonthWeekDayCheckInfos,
        start_normal: (i64, i64),
        end_normal: (i64, i64),
        start_leap: (i64, i64),
        end_leap: (i64, i64),
    ) {
        assert_eq!(check_infos.start_normal_year_offset_range, start_normal);
        assert_eq!(check_infos.end_normal_year_offset_range, end_normal);
        assert_eq!(check_infos.start_leap_year_offset_range, start_leap);
        assert_eq!(check_infos.end_leap_year_offset_range, end_leap);
    }

    fn check(dst_start: RuleDay, dst_start_time: i32, dst_end: RuleDay, dst_end_time: i32) -> bool {
        let check_1 = check_dst_transition_rules_consistency(
            &LocalTimeType::UTC,
            &LocalTimeType::UTC,
            dst_start,
            dst_start_time,
            dst_end,
            dst_end_time,
        );

        let check_2 = check_dst_transition_rules_consistency(
            &LocalTimeType::UTC,
            &LocalTimeType::UTC,
            dst_end,
            dst_end_time,
            dst_start,
            dst_start_time,
        );

        assert_eq!(check_1, check_2);

        check_1
    }

    fn check_all(
        dst_start: RuleDay,
        dst_start_times: &[i32],
        dst_end: RuleDay,
        dst_end_time: i32,
        results: &[bool],
    ) {
        assert_eq!(dst_start_times.len(), results.len());

        for (&dst_start_time, &result) in dst_start_times.iter().zip(results) {
            assert_eq!(check(dst_start, dst_start_time, dst_end, dst_end_time), result);
        }
    }

    #[test]
    fn test_compute_check_infos() -> Result<(), Error> {
        check_julian_infos(JulianDayCheckInfos::from_julian_1(1, 1), 1, -31535999, 1, -31622399);
        check_julian_infos(
            JulianDayCheckInfos::from_julian_1(365, 1),
            31449601,
            -86399,
            31536001,
            -86399,
        );

        check_julian_infos(JulianDayCheckInfos::from_julian_0(0, 1), 1, -31535999, 1, -31622399);
        check_julian_infos(
            JulianDayCheckInfos::from_julian_0(365, 1),
            31536001,
            1,
            31536001,
            -86399,
        );

        check_mwd_infos(
            MonthWeekDayCheckInfos::from_month_weekday(1, 1, 1),
            (1, 518401),
            (-31535999, -31017599),
            (1, 518401),
            (-31622399, -31103999),
        );
        check_mwd_infos(
            MonthWeekDayCheckInfos::from_month_weekday(1, 5, 1),
            (2073601, 2592001),
            (-29462399, -28943999),
            (2073601, 2592001),
            (-29548799, -29030399),
        );
        check_mwd_infos(
            MonthWeekDayCheckInfos::from_month_weekday(2, 4, 1),
            (4492801, 5011201),
            (-27043199, -26524799),
            (4492801, 5011201),
            (-27129599, -26611199),
        );
        check_mwd_infos(
            MonthWeekDayCheckInfos::from_month_weekday(2, 5, 1),
            (4492801, 5011201),
            (-27043199, -26524799),
            (4579201, 5097601),
            (-27043199, -26524799),
        );
        check_mwd_infos(
            MonthWeekDayCheckInfos::from_month_weekday(3, 1, 1),
            (5097601, 5616001),
            (-26438399, -25919999),
            (5184001, 5702401),
            (-26438399, -25919999),
        );
        check_mwd_infos(
            MonthWeekDayCheckInfos::from_month_weekday(3, 5, 1),
            (7171201, 7689601),
            (-24364799, -23846399),
            (7257601, 7776001),
            (-24364799, -23846399),
        );
        check_mwd_infos(
            MonthWeekDayCheckInfos::from_month_weekday(12, 5, 1),
            (30931201, 31449601),
            (-604799, -86399),
            (31017601, 31536001),
            (-604799, -86399),
        );

        Ok(())
    }

    #[test]
    fn test_check_dst_transition_rules_consistency() -> Result<(), Error> {
        let julian_1 = RuleDay::julian_1;
        let julian_0 = RuleDay::julian_0;
        let mwd = RuleDay::month_weekday;

        const DAY_1: i32 = 86400;
        const DAY_2: i32 = 2 * DAY_1;
        const DAY_3: i32 = 3 * DAY_1;
        const DAY_4: i32 = 4 * DAY_1;
        const DAY_5: i32 = 5 * DAY_1;
        const DAY_6: i32 = 6 * DAY_1;

        check_all(julian_1(59)?, &[-1, 0, 1], julian_1(60)?, -DAY_1, &[true, true, false]);
        check_all(julian_1(365)?, &[-1, 0, 1], julian_1(1)?, -DAY_1, &[true, true, true]);

        check_all(julian_0(58)?, &[-1, 0, 1], julian_0(59)?, -DAY_1, &[true, true, true]);
        check_all(julian_0(364)?, &[-1, 0, 1], julian_0(0)?, -DAY_1, &[true, true, false]);
        check_all(julian_0(365)?, &[-1, 0, 1], julian_0(0)?, 0, &[true, true, false]);

        check_all(julian_1(90)?, &[-1, 0, 1], julian_0(90)?, 0, &[true, true, false]);
        check_all(julian_1(365)?, &[-1, 0, 1], julian_0(0)?, 0, &[true, true, true]);

        check_all(julian_0(89)?, &[-1, 0, 1], julian_1(90)?, 0, &[true, true, false]);
        check_all(julian_0(364)?, &[-1, 0, 1], julian_1(1)?, -DAY_1, &[true, true, false]);
        check_all(julian_0(365)?, &[-1, 0, 1], julian_1(1)?, 0, &[true, true, false]);

        check_all(mwd(1, 4, 0)?, &[-1, 0, 1], julian_1(28)?, 0, &[true, true, false]);
        check_all(mwd(2, 5, 0)?, &[-1, 0, 1], julian_1(60)?, -DAY_1, &[true, true, false]);
        check_all(mwd(12, 5, 0)?, &[-1, 0, 1], julian_1(1)?, -DAY_1, &[true, true, false]);
        check_all(
            mwd(12, 5, 0)?,
            &[DAY_3 - 1, DAY_3, DAY_3 + 1],
            julian_1(1)?,
            -DAY_4,
            &[false, true, true],
        );

        check_all(mwd(1, 4, 0)?, &[-1, 0, 1], julian_0(27)?, 0, &[true, true, false]);
        check_all(mwd(2, 5, 0)?, &[-1, 0, 1], julian_0(58)?, DAY_1, &[true, true, false]);
        check_all(mwd(2, 4, 0)?, &[-1, 0, 1], julian_0(59)?, -DAY_1, &[true, true, false]);
        check_all(mwd(2, 5, 0)?, &[-1, 0, 1], julian_0(59)?, 0, &[true, true, false]);
        check_all(mwd(12, 5, 0)?, &[-1, 0, 1], julian_0(0)?, -DAY_1, &[true, true, false]);
        check_all(
            mwd(12, 5, 0)?,
            &[DAY_3 - 1, DAY_3, DAY_3 + 1],
            julian_0(0)?,
            -DAY_4,
            &[false, true, true],
        );

        check_all(julian_1(1)?, &[-1, 0, 1], mwd(1, 1, 0)?, 0, &[true, true, false]);
        check_all(julian_1(53)?, &[-1, 0, 1], mwd(2, 5, 0)?, 0, &[true, true, false]);
        check_all(julian_1(365)?, &[-1, 0, 1], mwd(1, 1, 0)?, -DAY_1, &[true, true, false]);
        check_all(
            julian_1(365)?,
            &[DAY_3 - 1, DAY_3, DAY_3 + 1],
            mwd(1, 1, 0)?,
            -DAY_4,
            &[false, true, true],
        );

        check_all(julian_0(0)?, &[-1, 0, 1], mwd(1, 1, 0)?, 0, &[true, true, false]);
        check_all(julian_0(52)?, &[-1, 0, 1], mwd(2, 5, 0)?, 0, &[true, true, false]);
        check_all(julian_0(59)?, &[-1, 0, 1], mwd(3, 1, 0)?, 0, &[true, true, false]);
        check_all(
            julian_0(59)?,
            &[-DAY_3 - 1, -DAY_3, -DAY_3 + 1],
            mwd(2, 5, 0)?,
            DAY_4,
            &[true, true, false],
        );
        check_all(julian_0(364)?, &[-1, 0, 1], mwd(1, 1, 0)?, -DAY_1, &[true, true, false]);
        check_all(julian_0(365)?, &[-1, 0, 1], mwd(1, 1, 0)?, 0, &[true, true, false]);
        check_all(
            julian_0(364)?,
            &[DAY_4 - 1, DAY_4, DAY_4 + 1],
            mwd(1, 1, 0)?,
            -DAY_4,
            &[false, true, true],
        );
        check_all(
            julian_0(365)?,
            &[DAY_3 - 1, DAY_3, DAY_3 + 1],
            mwd(1, 1, 0)?,
            -DAY_4,
            &[false, true, true],
        );

        let months_per_year = MONTHS_PER_YEAR as u8;
        for i in 0..months_per_year - 1 {
            let month = i + 1;
            let month_1 = (i + 1) % months_per_year + 1;
            let month_2 = (i + 2) % months_per_year + 1;

            assert!(check(mwd(month, 1, 0)?, 0, mwd(month_2, 1, 0)?, 0));
            assert!(check(mwd(month, 3, 0)?, DAY_4, mwd(month, 4, 0)?, -DAY_3));

            check_all(mwd(month, 5, 0)?, &[-1, 0, 1], mwd(month, 5, 0)?, 0, &[true, true, true]);
            check_all(mwd(month, 4, 0)?, &[-1, 0, 1], mwd(month, 5, 0)?, 0, &[true, true, false]);
            check_all(
                mwd(month, 4, 0)?,
                &[DAY_4 - 1, DAY_4, DAY_4 + 1],
                mwd(month_1, 1, 0)?,
                -DAY_3,
                &[true, true, false],
            );
            check_all(
                mwd(month, 5, 0)?,
                &[DAY_4 - 1, DAY_4, DAY_4 + 1],
                mwd(month_1, 1, 0)?,
                -DAY_3,
                &[true, true, true],
            );
            check_all(mwd(month, 5, 0)?, &[-1, 0, 1], mwd(month_1, 5, 0)?, 0, &[true, true, true]);
            check_all(
                mwd(month, 3, 2)?,
                &[-1, 0, 1],
                mwd(month, 4, 3)?,
                -DAY_1,
                &[true, true, false],
            );
            check_all(
                mwd(month, 5, 2)?,
                &[-1, 0, 1],
                mwd(month, 5, 3)?,
                -DAY_1,
                &[false, true, true],
            );
            check_all(
                mwd(month, 5, 2)?,
                &[-1, 0, 1],
                mwd(month_1, 1, 3)?,
                -DAY_1,
                &[true, true, false],
            );
            check_all(mwd(month, 5, 2)?, &[-1, 0, 1], mwd(month_1, 5, 3)?, 0, &[true, true, true]);
        }

        check_all(mwd(2, 4, 2)?, &[-1, 0, 1], mwd(2, 5, 3)?, -DAY_1, &[false, true, true]);

        check_all(mwd(3, 4, 2)?, &[-1, 0, 1], mwd(3, 5, 4)?, -DAY_2, &[true, true, false]);
        check_all(mwd(3, 4, 2)?, &[-1, 0, 1], mwd(3, 5, 5)?, -DAY_3, &[true, true, true]);
        check_all(mwd(3, 4, 2)?, &[-1, 0, 1], mwd(3, 5, 6)?, -DAY_4, &[false, true, true]);

        check_all(mwd(4, 4, 2)?, &[-1, 0, 1], mwd(4, 5, 3)?, -DAY_1, &[true, true, false]);
        check_all(mwd(4, 4, 2)?, &[-1, 0, 1], mwd(4, 5, 4)?, -DAY_2, &[true, true, true]);
        check_all(mwd(4, 4, 2)?, &[-1, 0, 1], mwd(4, 5, 5)?, -DAY_3, &[false, true, true]);

        check_all(
            mwd(2, 4, 2)?,
            &[DAY_5 - 1, DAY_5, DAY_5 + 1],
            mwd(3, 1, 3)?,
            -DAY_3,
            &[false, true, true],
        );

        check_all(
            mwd(3, 4, 2)?,
            &[DAY_5 - 1, DAY_5, DAY_5 + 1],
            mwd(4, 1, 4)?,
            -DAY_4,
            &[true, true, false],
        );
        check_all(
            mwd(3, 4, 2)?,
            &[DAY_5 - 1, DAY_5, DAY_5 + 1],
            mwd(4, 1, 5)?,
            -DAY_5,
            &[true, true, true],
        );
        check_all(
            mwd(3, 4, 2)?,
            &[DAY_5 - 1, DAY_5, DAY_5 + 1],
            mwd(4, 1, 6)?,
            -DAY_6,
            &[false, true, true],
        );

        check_all(
            mwd(4, 4, 2)?,
            &[DAY_5 - 1, DAY_5, DAY_5 + 1],
            mwd(5, 1, 3)?,
            -DAY_3,
            &[true, true, false],
        );
        check_all(
            mwd(4, 4, 2)?,
            &[DAY_5 - 1, DAY_5, DAY_5 + 1],
            mwd(5, 1, 4)?,
            -DAY_4,
            &[true, true, true],
        );
        check_all(
            mwd(4, 4, 2)?,
            &[DAY_5 - 1, DAY_5, DAY_5 + 1],
            mwd(5, 1, 5)?,
            -DAY_5,
            &[false, true, true],
        );

        Ok(())
    }
}
