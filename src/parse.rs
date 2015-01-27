extern crate regex_macros;      // for compile-time regular expression compilation
extern crate regex;
use std::num::Int;
use std::cmp;
use ::{Offset};

//
//  parse.rs  --  parsing for various standardized date and time string formats
//
//  John Nagle
//  January, 2015
//
//
//  RFC2822 time/date stamp parsing
//
//  Example: "Tue, 20 Jan 2015 17:35:20 -0800".
//  Common use case: email date/time.
//
// Date format specification, from RFC2822.
//
// date-time       =       [ day-of-week "," ] date FWS time [CFWS]
//
// day-of-week     =       ([FWS] day-name) / obs-day-of-week
//
// day-name        =       "Mon" / "Tue" / "Wed" / "Thu" /
//                         "Fri" / "Sat" / "Sun"
//
// date            =       day month year
//
// year            =       4*DIGIT / obs-year
//
// month           =       (FWS month-name FWS) / obs-month
//
// month-name      =       "Jan" / "Feb" / "Mar" / "Apr" /
//                         "May" / "Jun" / "Jul" / "Aug" /
//                         "Sep" / "Oct" / "Nov" / "Dec"
//
// day             =       ([FWS] 1*2DIGIT) / obs-day
//
// time            =       time-of-day FWS zone
//
// time-of-day     =       hour ":" minute [ ":" second ]
// 
// hour            =       2DIGIT / obs-hour
// 
// minute          =       2DIGIT / obs-minute
// 
// second          =       2DIGIT / obs-second
// 
// zone            =       (( "+" / "-" ) 4DIGIT) / obs-zone
//
//
// Obsolete forms
//
// obs-day-of-week =       [CFWS] day-name [CFWS]
//
// obs-year        =       [CFWS] 2*DIGIT [CFWS]
//
// obs-month       =       CFWS month-name CFWS
//
// obs-day         =       [CFWS] 1*2DIGIT [CFWS]
//
// obs-hour        =       [CFWS] 2DIGIT [CFWS]
//
// obs-minute      =       [CFWS] 2DIGIT [CFWS]
//
// obs-second      =       [CFWS] 2DIGIT [CFWS]
//
// obs-zone        =       "UT" / "GMT" /          ; Universal Time
//                                                 ; North American UT
//                                                 ; offsets
//                         "EST" / "EDT" /         ; Eastern:  - 5/ - 4
//                         "CST" / "CDT" /         ; Central:  - 6/ - 5
//                         "MST" / "MDT" /         ; Mountain: - 7/ - 6
//                         "PST" / "PDT" /         ; Pacific:  - 8/ - 7
// 
//                         %d65-73 /               ; Military zones - "A"
//                         %d75-90 /               ; through "I" and "K"
//                         %d97-105 /              ; through "Z", both
//                         %d107-122               ; upper and lower case
//
//
// Per RFC2882, all the obsolete one-letter military time zones are interpreted as 
//  +0000.
//
// The only feature not supported is that an offset of "-0000" should return a
// naive date/time, not a time zone aware one.  This returns a time zone aware
// date/time object in all cases.
// 
//
/// Time zone offset in minutes, from string.
/// Allowed input per RFC2822 above - numeric offset or named time zone
fn offsetmins(s: &str) -> Option<i32> {
    let offsetre = regex!(r"^([+-])(\d\d)(\d\d)$"); // +0800 as 8 hour offset
    let offsetmatches = offsetre.captures(s);           // match time zone
    match offsetmatches {
        Some(caps) => {                                 // It looks like a numeric offset
            let sign = caps.at(1).unwrap();             // + or -
            let hh = caps.at(2).unwrap().parse::<i32>().unwrap(); // hours
            let mm = caps.at(3).unwrap().parse::<i32>().unwrap(); // minutes
            let signval = match sign {
                "+" => 1,
                "-" => -1,
                _ => return None                        // unreachable
                };
            if hh < -12 || hh > 12 || mm < 0 || mm > 59 { return None }   // check offsets
            return Some(signval*(hh*60 + mm))           // return offset in minute
            }
        None => {                                       // not numeric, try the named time zones
             return match s {
                "GMT"|"UT"|"Z"|"z" => Some(0),          // prime meridian
                "EDT" => Some(-4*60),                   // obsolete forms
                "EST"|"CDT" => Some(-5*60),             // rather US-centric in this old RFC.
                "CST"|"MDT" => Some(-6*60),
                "MST"|"PDT" => Some(-7*60),
                "PST" => Some(-8*60),
                _ => match s.len() { 1 => Some(0), _  => None } // obsolete single-letter miltary forms are treated as 0 per RFC2822
            }
        }       
    };
}

/// Makes a new `DateTime` with offset given a valid RFC2822 string.
/// Example: "Tue, 20 Jan 2015 17:35:20 -0800"
pub fn rfc2822_to_datetime(s: &str) -> Option<::DateTime<::FixedOffset>> {

    //  Match the date format.  Case-insensitive, compile-time regex.
    let datere = regex!(r"^(?i)(?:Mon,|Tue,|Wed,|Thu,|Fri,|Sat,|Sun,)??\s*(\d+)\s+(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)\s+(\d\d\d\d)\s+(\d+):(\d+):(\d+)\s*([+-]\d\d\d\d|[A-Z]+)$");
    let matches = datere.captures(s.trim());   // Pattern match the date
    let captures = match matches {
        Some(caps) => caps,             // succeed
        None => return None             // fail
    };
    //  Unwrapping numeric fields is safe because we've matched the regular expression.
    let dd = captures.at(1).unwrap().parse::<u32>().unwrap();   // day of month
    //  Month names are case-sensitive in RFC 2822, but we allow the obvious other forms.
    let mo = match captures.at(2).unwrap() {                    // month decode
        "Jan"|"JAN"|"jan" => 1,
        "Feb"|"FEB"|"feb" => 2,
        "Mar"|"MAR"|"mar" => 3,
        "Apr"|"APR"|"apr" => 4,
        "May"|"MAY"|"may" => 5,
        "Jun"|"JUN"|"jun" => 6,
        "Jul"|"JUL"|"jul" => 7,
        "Aug"|"AUG"|"aug" => 8,
        "Sep"|"SEP"|"sep" => 9,
        "Oct"|"OCT"|"oct" => 10,
        "Nov"|"NOV"|"nov" => 11,
        "Dec"|"DEC"|"dec" => 12,
        _ => return None
        };    
    let yyyy = captures.at(3).unwrap().parse::<i32>().unwrap(); // chrono wants a signed year
    let hh = captures.at(4).unwrap().parse::<u32>().unwrap();
    let mm = captures.at(5).unwrap().parse::<u32>().unwrap();   // minute
    let ss = captures.at(6).unwrap().parse::<u32>().unwrap();
    let offsetstr = captures.at(7).unwrap();                    // can be +0800 or a time zone name
    let offsetmm = match offsetmins(offsetstr) {
        Some(v) => v,
        None => return None
    };    
    let tz = ::FixedOffset::east(offsetmm*60);                  // decode time zone offset
    //  Pack numeric values into DateTime object, returning None if fail.
    let date = tz.ymd_opt(yyyy, mo, dd);                        // date or none
    match date {                                                // check for invalid date
        ::LocalResult::Single(d) => d.and_hms_opt(hh, mm, ss),  // encode into DateTime
        _ => return None                                        // date conversion failed
    }     
}

/// Formats a DateTime as an RF2822 string.
/// This is primarily for debugging.
pub fn fmt_rfc2822_datetime(dt: ::DateTime<::FixedOffset>) -> String {
    dt.format("%a, %e %b %Y %H:%M:%S %z").to_string()           // inverse of parsing
}

//
//  RFC3339 date parsing
//
//  This is a subset of ISO 8601 date format.
//  Example: "2012-09-09T18:00:00-07:00"
//  Common use case: Atom feeds.
//
//
//   From RFC3339, "Date and Time on the Internet: Timestamps", section 5.6:
//
//   date-fullyear   = 4DIGIT
//   date-month      = 2DIGIT  ; 01-12
//   date-mday       = 2DIGIT  ; 01-28, 01-29, 01-30, 01-31 based on
//                             ; month/year
//   time-hour       = 2DIGIT  ; 00-23
//   time-minute     = 2DIGIT  ; 00-59
//   time-second     = 2DIGIT  ; 00-58, 00-59, 00-60 based on leap second
//                             ; rules
//   time-secfrac    = "." 1*DIGIT
//   time-numoffset  = ("+" / "-") time-hour ":" time-minute
//   time-offset     = "Z" / time-numoffset
//
//   partial-time    = time-hour ":" time-minute ":" time-second
//                    [time-secfrac]
//   full-date       = date-fullyear "-" date-month "-" date-mday
//   full-time       = partial-time time-offset
//
//   date-time       = full-date "T" full-time
//
//   NOTE: Per [ABNF] and ISO8601, the "T" and "Z" characters in this
//      syntax may alternatively be lower case "t" or "z" respectively.
//
//      ISO 8601 defines date and time separated by "T".
//      Applications using this syntax may choose, for the sake of
//      readability, to specify a full-date and full-time separated by
//      (say) a space character.
//

/// Parse a string with a RFC3339 date, time, and offset into a DateTime.
/// This is the subset of ISO 8601 date and time strings most used on the Web.
pub fn rfc3339_to_datetime(s: &str) -> Option<::DateTime<::FixedOffset>> {
    let datere = regex!(r"^(?i)(\d\d\d\d)-(\d\d)-(\d\d)T(\d\d):(\d\d):(\d\d)(\.\d+)??([+-]\d\d\d\d|[A-Z]+)$"); // format regex
        let matches = datere.captures(s.trim());   // Pattern match the date
    let captures = match matches {
        Some(caps) => caps,             // succeed
        None => return None             // fail
    };
    //  Unwrapping numeric fields is safe because we've matched the regular expression.
    let yyyy = captures.at(1).unwrap().parse::<i32>().unwrap(); // chrono wants a signed year
    let mo = captures.at(2).unwrap().parse::<u32>().unwrap();   // month of year
    let dd = captures.at(3).unwrap().parse::<u32>().unwrap();   // day of month
    let hh = captures.at(4).unwrap().parse::<u32>().unwrap();   // hour
    let mm = captures.at(5).unwrap().parse::<u32>().unwrap();   // minute
    let ss = captures.at(6).unwrap().parse::<u32>().unwrap();   // second
    let ns = match captures.at(7) {                             // fractional seconds present?
        Some(fractstr) =>  parsensfract(fractstr),              // parse as nanoseconds
        None => 0                                               // no fraction
    };
    let offsetstr = captures.at(8).unwrap();                    // time zone offset, numeric
    let offsetmm = match offsetmins(offsetstr) {                // also accepts named time zones, not required.
        Some(v) => v,
        None => return None
    };    
    let tz = ::FixedOffset::east(offsetmm*60);                    // decode time zone offset
    //  Pack numeric values into DateTime object, returning None if fail.
    let date = tz.ymd_opt(yyyy, mo, dd);                        // date or none
    match date {                                                // check for invalid date
        ::LocalResult::Single(d) => d.and_hms_nano_opt(hh, mm, ss, ns), // encode into DateTime
        _ => return None                                        // date conversion failed
    }     
}

/// Parse ".NNN" into nanoseconds.
/// Assumes input has already been checked for ".NNN" format.
fn parsensfract(s: &str) -> u32 {
    let sdigits = &s[1..];                                      // trim off leading "."
    let sdigits9 = &sdigits[0..(cmp::min(sdigits.len(),9))]; // truncate at 9 digits after "."
    let v = sdigits9.parse::<u32>().unwrap();                   // digits as u32 (will fit)
    let vl = 9-sdigits9.len();                                  // power of 10 for scaling
    let scale = Int::pow(10,vl);                                // scale factor to get to 
    //panic!("parsens: s: {}  sdigits9: {}  v: {}  scale: {}  result: {}", s, sdigits9 , v, scale, v*scale);   // ***TEMP***       
    v*scale                                                     // as nanoseconds
}

/// Formats a DateTime as an RFC 3339/ISO8601 date, with 9 digits of nanoseconds.
/// This is the inverse operation of rfc3339 parsing.
pub fn fmt_rfc3339_datetime(dt: ::DateTime<::FixedOffset>) -> String {
    dt.format("%Y-%m-%dT%H:%M:%S.%f%z").to_string()           // inverse of parsing
}


//
//  Unit tests
//
#[test]
/// Test RFC2822 parser.
fn testrfc2822parser() {
    //  Test data - [input, expected result after parse and format]
    let testdates = [
        ["Tue, 20 Jan 2015 17:35:20 -0800", "Tue, 20 Jan 2015 17:35:20 -0800"], // normal case
        ["20 Jan 2015 17:35:20 -0800", "Tue, 20 Jan 2015 17:35:20 -0800"],  // no day of week
        ["20 JAN 2015 17:35:20 -0800", "Tue, 20 Jan 2015 17:35:20 -0800"],  // upper case month allowed
        ["6 Jun 1944 04:00:00Z","Tue,  6 Jun 1944 04:00:00 +0000"],         // D-day
        ["11 Sep 2001 9:45:00 EST", "Tue, 11 Sep 2001 09:45:00 -0500"],
        ["30 Feb 2015 17:35:20 -0800", ""],     // bad day of month
        ["Tue, 20 Avr 2015 17:35:20 -0800", ""],// bad month name
        ["Tue, 20 Jan 2015 25:35:20 -0800",""], // bad hour
        ["Tue, 20 Jan 2015 17:65:20 -0800",""], // bad minute
        ["Tue, 20 Jan 2015 17:35:90 -0800",""], // bad second
        ["Tue, 20 Jan 2015 17:35:20 -1800",""], // bad offset
        ["Tue, 20 Jan 2015 17:35:20 HAS",""]    // bad named time zone
        ];
    //  Test against test data above
    for testdate in testdates.iter() {
        let date = testdate[0];                 // input
        let checkdate = testdate[1];            // expected result or ""
        let d = rfc2822_to_datetime(date);      // parse a date
        let dt = match d {                      // did we get a value?
            Some(dt) => dt,                     // yes, go on
            None => if checkdate != "" { panic!("Failed to convert date {}", date)} else { continue },
        };
        // let mut s = String::new();
        let s = fmt_rfc2822_datetime(dt);       // convert date/time back to string
        if s != checkdate {                     // check for expected result
            panic!("Date conversion failed for {}\nReceived: {}\nExpected: {}",date, s, checkdate);
        }
    };  
}
#[test]
/// Test RFC3339/ISO8601 parser.
fn testrfc3339parser() {
    //  Test data - [input, expected result after parse and format]
    let testdates = [
        ["2015-01-20T17:35:20-0800", "2015-01-20T17:35:20.000000000-0800"],   // normal case
        ["1944-06-06T04:04:00Z", "1944-06-06T04:04:00.000000000+0000"],        // D-day
        ["2001-09-11T09:45:00-0800", "2001-09-11T09:45:00.000000000-0800"],
        ["2015-01-20T17:35:20.001-0800", "2015-01-20T17:35:20.001000000-0800"],   // milliseconds
        ["2015-01-20T17:35:20.000031-0800", "2015-01-20T17:35:20.000031000-0800"],   // microseconds
        ["2015-01-20T17:35:20.000000004-0800", "2015-01-20T17:35:20.000000004-0800"],   // nanoseconds
        ["2015-01-20T17:35:20.000000000452-0800", "2015-01-20T17:35:20.000000000-0800"],   // picoseconds (too small)
        ["2015-02-30T17:35:20-0800", ""],                           // bad day of month
        ["2015-01-20T25:35:20-0800", ""],                           // bad hour
        ["2015-01-20T17:65:20-0800", ""],                           // bad minute
        ["2015-01-20T17:35:90-0800", ""],                           // bad second
        ["2015-01-20T17:35:20-1800", ""],                           // bad offset
        ];
    //  Test against test data above
    for testdate in testdates.iter() {
        let date = testdate[0];                 // input
        let checkdate = testdate[1];            // expected result or ""
        let d = rfc3339_to_datetime(date);      // parse a date
        let dt = match d {                      // did we get a value?
            Some(dt) => dt,                     // yes, go on
            None => if checkdate != "" { panic!("Failed to convert date {}", date)} else { continue },
        };
        // let mut s = String::new();
        let s = fmt_rfc3339_datetime(dt);       // convert date/time back to string
        if s != checkdate {                     // check for expected result
            panic!("Date conversion failed for {}\nReceived: {}\nExpected: {}",date, s, checkdate);
        }
    };  
}
