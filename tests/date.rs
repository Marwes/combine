//! Parser example for ISO8601 dates. This does not handle the entire specification but it should
//! show the gist of it and be easy to extend to parse additional forms.

#[macro_use]
extern crate combine;

use combine::char::{char, digit};
use combine::{choice, many, optional, Parser, Stream};

#[derive(PartialEq, Debug)]
pub struct Date {
    pub year: i32,
    pub month: i32,
    pub day: i32,
}

#[derive(PartialEq, Debug)]
pub struct Time {
    pub hour: i32,
    pub minute: i32,
    pub second: i32,
    pub time_zone: i32,
}

#[derive(PartialEq, Debug)]
pub struct DateTime {
    pub date: Date,
    pub time: Time,
}

fn two_digits_to_int((x, y): (char, char)) -> i32 {
    let x = x.to_digit(10).expect("digit");
    let y = y.to_digit(10).expect("digit");
    (x * 10 + y) as i32
}


parser!{
    two_digits[I](I) -> i32
    where
        [I: Stream<Item = char>,]
    {
        (digit(), digit())
            .map(two_digits_to_int)
    }
}

/// Parses a time zone
/// +0012
/// -06:30
/// -01
/// Z
parser!{
    time_zone[I](I) -> i32
    where
        [I: Stream<Item = char>,]
    {
        let utc = char('Z').map(|_| 0);
        let offset = (
            choice([char('-'), char('+')]),
            two_digits(),
            optional(optional(char(':')).with(two_digits())),
        ).map(|(sign, hour, minute)| {
                let offset = hour * 60 + minute.unwrap_or(0);
                if sign == '-' {
                    -offset
                } else {
                    offset
                }
            });

        utc.or(offset)
    }
}

/// Parses a date
/// 2010-01-30
parser!{
    date[I](I) -> Date
    where
        [I: Stream<Item = char>,]
    {
        (
            many::<String, _>(digit()),
            char('-'),
            two_digits(),
            char('-'),
            two_digits(),
        ).map(|(year, _, month, _, day)| {
                // Its ok to just unwrap since we only parsed digits
                Date {
                    year: year.parse().unwrap(),
                    month: month,
                    day: day,
                }
            })
    }
}

/// Parses a time
/// 12:30:02
parser!{
    time[I](I) -> Time
    where
        [I: Stream<Item = char>,]
    {
        (
            two_digits(),
            char(':'),
            two_digits(),
            char(':'),
            two_digits(),
            time_zone(),
        ).map(|(hour, _, minute, _, second, time_zone)| {
                // Its ok to just unwrap since we only parsed digits
                Time {
                    hour: hour,
                    minute: minute,
                    second: second,
                    time_zone: time_zone,
                }
            })
    }
}

/// Parses a date time according to ISO8601
/// 2015-08-02T18:54:42+02
parser!{
    date_time [I](I) -> DateTime
    where
        [I: Stream<Item = char>,]
    {
        (date(), char('T'), time())
            .map(|(date, _, time)| {
                DateTime {
                    date: date,
                    time: time,
                }
            })
    }
}

#[test]
fn test() {
    // A parser for
    let result = date_time().parse("2015-08-02T18:54:42+02");
    let d = DateTime {
        date: Date {
            year: 2015,
            month: 8,
            day: 2,
        },
        time: Time {
            hour: 18,
            minute: 54,
            second: 42,
            time_zone: 2 * 60,
        },
    };
    assert_eq!(result, Ok((d, "")));

    let result = date_time().parse("50015-12-30T08:54:42Z");
    let d = DateTime {
        date: Date {
            year: 50015,
            month: 12,
            day: 30,
        },
        time: Time {
            hour: 8,
            minute: 54,
            second: 42,
            time_zone: 0,
        },
    };
    assert_eq!(result, Ok((d, "")));
}
