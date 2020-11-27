use thiserror::Error;
use std::fmt;

#[derive(Debug, PartialEq)]
pub(crate) struct ResolvAddr(String);

impl ResolvAddr {
    pub(crate) fn as_str(&self) -> &str {
        &self.0
    }

    pub(crate) fn try_from_generic<T: std::ops::Deref<Target=str> + Into<String>>(string: T) -> Result<Self, ResolvAddrError> {
        // can't use a combinator due to borrowing
        let colon = match string.rfind(':') {
            Some(colon) => colon,
            None => return Err(ResolvAddrError::MissingPort(string.into())),
        };

        let (hostname, port) = string.split_at(colon);

        if let Err(error) = port[1..].parse::<u16>() {
            return Err(ResolvAddrError::InvalidPort { string: string.into(), error, });
        }

        let len = hostname.len();
        if len > 253 {
            return Err(ResolvAddrError::TooLong { string: string.into(), len, } )
        }

        let mut label_start = 0usize;

        for (i, c) in hostname.chars().enumerate() {
            match c {
                '.' => {
                    if i - label_start == 0 {
                        return Err(ResolvAddrError::EmptyLabel { string: string.into(), label_start, });
                    }

                    label_start = i + 1;
                },
                'a'..='z' | 'A'..='Z' | '0'..='9' | '-' => (),
                _ => return Err(ResolvAddrError::InvalidCharacter { string: string.into(), c, pos: i, }),
            }

            if i - label_start > 63 {
                return Err(ResolvAddrError::LongLabel { string: string.into(), label_start, label_end: i, });
            }
        }

        Ok(ResolvAddr(string.into()))
    }
}

impl fmt::Display for ResolvAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}


#[derive(Debug, Error)]
pub(crate) enum ResolvAddrError {
    #[error("hostname {string} has {len} character which exceeds the limit of 253")]
    TooLong { string: String, len: usize },
    #[error("invalid character {c} in hostname {string} at position {pos}")]
    InvalidCharacter { string: String, pos: usize, c: char, },
    #[error("hostname {string} contains a label {} at position {label_start} which is {} characters long - more than the limit 63", &string[(*label_start)..(*label_end)], label_end - label_start)]
    LongLabel { string: String, label_start: usize, label_end: usize, },
    #[error("hostname {string} contains an empty label at position {label_start}")]
    EmptyLabel { string: String, label_start: usize, },
    #[error("the address {0} is missing a port")]
    MissingPort(String),
    #[error("failed to parse port numer in the address {string}")]
    InvalidPort { string: String, error: std::num::ParseIntError, },
}
