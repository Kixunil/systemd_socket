//! Error types that can occur when dealing with `SocketAddr`
//!
//! This module separates the error types from root module to avoid clutter.


use thiserror::Error;
use std::io;

/// Error that can occur during parsing of `SocketAddr` from a string
///
/// This encapsulates possible errors that can occur when parsing the input.
/// It is currently opaque because the representation is not certain yet.
/// It can be displayed using the standard `Error` trait.
#[derive(Debug, Error)]
#[error(transparent)]
pub struct ParseError(#[from] pub(crate) ParseErrorInner);

#[derive(Debug, Error)]
pub(crate) enum ParseErrorInner {
    #[error("failed to parse socket address")]
    ResolvAddr(#[from] crate::resolv_addr::ResolvAddrError),
    #[cfg(linux)]
    #[error("invalid character '{c}' in systemd socket name {string} at position {pos}")]
    InvalidCharacter { string: String, c: char, pos: usize, },
    #[cfg(linux)]
    #[error("systemd socket name {string} is {len} characters long which is more than the limit 255")]
    LongSocketName { string: String, len: usize, },
    #[cfg(not(linux))]
    #[error("can't parse {0} because systemd is not supported on this operating system")]
    SystemdUnsupported(String),
}

/// Error that can occur during parsing of `SocketAddr` from a `OsStr`/`OsString`
///
/// As opposed to parsing from `&str` or `String`, parsing from `OsStr` can fail due to one more
/// reason: invalid UTF-8. This error type expresses this possibility and is returned whenever such
/// conversion is attempted. It is not opaque because the possible variants are pretty much
/// certain, but it may contain `ParseError` which is opaque.
///
/// This error can be displayed using standard `Error` trait.
/// See `ParseError` for more information.
#[derive(Debug, Error)]
pub enum ParseOsStrError {
    /// The input was not a valid UTF-8 string
    #[error("the address is not a valid UTF-8 string")]
    InvalidUtf8,
    /// The input was a valid UTF-8 string but the address was invalid
    #[error(transparent)]
    InvalidAddress(#[from] ParseError),
}

/// Error that can occur during binding of a socket
///
/// This encapsulates possible errors that can occur when binding a socket or receiving a socket
/// from systemd.
/// It is currently opaque because the representation is not certain yet.
/// It can be displayed using the standard `Error` trait.
#[derive(Debug, Error)]
#[error(transparent)]
pub struct BindError(#[from] pub(crate) BindErrorInner);

#[derive(Debug, Error)]
pub(crate) enum BindErrorInner {
    #[error("failed to bind {addr}")]
    BindFailed { addr: std::net::SocketAddr, #[source] error: io::Error, },
    #[error("failed to bind {addr}")]
    BindOrResolvFailed { addr: crate::resolv_addr::ResolvAddr, #[source] error: io::Error, },
    #[cfg(linux)]
    #[error("failed to receive descriptors with names")]
    ReceiveDescriptors(#[source] crate::systemd_sockets::Error),
    #[error("missing systemd socket {0} - a typo or an attempt to bind twice")]
    #[cfg(linux)]
    MissingDescriptor(String),
    #[error("the systemd socket {0} is not an internet socket")]
    #[cfg(linux)]
    NotInetSocket(String),
}

/// Error that can happen when binding Tokio socket.
///
/// As opposed to `std` and `async_std` sockets, tokio sockets can fail to convert.
/// This error type expresses this possibility.
#[cfg(any(feature = "tokio_0_2", feature = "tokio_0_3"))]
#[derive(Debug, Error)]
#[error(transparent)]
pub enum TokioBindError {
    /// Either binding of socket or receiving systemd socket failed
    Bind(#[from] BindError),
    /// Conversion from std `std::net::TcpListener` to `tokio::net::TcpListener` failed
    Convert(#[from] TokioConversionError),
}

/// Error that can happen when converting Tokio socket.
///
/// As opposed to `std` and `async_std` sockets, tokio sockets can fail to convert.
/// This error type encapsulates conversion error together with additional information so that it
/// can be displayed nicely. The encapsulation also allows for future-proofing.
#[cfg(any(feature = "tokio_0_2", feature = "tokio_0_3"))]
#[derive(Debug, Error)]
#[error("failed to convert std socket {addr} into tokio socket")]
pub struct TokioConversionError {
    pub(crate) addr: crate::SocketAddrInner,
    #[source]
    pub(crate) error: io::Error,
}

