//! A convenience crate for optionally supporting systemd socket activation.
//! 
//! ## About
//! 
//! The goal of this crate is to make socket activation with systemd in your project trivial.
//! It provides a replacement for `std::net::SocketAddr` that allows parsing the bind address from string just like the one from `std`
//! but on top of that also allows `systemd://socket_name` format that tells it to use systemd activation with given socket name.
//! Then it provides a method to bind the address which will return the socket from systemd if available.
//! 
//! The provided type supports conversions from various types of strings and also `serde` and `parse_arg` via feature flag.
//! Thanks to this the change to your code should be minimal - parsing will continue to work, it'll just allow a new format.
//! You only need to change the code to use `SocketAddr::bind()` instead of `TcpListener::bind()` for binding.
//!
//! You also don't need to worry about conditional compilation to ensure OS compatibility.
//! This crate handles that for you by disabling systemd on non-linux systems.
//!
//! Further, the crate also provides methods for binding `tokio` 0.2, 0.3, and `async_std` sockets if the appropriate features are
//! activated.
//! 
//! ## Example
//! 
//! ```no_run
//! use systemd_socket::SocketAddr;
//! use std::convert::TryFrom;
//! use std::io::Write;
//! 
//! let mut args = std::env::args_os();
//! let program_name = args.next().expect("unknown program name");
//! let socket_addr = args.next().expect("missing socket address");
//! let socket_addr = SocketAddr::try_from(socket_addr).expect("failed to parse socket address");
//! let socket = socket_addr.bind().expect("failed to bind socket");
//!
//! loop {
//!     let _ = socket
//!     .accept()
//!     .expect("failed to accept connection")
//!     .0
//!     .write_all(b"Hello world!")
//!     .map_err(|err| eprintln!("Failed to send {}", err));
//! }
//! ```
//!
//! ## Features
//!
//! * `enable_systemd` - on by default, the existence of this feature can allow your users to turn
//!   off systemd support if they don't need it. Note that it's already disabled on non-linux
//!   systems, so you don't need to care about that.
//! * `serde` - implements `serde::Deserialize` for `SocketAddr`
//! * `parse_arg` - implements `parse_arg::ParseArg` for `SocketAddr`
//! * `tokio_0_2` - adds `bind_tokio_0_2` method to `SocketAddr`
//! * `tokio_0_3` - adds `bind_tokio_0_3` method to `SocketAddr`
//! * `async_std` - adds `bind_async_std` method to `SocketAddr`
//!
//! ## MSRV
//!
//! This crate must always compile with the latest Rust available in the latest Debian stable.
//! That is currently Rust 1.41.1. (Debian 10 - Buster)


#![deny(missing_docs)]

pub mod error;
mod resolv_addr;

use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::ffi::{OsStr, OsString};
use crate::error::*;
use crate::resolv_addr::ResolvAddr;

#[cfg(not(all(target_os = "linux", feature = "enable_systemd")))]
use std::convert::Infallible as Never;

#[cfg(all(target_os = "linux", feature = "enable_systemd"))]
pub(crate) mod systemd_sockets {
    use std::fmt;
    use std::sync::Mutex;
    use libsystemd::activation::FileDescriptor;
    use libsystemd::errors::Error as LibSystemdError;
    use libsystemd::errors::Result as LibSystemdResult;

    #[derive(Debug)]
    pub(crate) struct Error(&'static Mutex<LibSystemdError>);

    impl fmt::Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            fmt::Display::fmt(&*self.0.lock().expect("mutex poisoned"), f)
        }
    }

    // No source we can't keep the mutex locked
    impl std::error::Error for Error {}

    pub(crate) fn take(name: &str) -> Result<Option<FileDescriptor>, Error> {
        match &*SYSTEMD_SOCKETS {
            Ok(sockets) => Ok(sockets.take(name)),
            Err(error) => Err(Error(error))
        }
    }

    struct SystemdSockets(std::sync::Mutex<std::collections::HashMap<String, FileDescriptor>>);

    impl SystemdSockets {
        fn new() -> LibSystemdResult<Self> {
                                                                            // MUST BE true FOR SAFETY!!!
            let map = libsystemd::activation::receive_descriptors_with_names(/*unset env = */ true)?.into_iter().map(|(fd, name)| (name, fd)).collect();
            Ok(SystemdSockets(Mutex::new(map)))
        }

        fn take(&self, name: &str) -> Option<FileDescriptor> {
            // MUST remove THE SOCKET FOR SAFETY!!!
            self.0.lock().expect("poisoned mutex").remove(name)
        }
    }

    lazy_static::lazy_static! {
        // We don't panic in order to let the application handle the error later
        static ref SYSTEMD_SOCKETS: Result<SystemdSockets, Mutex<LibSystemdError>> = SystemdSockets::new().map_err(Mutex::new);
    }
}

/// Socket address that can be an ordinary address or a systemd socket
///
/// This is the core type of this crate that abstracts possible addresses.
/// It can be (fallibly) converted from various types of strings or deserialized with `serde`.
/// After it's created, it can be bound as `TcpListener` from `std` or even `tokio` or `async_std`
/// if the appropriate feature is enabled.
///
/// Optional dependencies on `parse_arg` and `serde` make it trivial to use with
/// [`configure_me`](https://crates.io/crates/configure_me).
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(serde_crate::Deserialize), serde(crate = "serde_crate", try_from = "serde_str_helpers::DeserBorrowStr"))]
pub struct SocketAddr(SocketAddrInner);

impl SocketAddr {
    /// Creates `std::net::TcpListener`
    ///
    /// This method either `binds` the socket, if the address was provided or uses systemd socket
    /// if the socket name was provided.
    pub fn bind(self) -> Result<std::net::TcpListener, BindError> {
        match self.0 {
            SocketAddrInner::Ordinary(addr) => match std::net::TcpListener::bind(addr) {
                Ok(socket) => Ok(socket),
                Err(error) => Err(BindErrorInner::BindFailed { addr, error, }.into()),
            },
            SocketAddrInner::WithHostname(addr) => match std::net::TcpListener::bind(addr.as_str()) {
                Ok(socket) => Ok(socket),
                Err(error) => Err(BindErrorInner::BindOrResolvFailed { addr, error, }.into()),
            },
            SocketAddrInner::Systemd(socket_name) => Self::get_systemd(socket_name).map(|(socket, _)| socket),
        }
    }

    /// Creates `tokio::net::TcpListener`
    ///
    /// To be specific, it binds the socket or converts systemd socket to `tokio` 0.2 socket.
    ///
    /// This method either `binds` the socket, if the address was provided or uses systemd socket
    /// if the socket name was provided.
    #[cfg(feature = "tokio_0_2")]
    pub async fn bind_tokio_0_2(self) -> Result<tokio_0_2::net::TcpListener, TokioBindError> {
        match self.0 {
            SocketAddrInner::Ordinary(addr) => match tokio_0_2::net::TcpListener::bind(addr).await {
                Ok(socket) => Ok(socket),
                Err(error) => Err(TokioBindError::Bind(BindErrorInner::BindFailed { addr, error, }.into())),
            },
            SocketAddrInner::WithHostname(addr) => match tokio_0_2::net::TcpListener::bind(addr.as_str()).await {
                Ok(socket) => Ok(socket),
                Err(error) => Err(TokioBindError::Bind(BindErrorInner::BindOrResolvFailed { addr, error, }.into())),
            },
            SocketAddrInner::Systemd(socket_name) => {
                let (socket, addr) = Self::get_systemd(socket_name)?;
                socket.try_into().map_err(|error| TokioConversionError { addr, error, }.into())
            },
        }
    }

    /// Creates `tokio::net::TcpListener`
    ///
    /// To be specific, it binds the socket or converts systemd socket to `tokio` 0.3 socket.
    ///
    /// This method either `binds` the socket, if the address was provided or uses systemd socket
    /// if the socket name was provided.
    #[cfg(feature = "tokio_0_3")]
    pub async fn bind_tokio_0_3(self) -> Result<tokio_0_3::net::TcpListener, TokioBindError> {
        match self.0 {
            SocketAddrInner::Ordinary(addr) => match tokio_0_3::net::TcpListener::bind(addr).await {
                Ok(socket) => Ok(socket),
                Err(error) => Err(TokioBindError::Bind(BindErrorInner::BindFailed { addr, error, }.into())),
            },
            SocketAddrInner::WithHostname(addr) => match tokio_0_3::net::TcpListener::bind(addr.as_str()).await {
                Ok(socket) => Ok(socket),
                Err(error) => Err(TokioBindError::Bind(BindErrorInner::BindOrResolvFailed { addr, error, }.into())),
            },
            SocketAddrInner::Systemd(socket_name) => {
                let (socket, addr) = Self::get_systemd(socket_name)?;
                socket.try_into().map_err(|error| TokioConversionError { addr, error, }.into())
            },
        }
    }

    /// Creates `async_std::net::TcpListener`
    ///
    /// To be specific, it binds the socket or converts systemd socket to `async_std` socket.
    ///
    /// This method either `binds` the socket, if the address was provided or uses systemd socket
    /// if the socket name was provided.
    #[cfg(feature = "async-std")]
    pub async fn bind_async_std(self) -> Result<async_std::net::TcpListener, BindError> {
        match self.0 {
            SocketAddrInner::Ordinary(addr) => match async_std::net::TcpListener::bind(addr).await {
                Ok(socket) => Ok(socket),
                Err(error) => Err(BindErrorInner::BindFailed { addr, error, }.into()),
            },
            SocketAddrInner::WithHostname(addr) => match async_std::net::TcpListener::bind(addr.as_str()).await {
                Ok(socket) => Ok(socket),
                Err(error) => Err(BindErrorInner::BindOrResolvFailed { addr, error, }.into()),
            },
            SocketAddrInner::Systemd(socket_name) => {
                let (socket, _) = Self::get_systemd(socket_name)?;
                Ok(socket.into())
            },
        }
    }

    // We can't impl<T: Deref<Target=str> + Into<String>> TryFrom<T> for SocketAddr because of orphan
    // rules.
    fn try_from_generic<'a, T>(string: T) -> Result<Self, ParseError> where T: 'a + std::ops::Deref<Target=str> + Into<String> {
        if string.starts_with(SYSTEMD_PREFIX) {
            #[cfg(all(target_os = "linux", feature = "enable_systemd"))]
            {
                let name_len = string.len() - SYSTEMD_PREFIX.len();
                match string[SYSTEMD_PREFIX.len()..].chars().enumerate().find(|(_, c)| !c.is_ascii() || *c < ' ' || *c == ':') {
                    None if name_len <= 255 => Ok(SocketAddr(SocketAddrInner::Systemd(string.into()))),
                    None => Err(ParseErrorInner::LongSocketName { string: string.into(), len: name_len }.into()),
                    Some((pos, c)) => Err(ParseErrorInner::InvalidCharacter { string: string.into(), c, pos, }.into()),
                }
            }
            #[cfg(not(all(target_os = "linux", feature = "enable_systemd")))]
            {
                Err(ParseErrorInner::SystemdUnsupported(string.into()).into())
            }
        } else {
            match string.parse() {
                Ok(addr) => Ok(SocketAddr(SocketAddrInner::Ordinary(addr))),
                Err(_) => Ok(SocketAddr(SocketAddrInner::WithHostname(ResolvAddr::try_from_generic(string).map_err(ParseErrorInner::ResolvAddr)?))),
            }
        }
    }

    #[cfg(all(target_os = "linux", feature = "enable_systemd"))]
    fn get_systemd(socket_name: String) -> Result<(std::net::TcpListener, SocketAddrInner), BindError> {
        use libsystemd::activation::IsType;
        use std::os::unix::io::{FromRawFd, IntoRawFd};

        let socket = systemd_sockets::take(&socket_name[SYSTEMD_PREFIX.len()..]).map_err(BindErrorInner::ReceiveDescriptors)?;
        // Safety: The environment variable is unset, so that no other calls can get the
        // descriptors. The descriptors are taken from the map, not cloned, so they can't
        // be duplicated.
        unsafe {
            // match instead of combinators to avoid cloning socket_name
            match socket {
                Some(socket) if socket.is_inet() => Ok((std::net::TcpListener::from_raw_fd(socket.into_raw_fd()), SocketAddrInner::Systemd(socket_name))),
                Some(_) => Err(BindErrorInner::NotInetSocket(socket_name).into()),
                None => Err(BindErrorInner::MissingDescriptor(socket_name).into())
            }
        }
    }

    // This approach makes the rest of the code much simpler as it doesn't require sprinkling it
    // with #[cfg(all(target_os = "linux", feature = "enable_systemd"))] yet still statically guarantees it won't execute.
    #[cfg(not(all(target_os = "linux", feature = "enable_systemd")))]
    fn get_systemd(socket_name: Never) -> Result<(std::net::TcpListener, SocketAddrInner), BindError> {
        match socket_name {}
    }
}

/// Displays the address in format that can be parsed again.
///
/// **Important: While I don't expect this impl to change, don't rely on it!**
/// It should be used mostly for debugging/logging.
impl fmt::Display for SocketAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::Display for SocketAddrInner {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SocketAddrInner::Ordinary(addr) => fmt::Display::fmt(addr, f),
            SocketAddrInner::Systemd(addr) => fmt::Display::fmt(addr, f),
            SocketAddrInner::WithHostname(addr) => fmt::Display::fmt(addr, f),
        }
    }
}

// PartialEq for testing, I'm not convinced it should be exposed
#[derive(Debug, PartialEq)]
enum SocketAddrInner {
    Ordinary(std::net::SocketAddr),
    WithHostname(resolv_addr::ResolvAddr),
    #[cfg(all(target_os = "linux", feature = "enable_systemd"))]
    Systemd(String),
    #[cfg(not(all(target_os = "linux", feature = "enable_systemd")))]
    #[allow(dead_code)]
    Systemd(Never),
}

const SYSTEMD_PREFIX: &str = "systemd://";

impl<I: Into<std::net::IpAddr>> From<(I, u16)> for SocketAddr {
    fn from(value: (I, u16)) -> Self {
        SocketAddr(SocketAddrInner::Ordinary(value.into()))
    }
}

impl From<std::net::SocketAddrV4> for SocketAddr {
    fn from(value: std::net::SocketAddrV4) -> Self {
        SocketAddr(SocketAddrInner::Ordinary(value.into()))
    }
}

impl From<std::net::SocketAddrV6> for SocketAddr {
    fn from(value: std::net::SocketAddrV6) -> Self {
        SocketAddr(SocketAddrInner::Ordinary(value.into()))
    }
}

impl std::str::FromStr for SocketAddr {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        SocketAddr::try_from_generic(s)
    }
}

impl<'a> TryFrom<&'a str> for SocketAddr {
    type Error = ParseError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        SocketAddr::try_from_generic(s)
    }
}

impl TryFrom<String> for SocketAddr {
    type Error = ParseError;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        SocketAddr::try_from_generic(s)
    }
}

impl<'a> TryFrom<&'a OsStr> for SocketAddr {
    type Error = ParseOsStrError;

    fn try_from(s: &'a OsStr) -> Result<Self, Self::Error> {
        s.to_str().ok_or(ParseOsStrError::InvalidUtf8)?.try_into().map_err(Into::into)
    }
}

impl TryFrom<OsString> for SocketAddr {
    type Error = ParseOsStrError;

    fn try_from(s: OsString) -> Result<Self, Self::Error> {
        s.into_string().map_err(|_| ParseOsStrError::InvalidUtf8)?.try_into().map_err(Into::into)
    }
}

#[cfg(feature = "serde")]
impl<'a> TryFrom<serde_str_helpers::DeserBorrowStr<'a>> for SocketAddr {
    type Error = ParseError;

    fn try_from(s: serde_str_helpers::DeserBorrowStr<'a>) -> Result<Self, Self::Error> {
        SocketAddr::try_from_generic(s)
    }
}

#[cfg(feature = "parse_arg")]
impl parse_arg::ParseArg for SocketAddr {
    type Error = ParseOsStrError;

    fn describe_type<W: fmt::Write>(mut writer: W) -> fmt::Result {
        std::net::SocketAddr::describe_type(&mut writer)?;
        write!(writer, " or a systemd socket name prefixed with systemd://")
    }

    fn parse_arg(arg: &OsStr) -> Result<Self, Self::Error> {
        arg.try_into()
    }

    fn parse_owned_arg(arg: OsString) -> Result<Self, Self::Error> {
        arg.try_into()
    }
}

#[cfg(test)]
mod tests {
    use super::{SocketAddr, SocketAddrInner};

    #[test]
    fn parse_ordinary() {
        assert_eq!("127.0.0.1:42".parse::<SocketAddr>().unwrap().0, SocketAddrInner::Ordinary(([127, 0, 0, 1], 42).into()));
    }

    #[test]
    #[cfg(all(target_os = "linux", feature = "enable_systemd"))]
    fn parse_systemd() {
        assert_eq!("systemd://foo".parse::<SocketAddr>().unwrap().0, SocketAddrInner::Systemd("systemd://foo".to_owned()));
    }

    #[test]
    #[cfg(not(all(target_os = "linux", feature = "enable_systemd")))]
    #[should_panic]
    fn parse_systemd() {
        "systemd://foo".parse::<SocketAddr>().unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_systemd_fail_control() {
        "systemd://foo\n".parse::<SocketAddr>().unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_systemd_fail_colon() {
        "systemd://foo:".parse::<SocketAddr>().unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_systemd_fail_non_ascii() {
        "systemd://fooá".parse::<SocketAddr>().unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_systemd_fail_too_long() {
        "systemd://xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx".parse::<SocketAddr>().unwrap();
    }
}
