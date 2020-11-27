# systemd socket

A convenience crate for optionally supporting systemd socket activation.

## About

The goal of this crate is to make socket activation with systemd in your project trivial.
It provides a replacement for `std::net::SocketAddr` that allows parsing the bind address from string just like the one from `std`
but on top of that also allows `systemd://socket_name` format that tells it to use systemd activation with given socket name.
Then it provides a method to bind the address which will return the socket from systemd if available.

The provided type supports conversions from various types of strings and also `serde` and `parse_arg` via feature flag.
Thanks to this the change to your code should be minimal - parsing will continue to work, it'll just allow a new format.
You only need to change the code to use `SocketAddr::bind()` instead of `TcpListener::bind()` for binding.

Further, the crate also provides methods for binding `tokio` 0.2, 0.3, and `async_std` sockets if the appropriate features are
activated.

## Example

```rust
use systemd_socket::SocketAddr;
use std::convert::TryFrom;
use std::io::Write;

let mut args = std::env::args_os();
let program_name = args.next().expect("unknown program name");
let socket_addr = args.next().expect("missing socket address");
let socket_addr = SocketAddr::try_from(socket_addr).expect("failed to parse socket address");
let socket = socket_addr.bind().expect("failed to bind socket");

loop {
    let _ = socket
    .accept()
    .expect("failed to accept connection")
    .0
    .write_all(b"Hello world!")
    .map_err(|err| eprintln!("Failed to send {}", err));
}
```

## Features

* `serde` - implements `serde::Deserialize` for `SocketAddr`
* `parse_arg` - implements `parse_arg::ParseArg` for `SocketAddr`
* `tokio_0_2` - adds `bind_tokio_0_2` method to `SocketAddr`
* `tokio_0_3` - adds `bind_tokio_0_3` method to `SocketAddr`
* `async_std` - adds `bind_async_std` method to `SocketAddr`

## MSRV

This crate must always compile with the latest Rust available in the latest Debian stable.
That is currently Rust 1.41.1. (Debian 10 - Buster)

## License

MITNFA
