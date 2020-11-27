use std::io;
use std::ffi::OsStr;
use std::process::{Command, Child};

mod comm;

enum Test {}

impl comm::Test for Test {
    const SOCKET_ADDR: &'static str = "localhost:4242";

    fn spawn_slave(program_name: &OsStr) -> io::Result<Child> {
        Command::new(program_name)
            .env("SYSTEMD_SOCKET_INTEGRATION_TEST", "slave")
            .spawn()
    }
}

#[test]
fn main() {
    comm::main::<Test>();
}
