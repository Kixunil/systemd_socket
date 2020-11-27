// This integration test requires presence of systemd-socket-activate

use std::io;
use std::ffi::OsStr;
use std::process::{Command, Child};

mod comm;

enum Test {}

impl comm::Test for Test {
    const SOCKET_ADDR: &'static str = "systemd://secret_socket_of_satoshi_nakamoto";

    fn spawn_slave(program_name: &OsStr) -> io::Result<Child> {
        Command::new("systemd-socket-activate")
            .arg("-l")
            .arg("127.0.0.1:4242")
            .arg("--fdname=secret_socket_of_satoshi_nakamoto")
            .arg("--setenv=SYSTEMD_SOCKET_INTEGRATION_TEST=slave")
            .arg(program_name)
            .spawn()
    }
}

#[test]
fn main() {
    comm::main::<Test>();
}
