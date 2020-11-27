use std::process::Child;
use std::ffi::OsStr;
use std::io::{self, Read, Write};

pub trait Test {
    const SOCKET_ADDR: &'static str;

    fn spawn_slave(program_name: &OsStr) -> io::Result<Child>;
}

const REQUEST: &[u8] = b"orange coin";
const RESPONSE: &[u8] = b"good";

fn main_master(slave: io::Result<Child>) {
    let mut slave = slave.expect("failed to run systemd-socket-activate");

    // give slave some time to bind the socket just to be sure
    std::thread::sleep(std::time::Duration::from_secs(1));

    let mut client_socket = std::net::TcpStream::connect("127.0.0.1:4242").expect("Failed to connect to 127.0.0.1:4242");
    client_socket.write_all(REQUEST).expect("failed to send data");
    let mut buf = [0u8; RESPONSE.len()];
    client_socket.read_exact(&mut buf).expect("failed to read response");
    assert_eq!(buf, RESPONSE);

    let status = slave.wait().expect("faild to wait for slave");
    if !status.success() {
        panic!("slave did not exit with succcess, status: {}", status);
    }
}

fn main_slave(addr: &str) {
    use systemd_socket::SocketAddr;

    let socket = addr
        .parse::<SocketAddr>()
        .expect("failed to parse socket")
        .bind()
        .expect("failed to bind");

    let (mut client_socket, _) = socket.accept().expect("failed to accept");
    let mut buf = [0u8; REQUEST.len()];
    client_socket.read_exact(&mut buf).expect("failed to read response");
    assert_eq!(buf, REQUEST);
    client_socket.write_all(RESPONSE).expect("failed to send data");
}

pub fn main<T: Test>() {
    let mut args = std::env::args_os();
    let program_name = args.next().expect("missing program name");

    match std::env::var_os("SYSTEMD_SOCKET_INTEGRATION_TEST") {
        None => main_master(T::spawn_slave(&program_name)),
        Some(arg) if arg == "slave" => main_slave(T::SOCKET_ADDR),
        Some(arg) => panic!("Unknown argument '{:?}'", arg),
    }
}
