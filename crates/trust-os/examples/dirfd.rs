use std::io::{Read, Write};

use trust_os::{DirFd, UnixMode};

fn main() -> std::io::Result<()> {
    let tmp = tempfile::tempdir()?;
    let dir = DirFd::open(tmp.path())?;

    let mut file = dir.create_file("artifact.txt", UnixMode::OWNER_READ_WRITE)?;
    file.write_all(b"verified\n")?;
    drop(file);

    let identity = dir.identity("artifact.txt")?;
    println!("identity: dev={} ino={}", identity.device(), identity.inode());

    let mut reopened = dir.open_file("artifact.txt")?;
    let mut contents = String::new();
    reopened.read_to_string(&mut contents)?;
    print!("{contents}");

    dir.remove_file("artifact.txt")?;
    Ok(())
}
