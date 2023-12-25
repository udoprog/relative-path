use std::io::{Read, Seek, Write};

use anyhow::{Context, Result};

use relative_path::Root;

fn main() -> Result<()> {
    let root = Root::open(".")?;

    let mut cargo_toml = root
        .open_options()
        .write(true)
        .append(true)
        .open("test.txt")
        .context("Opening file")?;

    let mut contents = String::new();
    // cargo_toml.seek(std::io::SeekFrom::Start(0))?;
    cargo_toml.write_all(b"Bye!\n")?;
    println!("{:?}", contents);
    Ok(())
}
