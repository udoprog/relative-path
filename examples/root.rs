use std::io::Read;

use anyhow::{Context, Result};

use relative_path::Root;

fn main() -> Result<()> {
    let root = Root::new("..").context("Opening root directory")?;

    let mut cargo_toml = root
        .open("relative-path/Cargo.toml")
        .context("Opening file")?;

    let mut contents = String::new();
    cargo_toml.read_to_string(&mut contents)?;
    println!("{:?}", contents);
    Ok(())
}
