use clap::Parser;
use std::process::exit;

mod error;
mod parser;

pub use error::*;

#[derive(Parser, Debug)]
#[command(version)]
struct Args {
    /// Path to the sound changes file.
    changes_file: String,
}

fn start() -> Result<()> {
    let args = Args::parse();
    parser::main(&args)?;

    Ok(())
}

fn main() {
    let error = start().err();
    if let Some(e) = error {
        eprintln!("{}", e);
        exit(1);
    }
}
