use clap::Parser;
use lexer::Lexer;
use std::{fs::read_to_string, process::ExitCode};

mod error;
mod lexer;
mod parser;
mod utils;

pub use error::*;
pub use utils::*;

#[derive(Parser, Debug)]
#[command(version)]
struct Args {
    /// Path to the sound changes file.
    changes_file: String,
}

fn start() -> Result<()> {
    let args = Args::parse();

    let content = read_to_string(&args.changes_file)?;
    let tokens = Lexer::tokenise(&content)?;
    for t in tokens {
        println!("{t}");
    }

    Ok(())
}

fn main() -> ExitCode {
    let error = start().err();
    if let Some(e) = error {
        eprintln!("{}", e);
        return 1.into();
    }
    return 0.into();
}
