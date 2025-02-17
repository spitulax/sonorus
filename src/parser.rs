use crate::Args;
use std::fs::read_to_string;

mod error;
mod lexer;
mod lut;

pub use error::*;
use lexer::Lexer;

pub fn main(args: &Args) -> Result<()> {
    let content = read_to_string(&args.changes_file)?;
    let tokens = Lexer::tokenise(&content);
    println!("{tokens:#?}");

    Ok(())
}
