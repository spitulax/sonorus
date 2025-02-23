use crate::{lexer, parser};
use derive_more::{Display, From};
use std::io;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, From, Display)]
pub enum Error {
    #[from]
    #[display("Parser: {_0}")]
    Parser(parser::Error),

    /// Should be unrecoverable or even unexpected.
    #[from]
    #[display("Lexer: {_0}")]
    Lexer(lexer::Error),

    #[from]
    #[display("IO: {_0}")]
    Io(io::Error),
}
