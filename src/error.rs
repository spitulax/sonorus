use crate::parser;
use derive_more::{Display, From};

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, From, Display)]
pub enum Error {
    #[from]
    #[display("Parser: {_0}")]
    Parser(parser::Error),
}
