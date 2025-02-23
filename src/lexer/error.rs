use derive_more::{Display, From};

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Display, From)]
pub enum Error {
    #[display("Tried advancing at EOF")]
    AdvancingAtEof,
    #[display("Searched EOF token before actually reaching EOF")]
    PrematureEofToken,
    #[display("A token was separated by newline or empty")]
    EmptyToken,
    #[display("Tried to construct an invalid UTF-8 string")]
    InvalidUtf8,
    #[display("Tried to access invalid token data")]
    InvalidData,
}
