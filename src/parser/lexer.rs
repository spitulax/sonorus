use super::lut::NUMERIC_LUT;
use derive_more::{Display, From};
use std::{
    num::ParseFloatError,
    str::{from_utf8, Chars, Utf8Error},
};

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Display, From)]
pub enum Error {
    /// Tried advancing at EOF.
    #[display("Tried advancing at EOF")]
    AdvancingAtEOF,
    /// Searched EOF token before actually reaching EOF.
    #[display("Searched EOF token before actually reaching EOF")]
    PrematureEOFToken,
    /// A token was separated by newline or empty.
    #[display("A token was separated by newline or empty")]
    UnfinalisedOrEmptyToken,

    /// UTF-8 encoding errors.
    #[display("UTF-8: {_0}")]
    Utf8(Utf8Error),

    /// Number parsing errors.
    #[display("Number parsing: {_0}")]
    ParseFloat(ParseFloatError),
}

#[derive(Default, Debug, PartialEq)]
pub struct Token<'a> {
    kind: TokenKind,
    data: Option<TokenData<'a>>,

    /// `start_loc` points at the first character.
    /// `end_loc` points after the last character.
    /// `[start_loc, end_loc)`.
    start_loc: Loc,
    end_loc: Loc,
}

impl Token<'_> {
    pub fn new(kind: TokenKind, start_loc: Loc) -> Self {
        Self {
            kind,
            data: None,
            start_loc,
            end_loc: Loc::new(0, 0),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TokenData<'a> {
    Number(f64),
    String(&'a str),
}

#[derive(Copy, Clone, Default, Debug, Eq, PartialEq)]
pub struct Loc {
    line: usize,
    col: usize,
}

impl Loc {
    pub fn new(line: usize, col: usize) -> Self {
        Self { line, col }
    }
}

#[derive(Copy, Clone, Default, Eq, PartialEq, Debug)]
pub enum TokenKind {
    #[default]
    EOF,
    Indent,
    Newline,
    Identifier,
    Numeric,
    Colon,
    Equals,
    LBracket,
    RBracket,
    LParen,
    RParen,
}

#[derive(Copy, Clone, Debug)]
enum State {
    New,
    Search,
    Finalise,
}

pub struct Lexer<'a> {
    /// In bytes, zero indexed
    i: usize,
    /// In chars, one indexed
    cur_loc: Loc,

    str: &'a str,
    iter: Chars<'a>,

    cur_state: State,
    next_state: State,

    cur_token: Token<'a>,
    cur_char: Option<char>,

    tokens: Vec<Token<'a>>,
}

impl<'a> Lexer<'a> {
    fn new(str: &'a str) -> Self {
        let mut ret = Self {
            i: 0,
            cur_loc: Loc::new(1, 1),
            str,
            iter: str.chars(),
            cur_state: State::New,
            next_state: State::New,
            cur_token: Token::default(),
            cur_char: None,
            tokens: vec![],
        };
        ret.cur_char = ret.iter.next();

        ret
    }

    fn search(&mut self, token_kind: TokenKind) {
        self.cur_token = Token::new(token_kind, self.cur_loc);
        self.next_state = State::Search;
    }

    fn finalise(&mut self) {
        self.next_state = State::Finalise
    }

    fn finalise_token(&self, data: Option<TokenData<'a>>) -> Token<'a> {
        Token {
            data,
            kind: self.cur_token.kind,
            start_loc: self.cur_token.start_loc,
            end_loc: self.cur_loc,
        }
    }

    fn push(&mut self, data: Option<TokenData<'a>>) {
        self.tokens.push(self.finalise_token(data));
        self.next_state = State::New;
    }

    /// # Errors
    /// This function will return [`Error::AdvancingAtEOF`] if it is used
    /// when [`Self::cur_char`] is indicating EOF.
    fn next(&mut self) -> Result<()> {
        let c = if let Some(c) = self.cur_char {
            c
        } else {
            return Err(Error::AdvancingAtEOF);
        };
        self.i += c.len_utf8();
        self.cur_loc.col += 1;
        self.cur_char = self.iter.next();
        Ok(())
    }

    /// # Errors
    /// This function will return an error if the code does not run the logic
    /// as expected. Thus, the error should be unrecoverable.
    /// In any other cases that it does not violate the logic, it should
    /// never error and may return some kind of bizzare looking tokens instead.
    pub fn tokenise(str: &'a str) -> Result<Vec<Token<'a>>> {
        let mut lexer = Self::new(str);

        loop {
            match lexer.cur_state {
                State::New => {
                    if let Some(c) = lexer.cur_char {
                        if NUMERIC_LUT.contains(c) {
                            lexer.search(TokenKind::Numeric);
                        } else {
                            todo!();
                        }
                    } else {
                        lexer.search(TokenKind::EOF);
                    }
                }
                State::Search => {
                    if let Some(c) = lexer.cur_char {
                        match lexer.cur_token.kind {
                            TokenKind::Numeric => {
                                if !NUMERIC_LUT.contains(c) {
                                    lexer.finalise();
                                } else {
                                    lexer.next()?;
                                }
                            }
                            TokenKind::EOF => return Err(Error::PrematureEOFToken),
                            _ => todo!(),
                        }
                    } else {
                        lexer.finalise();
                    }
                }
                State::Finalise => match lexer.cur_token.kind {
                    TokenKind::Numeric => {
                        let start_loc = lexer.cur_token.start_loc;
                        let end_loc = lexer.cur_loc;
                        // We should finalise the token when encountering newline
                        if end_loc.col <= start_loc.col {
                            return Err(Error::UnfinalisedOrEmptyToken);
                        }

                        let number =
                            from_utf8(&lexer.str.as_bytes()[0..lexer.i])?.parse::<f64>()?;

                        lexer.push(Some(TokenData::Number(number)));
                    }
                    TokenKind::EOF => {
                        lexer.push(None);
                        return Ok(lexer.tokens);
                    }
                    _ => todo!(),
                },
            }

            lexer.cur_state = lexer.next_state;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    struct Value<'a> {
        kind: TokenKind,
        data: Option<TokenData<'a>>,
        len: usize,
    }

    fn assert_tokens(tokens: &[Token], values: &[Value]) {
        assert_eq!(
            tokens.len() - 1,
            values.len(),
            "Expected `values` with the length of `tokens` length minus 1"
        );

        let mut cur_loc = Loc::new(1, 1);
        for (token, value) in tokens.iter().zip(values) {
            let end_loc = Loc::new(cur_loc.line, cur_loc.col + value.len);
            assert_eq!(
                *token,
                Token {
                    kind: value.kind,
                    data: value.data.clone(),
                    start_loc: cur_loc,
                    // Tokens should not cross newline. Right?
                    end_loc,
                }
            );
            cur_loc = end_loc;
        }
        assert_eof(&tokens.last().unwrap(), cur_loc);
    }

    fn assert_eof(token: &Token, start_loc: Loc) {
        assert_eq!(
            *token,
            Token {
                kind: TokenKind::EOF,
                data: None,
                // EOFs should be zero-length
                start_loc,
                end_loc: start_loc,
            }
        );
    }

    #[test]
    fn empty() {
        let tokens = Lexer::tokenise("").unwrap();
        assert_tokens(&tokens, &[]);
    }

    #[test]
    fn integer_number() {
        for i in 1..=10 {
            let mut s = String::with_capacity(i);
            for j in 0..i {
                s.push(char::from_digit(j as u32, 10).unwrap());
            }

            let tokens = Lexer::tokenise(&s).unwrap();
            assert_tokens(
                &tokens,
                &[Value {
                    kind: TokenKind::Numeric,
                    data: Some(TokenData::Number(s.parse().unwrap())),
                    len: i,
                }],
            );
        }
    }
}
