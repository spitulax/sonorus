use super::lut;
use derive_more::{Display, From};
use std::{
    iter::Peekable,
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
    /// Tried finalising at EOF for other than EOF token.
    #[display("Tried finalising at EOF for other than EOF token")]
    FinalisingEOF,

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
    start_loc: Loc,
    start_byte: usize,
    len: usize,
}

impl Token<'_> {
    pub fn new(kind: TokenKind, start_loc: Loc, start_byte: usize) -> Self {
        Self {
            kind,
            data: None,
            start_loc,
            start_byte,
            len: 0,
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
#[allow(dead_code)]
pub enum TokenKind {
    #[default]
    Unknown,
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
    /// Location in bytes, zero indexed
    cur_byte: usize,
    /// Location in chars, one indexed
    cur_loc: Loc,

    str: &'a str,
    iter: Peekable<Chars<'a>>,

    cur_state: State,
    next_state: State,

    cur_token: Token<'a>,
    cur_char: Option<char>,

    tokens: Vec<Token<'a>>,
}

impl<'a> Lexer<'a> {
    fn new(str: &'a str) -> Self {
        let mut ret = Self {
            cur_byte: 0,
            cur_loc: Loc::new(1, 1),
            str,
            iter: str.chars().peekable(),
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
        self.cur_token = Token::new(token_kind, self.cur_loc, self.cur_byte);
        self.next_state = State::Search;
    }

    fn finalise(&mut self) {
        self.next_state = State::Finalise
    }

    fn finalise_token(&self, data: Option<TokenData<'a>>) -> Result<Token<'a>> {
        // NOTE: Only `TokenKind::EOF` is zero-sized
        if self.cur_token.kind != TokenKind::EOF && self.cur_loc.col <= self.cur_token.start_loc.col
        {
            return Err(Error::UnfinalisedOrEmptyToken);
        }

        Ok(Token {
            data,
            kind: self.cur_token.kind,
            start_loc: self.cur_token.start_loc,
            start_byte: self.cur_token.start_byte,
            len: self.cur_loc.col - self.cur_token.start_loc.col,
        })
    }

    fn push(&mut self, data: Option<TokenData<'a>>) -> Result<()> {
        self.tokens.push(self.finalise_token(data)?);
        self.next_state = State::New;
        Ok(())
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
        self.cur_byte += c.len_utf8();
        self.cur_loc.col += 1;
        self.cur_char = self.iter.next();
        Ok(())
    }

    /// # Errors
    /// This function may return [`Error::Utf8`].
    /// One possibility is [`Self::i`] is not incremented correctly,
    /// thus this function may slice a character halfway.
    fn cur_token_as_str(&self) -> Result<&'a str> {
        Ok(from_utf8(
            &self.str.as_bytes()[self.cur_token.start_byte..self.cur_byte],
        )?)
    }

    fn do_new(&mut self) {
        if let Some(c) = self.cur_char {
            if lut::NUMERIC.contains(c) {
                self.search(TokenKind::Numeric);
            } else if lut::NEWLINE.contains(c) {
                self.search(TokenKind::Newline);
            } else {
                todo!();
            }
        } else {
            self.search(TokenKind::EOF);
        }
    }

    fn do_search(&mut self) -> Result<()> {
        if let Some(c) = self.cur_char {
            // NOTE: Finalise any token when encountering newline
            match self.cur_token.kind {
                // TODO: Floats?
                TokenKind::Numeric => {
                    if !lut::NUMERIC.contains(c) {
                        self.finalise();
                    } else {
                        self.next()?;
                    }
                }
                TokenKind::EOF => return Err(Error::PrematureEOFToken),
                TokenKind::Newline => {
                    if c == '\r' {
                        let next = self.iter.peek().cloned().unwrap_or('\0');
                        if next == '\n' {
                            self.next()?;
                            self.next()?;
                            self.finalise();
                        } else {
                            self.search(TokenKind::Unknown);
                        }
                    } else if c == '\n' {
                        self.next()?;
                        self.finalise();
                    }
                }
                TokenKind::Unknown => {
                    self.next()?;
                    self.finalise();
                }
                _ => todo!(),
            }
        } else {
            self.finalise();
        }

        Ok(())
    }

    /// # Return
    /// This function returns `true` if it reaches EOF.
    fn do_finalise(&mut self) -> Result<bool> {
        //let start_loc = self.cur_token.start_loc;
        //let end_loc = self.cur_loc;

        match self.cur_token.kind {
            TokenKind::Numeric => {
                let number = self.cur_token_as_str()?.parse::<f64>()?;
                self.push(Some(TokenData::Number(number)))?;
            }
            TokenKind::EOF => {
                self.push(None)?;
                return Ok(true);
            }
            TokenKind::Newline => {
                self.push(None)?;
                self.cur_loc.line += 1;
                self.cur_loc.col = 1;
            }
            TokenKind::Unknown => {
                let s = self.cur_token_as_str()?;
                self.push(Some(TokenData::String(s)))?;
            }
            _ => todo!(),
        }

        Ok(false)
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
                    lexer.do_new();
                }
                State::Search => {
                    lexer.do_search()?;
                }
                State::Finalise => {
                    if lexer.do_finalise()? {
                        return Ok(lexer.tokens);
                    };
                }
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
            assert(token, &value.kind, &value.data, &cur_loc, &value.len);
            cur_loc = end_loc;

            if token.kind == TokenKind::Newline {
                cur_loc.line += 1;
                cur_loc.col = 1;
            }
        }
        assert_eof(&tokens.last().unwrap(), &cur_loc);
    }

    fn assert_eof(token: &Token, start_loc: &Loc) {
        assert(token, &TokenKind::EOF, &None, start_loc, &0);
    }

    // NOTE: Ignoring `start_byte`
    fn assert(
        token: &Token,
        kind: &TokenKind,
        data: &Option<TokenData>,
        start_loc: &Loc,
        len: &usize,
    ) {
        // NOTE: Keep track of fields
        let _ = Token {
            kind: TokenKind::default(),
            data: None,
            start_loc: Loc::new(0, 0),
            len: 0,
            start_byte: 0,
        };

        assert_eq!(token.kind, *kind);
        assert_eq!(token.data, *data);
        assert_eq!(token.start_loc, *start_loc);
        assert_eq!(token.len, *len);
    }

    #[test]
    fn empty() {
        let tokens = Lexer::tokenise("").unwrap();
        assert_tokens(&tokens, &[]);
    }

    #[test]
    fn integer_number() {
        for i in 1..=10 {
            let s = (0..i)
                .map(|x| char::from_digit(x as u32, 10).unwrap())
                .collect::<String>();

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

    #[test]
    fn unknown_token() {
        for i in 1..=10 {
            let s = (0..i).map(|_| '\r').collect::<String>();
            let v = (0..i)
                .map(|_| Value {
                    kind: TokenKind::Unknown,
                    data: Some(TokenData::String("\r")),
                    len: 1,
                })
                .collect::<Vec<Value>>();

            let tokens = Lexer::tokenise(&s).unwrap();
            assert_tokens(&tokens, &v);
        }
    }

    #[test]
    fn lone_newline() {
        for s in &["\n", "\r\n"] {
            let tokens = Lexer::tokenise(&s).unwrap();
            assert_tokens(
                &tokens,
                &[Value {
                    kind: TokenKind::Newline,
                    data: None,
                    len: s.len(),
                }],
            );
        }
    }

    #[test]
    fn newline_and_number() {
        for n in &["\n", "\r\n"] {
            let s = format!("1024{n}");
            let tokens = Lexer::tokenise(&s).unwrap();
            assert_tokens(
                &tokens,
                &[
                    Value {
                        kind: TokenKind::Numeric,
                        data: Some(TokenData::Number(1024.0)),
                        len: 4,
                    },
                    Value {
                        kind: TokenKind::Newline,
                        data: None,
                        len: n.len(),
                    },
                ],
            );
        }

        for n in &["\n", "\r\n"] {
            let s = format!("{n}1024");
            let tokens = Lexer::tokenise(&s).unwrap();
            assert_tokens(
                &tokens,
                &[
                    Value {
                        kind: TokenKind::Newline,
                        data: None,
                        len: n.len(),
                    },
                    Value {
                        kind: TokenKind::Numeric,
                        data: Some(TokenData::Number(1024.0)),
                        len: 4,
                    },
                ],
            );
        }
    }
}
