use super::lut;
use derive_more::{Display, From};
use std::{
    iter::Peekable,
    num::ParseFloatError,
    str::{from_utf8, Chars},
};

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Display, From)]
pub enum Error {
    /// Tried advancing at EOF.
    #[display("Tried advancing at EOF")]
    AdvancingAtEof,
    /// Searched EOF token before actually reaching EOF.
    #[display("Searched EOF token before actually reaching EOF")]
    PrematureEofToken,
    /// A token was separated by newline or empty.
    #[display("A token was separated by newline or empty")]
    UnfinalisedOrEmptyToken,
    /// Tried finalising at EOF for other than EOF token.
    #[display("Tried finalising at EOF for other than EOF token")]
    FinalisingEof,
    /// Tried to construct an invalid UTF-8 string.
    #[display("Tried to construct an invalid UTF-8 string")]
    InvalidUtf8,

    /// Number parsing errors.
    #[display("Number parsing: {_0}")]
    ParseFloat(ParseFloatError),
}

#[derive(Default, Debug, PartialEq)]
pub struct Token<'a> {
    kind: TokenKind,

    /// `start_loc` points at the first character.
    start_loc: Loc,
    start_byte: usize,

    /// [`Some`] after the token has been finalised.
    finalised: Option<TokenFinalised<'a>>,
}

// TODO: We're not using it yet
#[allow(dead_code)]
impl<'a> Token<'_> {
    /// Returns [`Some`] only if the token is already finalised.
    pub fn bytes(&self, s: &'a [u8]) -> Option<&'a [u8]> {
        self.finalised
            .as_ref()
            .map(|f| &s[self.start_byte..self.start_byte + f.len_byte])
    }

    /// Returns [`Some`] only if the token is already finalised and the resulting slice is a valid UTF-8.
    pub fn string(&self, s: &'a str) -> Option<&'a str> {
        self.bytes(s.as_bytes()).and_then(|b| from_utf8(b).ok())
    }
}

#[derive(Debug, PartialEq)]
pub struct TokenFinalised<'a> {
    data: Option<TokenData<'a>>,
    /// Length in characters
    len: usize,
    /// Length in bytes
    len_byte: usize,
}

impl Token<'_> {
    pub fn new(kind: TokenKind, start_loc: Loc, start_byte: usize) -> Self {
        Self {
            kind,
            start_loc,
            start_byte,
            finalised: None,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TokenData<'a> {
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
    Eof,
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
        // NOTE: Only `TokenKind::Eof` is zero-sized
        if self.cur_token.kind != TokenKind::Eof && self.cur_loc.col <= self.cur_token.start_loc.col
        {
            return Err(Error::UnfinalisedOrEmptyToken);
        }

        Ok(Token {
            kind: self.cur_token.kind,
            start_loc: self.cur_token.start_loc,
            start_byte: self.cur_token.start_byte,
            finalised: Some(TokenFinalised {
                data,
                len: self.cur_loc.col - self.cur_token.start_loc.col,
                len_byte: self.cur_byte - self.cur_token.start_byte,
            }),
        })
    }

    fn push(&mut self, data: Option<TokenData<'a>>) -> Result<()> {
        self.tokens.push(self.finalise_token(data)?);
        self.next_state = State::New;
        Ok(())
    }

    /// # Errors
    /// Returns [`Error::AdvancingAtEof`] if it is used
    /// when [`Self::cur_char`] is indicating Eof.
    fn next(&mut self) -> Result<()> {
        let c = if let Some(c) = self.cur_char {
            c
        } else {
            return Err(Error::AdvancingAtEof);
        };
        self.cur_byte += c.len_utf8();
        self.cur_loc.col += 1;
        self.cur_char = self.iter.next();
        Ok(())
    }

    /// # Errors
    /// Returns [`Error::InvalidUtf8`] if [`Self::cur_byte`] is not incremented correctly,
    /// thus this function may slice a character that's more than a byte halfway through.
    fn cur_token_as_str(&self) -> Result<&'a str> {
        self.str
            .get(self.cur_token.start_byte..self.cur_byte)
            .ok_or(Error::InvalidUtf8)
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
            self.search(TokenKind::Eof);
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
                TokenKind::Eof => return Err(Error::PrematureEofToken),
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
    /// This function returns `true` if it reaches Eof.
    fn do_finalise(&mut self) -> Result<bool> {
        //let start_loc = self.cur_token.start_loc;
        //let end_loc = self.cur_loc;

        match self.cur_token.kind {
            TokenKind::Numeric => {
                // It shouldn't be parsed here.
                let s = self.cur_token_as_str()?;
                self.push(Some(TokenData::String(s)))?;
            }
            TokenKind::Eof => {
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

// TODO: Test non-ASCII characters
#[cfg(test)]
mod test {
    use super::*;

    struct Value<'a> {
        kind: TokenKind,
        data: Option<TokenData<'a>>,
        len: usize,
        len_byte: usize,
    }

    impl<'a> Value<'a> {
        pub fn new(
            kind: TokenKind,
            data: Option<TokenData<'a>>,
            len: usize,
            len_byte: usize,
        ) -> Self {
            Self {
                kind,
                data,
                len,
                len_byte,
            }
        }
    }

    fn assert_tokens(tokens: &[Token], values: &[Value]) {
        assert_eq!(
            tokens.len() - 1,
            values.len(),
            "Expected `values` with the length of `tokens` length minus 1"
        );

        let mut cur_loc = Loc::new(1, 1);
        let mut cur_byte = 0;
        for (token, value) in tokens.iter().zip(values) {
            assert(
                token,
                &value.kind,
                &value.data,
                &cur_loc,
                &cur_byte,
                &value.len,
                &value.len_byte,
            );
            cur_loc = Loc::new(cur_loc.line, cur_loc.col + value.len);
            cur_byte += value.len_byte;

            if token.kind == TokenKind::Newline {
                cur_loc.line += 1;
                cur_loc.col = 1;
            }
        }
        assert_eof(&tokens.last().unwrap(), &cur_loc, &cur_byte);
    }

    fn assert_eof(token: &Token, start_loc: &Loc, start_byte: &usize) {
        assert(token, &TokenKind::Eof, &None, start_loc, start_byte, &0, &0);
    }

    fn assert(
        token: &Token,
        kind: &TokenKind,
        data: &Option<TokenData>,
        start_loc: &Loc,
        start_byte: &usize,
        len: &usize,
        len_byte: &usize,
    ) {
        // NOTE: Keep track of fields
        let _ = Token {
            kind: TokenKind::default(),
            start_loc: Loc::new(0, 0),
            start_byte: 0,
            finalised: Some(TokenFinalised {
                data: None,
                len: 0,
                len_byte: 0,
            }),
        };

        assert!(token.finalised.is_some(), "The token is not finalised");
        let f = token.finalised.as_ref().unwrap();
        assert_eq!(token.kind, *kind);
        assert_eq!(token.start_loc, *start_loc);
        assert_eq!(token.start_byte, *start_byte);
        assert_eq!(f.data, *data);
        assert_eq!(f.len, *len);
        assert_eq!(f.len_byte, *len_byte);
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
                &[Value::new(
                    TokenKind::Numeric,
                    Some(TokenData::String(&s)),
                    i,
                    // The numbers should be ASCII...
                    1 * i,
                )],
            );
        }
    }

    #[test]
    fn unknown_token() {
        for i in 1..=10 {
            let s = (0..i).map(|_| '\r').collect::<String>();
            let v = (0..i)
                .map(|_| Value::new(TokenKind::Unknown, Some(TokenData::String("\r")), 1, 1))
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
                &[Value::new(
                    TokenKind::Newline,
                    None,
                    s.len(),
                    // Should be ASCII
                    1 * s.len(),
                )],
            );
        }
    }

    #[test]
    fn newline_and_number() {
        let number = || Value::new(TokenKind::Numeric, Some(TokenData::String("1024")), 4, 4);
        let newline = |n: &str| {
            Value::new(
                TokenKind::Newline,
                None,
                n.len(),
                // Should be ASCII
                1 * n.len(),
            )
        };

        for n in &["\n", "\r\n"] {
            let s = format!("1024{n}");
            let tokens = Lexer::tokenise(&s).unwrap();
            assert_tokens(&tokens, &[number(), newline(n)]);
        }

        for n in &["\n", "\r\n"] {
            let s = format!("{n}1024");
            let tokens = Lexer::tokenise(&s).unwrap();
            assert_tokens(&tokens, &[newline(n), number()]);
        }
    }

    #[test]
    fn token_string() {
        let number = |n| {
            Value::new(
                TokenKind::Numeric,
                Some(TokenData::String(n)),
                4,
                // ASCII
                1 * 4,
            )
        };
        let newline = || {
            Value::new(
                TokenKind::Newline,
                None,
                1,
                // ASCII
                1 * 1,
            )
        };

        let s = "1024\n2048\n";
        let tokens = Lexer::tokenise(&s).unwrap();
        assert_tokens(
            &tokens,
            &[number("1024"), newline(), number("2048"), newline()],
        );

        for (token, token_str) in tokens.iter().zip(&["1024", "\n", "2048", "\n"]) {
            let bytes = token.bytes(&s.as_bytes()).unwrap();
            let string = token.string(&s).unwrap();
            assert_eq!(bytes, token_str.as_bytes());
            assert_eq!(string, *token_str);
        }
    }
}
