use super::lut;
use derive_more::{Display, From};
use std::{
    fmt,
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
    /// Tried to access invalid pending data for the current token.
    #[display("Tried to access invalid pending data for {_0:?}")]
    InvalidPendingData(TokenKind),

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
    Integer(usize),
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

impl fmt::Display for Loc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[derive(Copy, Clone, Default, Eq, PartialEq, Debug)]
pub enum TokenKind {
    #[default]
    /// # Data
    /// [`TokenData::String`]: The character (should only be a single character).
    Unknown,
    /// # Data
    /// None.
    Eof,
    /// # Data
    /// [`TokenData::Integer`]: The amount of indentation characters.
    Indent(IndentKind),
    /// # Data
    /// None.
    Newline,
    /// # Data
    /// [`TokenData::String`]: The string representing the number.
    Numeric,
    Identifier,
    Colon,
    Equals,
    LBracket,
    RBracket,
    LParen,
    RParen,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum IndentKind {
    Space,
    Tab,
}

impl From<char> for IndentKind {
    /// # Panics
    /// Panics if the character is neither a space or a tab.
    fn from(value: char) -> Self {
        match value {
            ' ' => IndentKind::Space,
            '\t' => IndentKind::Tab,
            _ => unreachable!(),
        }
    }
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

    /// Token data constructed before finalisation.
    pending_data: Option<TokenData<'a>>,
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
            pending_data: None,
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

    fn push_with_pending_data(&mut self) -> Result<()> {
        let data = self
            .pending_data
            .clone()
            .ok_or(Error::InvalidPendingData(self.cur_token.kind))?;
        self.push(Some(data))?;
        self.pending_data = None;
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

    fn do_new(&mut self) -> Result<()> {
        if let Some(c) = self.cur_char {
            if lut::NUMERIC.contains(c) {
                self.search(TokenKind::Numeric);
            } else if lut::NEWLINE.contains(c) {
                self.search(TokenKind::Newline);
            } else if lut::INDENT.contains(c) {
                if self.cur_loc.col == 1 {
                    // We need to know the indentation level, but not everyone uses the same amount of
                    // spaces. The indentation level will be figured out on parsing, the lexer only
                    // gives the amount of spaces.
                    // Indentation characters that are right next to each other are grouped into a
                    // single token.
                    self.pending_data = Some(TokenData::Integer(0));
                    self.search(TokenKind::Indent(c.into()));
                } else {
                    self.next()?;
                }
            } else {
                todo!();
            }
        } else {
            self.search(TokenKind::Eof);
        }

        Ok(())
    }

    fn do_search(&mut self) -> Result<()> {
        if let Some(c) = self.cur_char {
            // NOTE: Finalise any token when encountering newline
            match self.cur_token.kind {
                // TODO: Floats?
                TokenKind::Numeric => {
                    if lut::NUMERIC.contains(c) {
                        self.next()?;
                    } else {
                        self.finalise();
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
                TokenKind::Indent(kind) => {
                    if lut::INDENT.contains(c) && kind == c.into() {
                        self.pending_data = Some(
                            self.pending_data
                                .as_ref()
                                .and_then(|d| {
                                    if let TokenData::Integer(i) = d {
                                        Some(TokenData::Integer(i + 1))
                                    } else {
                                        None
                                    }
                                })
                                .ok_or(Error::InvalidPendingData(TokenKind::Indent(kind)))?,
                        );
                        self.next()?;
                    } else {
                        self.finalise();
                    }
                }
                _ => todo!(),
            }
        } else {
            self.finalise();
        }

        Ok(())
    }

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
            TokenKind::Indent(_) => self.push_with_pending_data()?,
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
                    lexer.do_new()?;
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
        /// [`None`] for filler, does not actually assert. Only for filling in skipped characters.
        kind: Option<TokenKind>,
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
                kind: Some(kind),
                data,
                len,
                len_byte,
            }
        }

        pub fn filler(len: usize, len_byte: usize) -> Self {
            Self {
                kind: None,
                data: None,
                len,
                len_byte,
            }
        }
    }

    fn filler(len: usize, len_byte: usize) -> Value<'static> {
        Value::filler(len, len_byte)
    }

    fn number(n: &str) -> Value {
        Value::new(
            TokenKind::Numeric,
            Some(TokenData::String(n)),
            n.len(),
            // Should be ASCII
            1 * n.len(),
        )
    }

    fn newline() -> Value<'static> {
        Value::new(
            TokenKind::Newline,
            None,
            1,
            // Should be ASCII
            1 * 1,
        )
    }

    fn indent(kind: IndentKind, n: usize) -> Value<'static> {
        Value::new(
            TokenKind::Indent(kind),
            Some(TokenData::Integer(n)),
            n,
            // Should be ASCII
            1 * n,
        )
    }

    fn assert_tokens(tokens: &[Token], values: &[Value]) {
        assert_eq!(
            tokens.len() - 1,
            values.iter().filter(|x| x.kind.is_some()).count(),
            "Expected non-filter `values` with the length of `tokens` length minus 1"
        );

        let mut cur_loc = Loc::new(1, 1);
        let mut cur_byte = 0;
        let mut i = 0;
        for value in values {
            let token = &tokens[i];

            if let Some(ref k) = value.kind {
                assert(
                    token,
                    k,
                    &value.data,
                    &cur_loc,
                    &cur_byte,
                    &value.len,
                    &value.len_byte,
                );

                i += 1;
            }

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

    macro_rules! error {
        ($token:expr, $($msg:tt)*) => {
            panic!("{}: {}", $token.start_loc, format!($($msg)*));
        };
    }

    macro_rules! eq {
        ($token:expr, $left:expr, $right:expr) => {
            if $left != $right {
                error!(
                    $token,
                    "`{} == {}` failed\nExpected {:?}, got {:?}",
                    stringify!($left),
                    stringify!($right),
                    $left,
                    $right,
                );
            }
        };
        ($token:expr, $left:expr, $right:expr, $($msg:tt)*) => {
            if $left != $right {
                error!($token, $($msg)* _l = $left, _r = $right);
            }
        };
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

        if let Some(ref f) = token.finalised {
            eq!(
                token,
                *kind,
                token.kind,
                "Expected token kind to be {_l:?}, is actually {_r:?}",
            );
            eq!(
                token,
                *start_loc,
                token.start_loc,
                "Expected token to start at {_l}, actually at {_r}",
            );
            eq!(
                token,
                *start_byte,
                token.start_byte,
                "Expected token to start at byte {_l}, actually at byte {_r}",
            );
            eq!(
                token,
                *data,
                f.data,
                "Expected token data to be {_l:?}, is actually {_r:?}",
            );
            eq!(
                token,
                *len,
                f.len,
                "Expected token length to be {_l} character(s), is actually {_r} character(s)",
            );
            eq!(
                token,
                *len_byte,
                f.len_byte,
                "Expected token length to be {_l} byte(s), is actually {_r} byte(s)",
            );
        } else {
            error!(token, "The token has not been finalised");
        }
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

    #[test]
    fn indentation() {
        let s = r#"
0

  1 2
    3   4
      5 6
        7   8

	1	2
		3	4

    	1
	    2
"#;

        let tokens = Lexer::tokenise(&s).unwrap();
        assert_tokens(
            &tokens,
            &[
                newline(),
                number("0"),
                newline(),
                newline(),
                indent(IndentKind::Space, 2),
                number("1"),
                filler(1, 1),
                number("2"),
                newline(),
                indent(IndentKind::Space, 4),
                number("3"),
                filler(3, 3),
                number("4"),
                newline(),
                indent(IndentKind::Space, 6),
                number("5"),
                filler(1, 1),
                number("6"),
                newline(),
                indent(IndentKind::Space, 8),
                number("7"),
                filler(3, 3),
                number("8"),
                newline(),
                newline(),
                indent(IndentKind::Tab, 1),
                number("1"),
                filler(1, 1),
                number("2"),
                newline(),
                indent(IndentKind::Tab, 2),
                number("3"),
                filler(1, 1),
                number("4"),
                newline(),
                newline(),
                indent(IndentKind::Space, 4),
                filler(1, 1),
                number("1"),
                newline(),
                indent(IndentKind::Tab, 1),
                filler(4, 4),
                number("2"),
                newline(),
            ],
        );
    }
}
