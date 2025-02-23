use std::{
    fmt,
    iter::Peekable,
    str::{from_utf8, Chars},
};

mod error;
mod lut;

#[cfg(test)]
mod tests;

pub use error::*;

#[derive(Default, Debug, PartialEq)]
pub struct Token<'a> {
    kind: TokenKind,

    /// `start_loc` points at the first character.
    start_loc: Loc,
    start_byte: usize,

    /// [`Some`] after the token has been finalised.
    finalised: Option<TokenFinalised<'a>>,
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({:?}, {}", self.kind, self.start_loc)?;
        if let Some(ref fin) = self.finalised {
            write!(f, ", {:?}", fin.data)?;
        }
        write!(f, ")")?;
        Ok(())
    }
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
    /// # Data
    /// [`TokenData::String`]: The character (should only be a single character).
    #[default]
    Unknown,
    Eof,
    /// # Data
    /// [`TokenData::Integer`]: The amount of indentation characters.
    Indent(IndentKind),
    Newline,
    /// # Data
    /// [`TokenData::String`]: The string representing the number.
    Numeric,
    Colon,
    Equals,
    LBracket,
    RBracket,
    LParen,
    RParen,
    /// # Data
    /// [`TokenData::String`]: The identifier string.
    Identifier,
    /// # Data
    /// [`TokenData::String`]: The identifier string (character by character, including the quotes).
    QuotedIdent,
    DollarSign,
    Question,
    Period,
    /// # Data
    /// [`TokenData::String`]: The comment string (including the opening hash symbol).
    // TODO: Multiline comment?
    Comment,
}

impl TokenKind {
    //pub fn is_single_char(&self) -> bool {
    //    match self {
    //        Self::Colon
    //        | Self::Equals
    //        | Self::LBracket
    //        | Self::RBracket
    //        | Self::LParen
    //        | Self::RParen => true,
    //        _ => false,
    //    }
    //}

    /// Get a single-character token kind.
    pub fn char(c: char) -> Option<Self> {
        match c {
            ':' => Some(Self::Colon),
            '=' => Some(Self::Equals),
            '[' => Some(Self::LBracket),
            ']' => Some(Self::RBracket),
            '(' => Some(Self::LParen),
            ')' => Some(Self::RParen),
            '$' => Some(Self::DollarSign),
            '?' => Some(Self::Question),
            '.' => Some(Self::Period),
            _ => None,
        }
    }
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

    inside_quotes: bool,
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
            inside_quotes: false,
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
            .take()
            .ok_or(Error::InvalidPendingData(self.cur_token.kind))?;
        self.push(Some(data))?;
        Ok(())
    }

    fn push_with_token_str(&mut self) -> Result<()> {
        let s = self.cur_token_as_str()?;
        self.push(Some(TokenData::String(s)))?;
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
            if c == '#' {
                self.search(TokenKind::Comment);
            } else if lut::NUMERIC.contains(c) {
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
            } else if let Some(k) = TokenKind::char(c) {
                self.search(k);
            } else if c == '"' {
                // Escaping should be done after tokenising.
                self.search(TokenKind::QuotedIdent);
            } else if is_valid_ident(c) {
                self.search(TokenKind::Identifier);
            } else {
                self.next()?;
            }
        } else {
            self.search(TokenKind::Eof);
        }

        Ok(())
    }

    fn do_search(&mut self) -> Result<()> {
        if let Some(c) = self.cur_char {
            // NOTE: Tokens should be finalised when encountering newline

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
                TokenKind::Colon
                | TokenKind::Equals
                | TokenKind::LBracket
                | TokenKind::RBracket
                | TokenKind::LParen
                | TokenKind::RParen
                | TokenKind::DollarSign
                | TokenKind::Question
                | TokenKind::Period => {
                    self.next()?;
                    self.finalise();
                }
                TokenKind::QuotedIdent => {
                    if c == '"' {
                        if !self.inside_quotes {
                            self.inside_quotes = true;
                            self.next()?;
                        } else {
                            self.inside_quotes = false;
                            self.next()?;
                            self.finalise();
                        }
                    } else if self.inside_quotes {
                        self.next()?;
                    }
                }
                TokenKind::Identifier => {
                    if is_valid_ident(c) {
                        self.next()?;
                    } else {
                        self.finalise();
                    }
                }
                TokenKind::Comment => {
                    if !lut::NEWLINE.contains(c) {
                        self.next()?;
                    } else {
                        self.finalise();
                    }
                }
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
            // Numeric tokens should not be parsed here.
            TokenKind::Numeric
            // The [`TokenData`] still contains the quotes.
            | TokenKind::QuotedIdent
            | TokenKind::Identifier
            | TokenKind::Unknown => self.push_with_token_str()?,
            TokenKind::Colon
            | TokenKind::Equals
            | TokenKind::LBracket
            | TokenKind::RBracket
            | TokenKind::LParen
            | TokenKind::RParen
            | TokenKind::DollarSign
            | TokenKind::Question
            | TokenKind::Period => self.push(None)?,
            TokenKind::Indent(_) => self.push_with_pending_data()?,
            TokenKind::Eof => {
                self.push(None)?;
                return Ok(true);
            }
            TokenKind::Newline => {
                self.push(None)?;
                self.cur_loc.line += 1;
                self.cur_loc.col = 1;
            }
            TokenKind::Comment => self.push_with_token_str()?,
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

/// # Valid Characters
/// All characters are valid to be part of (unquoted) identifier except control characters, tab,
/// and space. These invalid characters can act like separators.
fn is_valid_ident(c: char) -> bool {
    // TODO: Escaping
    // I'm still not really sure about this
    !(c.is_control() || lut::INDENT.contains(c) || TokenKind::char(c).is_some())
}
