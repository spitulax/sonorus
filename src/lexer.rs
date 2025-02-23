use crate::{
    loc::Loc,
    span::{Span, SpanStr},
};
use std::{fmt, iter::Peekable, str::Chars};

mod error;
mod lut;

#[cfg(test)]
mod tests;

pub use error::*;

type SpanLoc = Span<Loc>;

#[derive(Default, Debug, PartialEq)]
pub struct Token<'a> {
    kind: TokenKind,

    char_span: SpanLoc,
    byte_span: SpanStr<'a>,

    /// Extra informations.
    data: Option<TokenData>,
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({:?}, {}, {:?})", self.kind, self.char_span, self.data)
    }
}

#[derive(Default, Debug)]
pub struct TokenBuilder<'a> {
    kind: TokenKind,
    char_span: Span<Loc>,
    byte_span: SpanStr<'a>,
    data: Option<TokenData>,
}

impl<'a> TokenBuilder<'a> {
    pub fn reset(&mut self, string: &'a str, kind: TokenKind, start_loc: Loc, start_byte: usize) {
        self.kind = kind;
        self.char_span = SpanLoc::new(start_loc, start_loc);
        self.byte_span = SpanStr::new(string, start_byte, start_byte);
    }

    pub fn get_data_mut(&mut self) -> Result<&mut TokenData> {
        match self.data.as_mut() {
            Some(d) => Ok(d),
            None => Err(Error::InvalidData),
        }
    }

    pub fn new_data(&mut self, data: Option<TokenData>) {
        self.data = data;
    }

    /// Sets [`TokenBuilder::data`] to [`None`].
    pub fn build(&mut self, hi_loc: Loc, hi_byte: usize) -> Token<'a> {
        let mut char_span = self.char_span;
        char_span.hi = hi_loc;

        let mut byte_span = self.byte_span;
        byte_span.span.hi = hi_byte;

        Token {
            kind: self.kind,
            char_span,
            byte_span,
            data: self.data.take(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TokenData {
    Integer(usize),
}

impl TokenData {
    pub fn integer(&mut self) -> Result<&mut usize> {
        #[allow(irrefutable_let_patterns)]
        if let Self::Integer(v) = self {
            Ok(v)
        } else {
            Err(Error::InvalidData)
        }
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

    cur_token: TokenBuilder<'a>,
    cur_char: Option<char>,

    tokens: Vec<Token<'a>>,

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
            cur_token: TokenBuilder::default(),
            cur_char: None,
            tokens: vec![],
            inside_quotes: false,
        };
        ret.cur_char = ret.iter.next();

        ret
    }

    fn search(&mut self, token_kind: TokenKind) {
        self.cur_token
            .reset(self.str, token_kind, self.cur_loc, self.cur_byte);
        self.next_state = State::Search;
    }

    fn finalise(&mut self) {
        self.next_state = State::Finalise
    }

    fn finalise_token(&mut self) -> Result<Token<'a>> {
        // NOTE: Only `TokenKind::Eof` is zero-sized
        if self.cur_token.kind != TokenKind::Eof
            && self.cur_loc.col <= self.cur_token.char_span.lo.col
        {
            return Err(Error::EmptyToken);
        }

        Ok(self.cur_token.build(self.cur_loc, self.cur_byte))
    }

    fn push(&mut self) -> Result<()> {
        let token = self.finalise_token()?;
        self.tokens.push(token);
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
                    self.cur_token.new_data(Some(TokenData::Integer(0)));
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
                        let i = self.cur_token.get_data_mut()?.integer()?;
                        *i += 1;
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
            | TokenKind::Unknown
            | TokenKind::Colon
            | TokenKind::Equals
            | TokenKind::LBracket
            | TokenKind::RBracket
            | TokenKind::LParen
            | TokenKind::RParen
            | TokenKind::DollarSign
            | TokenKind::Question
            | TokenKind::Period
            | TokenKind::Comment
            | TokenKind::Indent(_) => self.push()?,
            TokenKind::Eof => {
                self.push()?;
                return Ok(true);
            }
            TokenKind::Newline => {
                self.push()?;
                self.cur_loc.line += 1;
                self.cur_loc.col = 1;
            }
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
