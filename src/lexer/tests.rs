// TODO: Test non-ASCII characters
use super::*;

mod assert {
    use super::*;

    pub struct Value<'a> {
        /// [`None`] for filler, does not actually assert. Only for filling in skipped characters.
        kind: Option<TokenKind>,
        data: Option<TokenData>,
        len_char: usize,
        len_byte: usize,
        string: Option<&'a str>,
    }

    impl<'a> Value<'a> {
        pub fn new(
            kind: TokenKind,
            len_char: usize,
            len_byte: usize,
            data: Option<TokenData>,
        ) -> Self {
            Self {
                kind: Some(kind),
                data,
                len_char,
                len_byte,
                string: None,
            }
        }

        pub fn with_str(kind: TokenKind, string: &'a str, data: Option<TokenData>) -> Self {
            Self {
                kind: Some(kind),
                data,
                len_char: string.chars().count(),
                len_byte: string.len(),
                string: Some(string),
            }
        }

        pub fn filler(len_char: usize, len_byte: usize) -> Self {
            Self {
                kind: None,
                data: None,
                len_char,
                len_byte,
                string: None,
            }
        }
    }

    pub mod values {
        use super::*;

        pub fn filler(len_char: usize, len_byte: usize) -> Value<'static> {
            Value::filler(len_char, len_byte)
        }

        pub fn numeric(n: &str) -> Value {
            Value::with_str(TokenKind::Numeric, n, None)
        }

        #[derive(Copy, Clone)]
        pub enum NewlineKind {
            Unix = 1,
            Dos = 2,
        }

        impl NewlineKind {
            pub fn into_str(self) -> &'static str {
                match self {
                    Self::Unix => "\n",
                    Self::Dos => "\r\n",
                }
            }
        }

        pub const NEWLINES: [NewlineKind; 2] = [NewlineKind::Unix, NewlineKind::Dos];

        impl From<NewlineKind> for &str {
            fn from(value: NewlineKind) -> Self {
                value.into_str()
            }
        }

        pub fn newline(kind: NewlineKind) -> Value<'static> {
            Value::with_str(TokenKind::Newline, kind.into(), None)
        }

        pub fn unewline() -> Value<'static> {
            newline(NewlineKind::Unix)
        }

        pub fn indent(kind: IndentKind, n: usize) -> Value<'static> {
            Value::new(
                TokenKind::Indent(kind),
                n,
                // Should be ASCII
                n,
                Some(TokenData::Integer(n)),
            )
        }

        pub fn unknown(s: &str) -> Value {
            Value::with_str(TokenKind::Unknown, s, None)
        }

        /// # Panics
        /// Panics if the character is invalid. See [`TokenKind::char`].
        pub fn single_char(c: char) -> Value<'static> {
            if !c.is_ascii() {
                panic!("Non ASCII character. Not yet needed");
            }

            if let Some(k) = TokenKind::char(c) {
                // Should be ASCII
                Value::new(k, 1, 1, None)
            } else {
                panic!("Invalid character");
            }
        }

        /// Automatically surround with quotes
        pub fn quoted_ident(s: &str) -> Value<'static> {
            // MAYBE: Use this <https://doc.rust-lang.org/beta/std/primitive.str.html#method.escape_debug>?
            // But I'm not sure what it escapes.
            let quoted = format!("\"{s}\"").leak();
            Value::with_str(TokenKind::QuotedIdent, quoted, None)
        }

        pub fn ident(s: &str) -> Value {
            Value::with_str(TokenKind::Identifier, s, None)
        }

        /// Include the hash sign.
        pub fn comment(s: &str) -> Value {
            Value::with_str(TokenKind::Comment, s, None)
        }
    }

    macro_rules! error {
            ($token:expr, $($msg:tt)*) => {
                panic!("{}: {}", $token.char_span.lo, format!($($msg)*));
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

    pub fn assert(
        token: &Token,
        kind: &TokenKind,
        char_span: &SpanLoc,
        byte_span: &SpanStr,
        data: &Option<TokenData>,
        string: &Option<&str>,
    ) {
        // NOTE: Keep track of fields
        let _ = Token {
            kind: TokenKind::default(),
            char_span: SpanLoc::default(),
            byte_span: SpanStr::default(),
            data: None,
        };

        eq!(
            token,
            *kind,
            token.kind,
            "Expected token kind to be {_l:?}, is actually {_r:?}",
        );
        eq!(
            token,
            *char_span,
            token.char_span,
            "Expected token to span (characters) {_l}, actually {_r}",
        );
        eq!(
            token,
            *byte_span,
            token.byte_span,
            "Expected token to span (bytes) {_l}, actually {_r}",
        );
        eq!(
            token,
            *data,
            token.data,
            "Expected token data to be {_l:?}, is actually {_r:?}",
        );
        if let Some(s) = string {
            eq!(
                token,
                *s,
                token.byte_span.to_string().unwrap(),
                "Expected token data to be {_l:?}, is actually {_r:?}",
            );
        }
    }

    pub fn assert_tokens(string: &str, tokens: &[Token], values: &[Value]) {
        assert_eq!(
                tokens.len() - 1,
                values.iter().filter(|x| x.kind.is_some()).count(),
                "Expected non-filter `values` with the length of `tokens` length minus 1\nActual tokens: {:#?}", tokens
            );

        let mut cur_loc = Loc::new(1, 1);
        let mut cur_byte = 0;
        let mut i = 0;
        for value in values {
            let token = &tokens[i];

            if let Some(ref k) = value.kind {
                // TODO: Under assumption that no tokens span multiple lines for now.
                // Obviously when we have added multiline comments this will break.
                let mut hi_loc = cur_loc;
                hi_loc.col += value.len_char;

                let mut hi_byte = cur_byte;
                hi_byte += value.len_byte;

                let char_span = SpanLoc::new(cur_loc, hi_loc);
                let byte_span = SpanStr::new(string, cur_byte, hi_byte);

                assert(token, k, &char_span, &byte_span, &value.data, &value.string);

                i += 1;
            }

            cur_loc = Loc::new(cur_loc.line, cur_loc.col + value.len_char);
            cur_byte += value.len_byte;

            if token.kind == TokenKind::Newline {
                cur_loc.line += 1;
                cur_loc.col = 1;
            }
        }
        assert_eof(string, tokens.last().unwrap(), &cur_loc, &cur_byte);
    }

    pub fn assert_eof(string: &str, token: &Token, start_loc: &Loc, start_byte: &usize) {
        let char_span = SpanLoc::new(*start_loc, *start_loc);
        let byte_span = SpanStr::new(string, *start_byte, *start_byte);
        assert(token, &TokenKind::Eof, &char_span, &byte_span, &None, &None);
    }
}

use assert::{assert_tokens, values::*, Value};

#[test]
fn empty() {
    let s = "";
    let tokens = Lexer::tokenise(s).unwrap();
    assert_tokens(s, &tokens, &[]);
}

#[test]
fn integer_number() {
    for i in 1..=10 {
        let s = (0..i)
            .map(|x| char::from_digit(x as u32, 10).unwrap())
            .collect::<String>();

        let tokens = Lexer::tokenise(&s).unwrap();
        assert_tokens(&s, &tokens, &[numeric(&s)]);
    }
}

#[test]
fn unknown_token() {
    for i in 1..=10 {
        let s = (0..i).map(|_| '\r').collect::<String>();
        let v = (0..i).map(|_| unknown("\r")).collect::<Vec<Value>>();
        let tokens = Lexer::tokenise(&s).unwrap();
        assert_tokens(&s, &tokens, &v);
    }
}

#[test]
fn lone_newline() {
    for n in NEWLINES {
        let s = n.into_str();
        let tokens = Lexer::tokenise(s).unwrap();
        assert_tokens(&s, &tokens, &[newline(n)]);
    }
}

#[test]
fn newline_and_number() {
    for n in NEWLINES {
        let s = format!("1024{}", n.into_str());
        let tokens = Lexer::tokenise(&s).unwrap();
        assert_tokens(&s, &tokens, &[numeric("1024"), newline(n)]);
    }

    for n in NEWLINES {
        let s = format!("{}1024", n.into_str());
        let tokens = Lexer::tokenise(&s).unwrap();
        assert_tokens(&s, &tokens, &[newline(n), numeric("1024")]);
    }
}

#[test]
fn token_string() {
    let s = "1024\n2048\n";
    let tokens = Lexer::tokenise(s).unwrap();
    assert_tokens(
        &s,
        &tokens,
        &[numeric("1024"), unewline(), numeric("2048"), unewline()],
    );
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

    let tokens = Lexer::tokenise(s).unwrap();

    assert_tokens(
        &s,
        &tokens,
        &[
            unewline(),
            numeric("0"),
            unewline(),
            unewline(),
            indent(IndentKind::Space, 2),
            numeric("1"),
            filler(1, 1),
            numeric("2"),
            unewline(),
            indent(IndentKind::Space, 4),
            numeric("3"),
            filler(3, 3),
            numeric("4"),
            unewline(),
            indent(IndentKind::Space, 6),
            numeric("5"),
            filler(1, 1),
            numeric("6"),
            unewline(),
            indent(IndentKind::Space, 8),
            numeric("7"),
            filler(3, 3),
            numeric("8"),
            unewline(),
            unewline(),
            indent(IndentKind::Tab, 1),
            numeric("1"),
            filler(1, 1),
            numeric("2"),
            unewline(),
            indent(IndentKind::Tab, 2),
            numeric("3"),
            filler(1, 1),
            numeric("4"),
            unewline(),
            unewline(),
            indent(IndentKind::Space, 4),
            filler(1, 1),
            numeric("1"),
            unewline(),
            indent(IndentKind::Tab, 1),
            filler(4, 4),
            numeric("2"),
            unewline(),
        ],
    );
}

#[test]
fn single_chars() {
    // NOTE: Keep track of kinds
    match TokenKind::default() {
            TokenKind::Unknown
            | TokenKind::Eof
            | TokenKind::Indent(_)
            | TokenKind::Newline
            | TokenKind::Numeric
            | TokenKind::Identifier
            | TokenKind::QuotedIdent
            | TokenKind::Comment

            // Single-character
            | TokenKind::Colon
            | TokenKind::Equals
            | TokenKind::LBracket
            | TokenKind::RBracket
            | TokenKind::LParen
            | TokenKind::RParen
            | TokenKind::DollarSign
            | TokenKind::Question
            | TokenKind::Period => (),
        }

    let s = ":=[]()$?.";
    let tokens = Lexer::tokenise(s).unwrap();
    assert_tokens(
        &s,
        &tokens,
        &s.chars().map(single_char).collect::<Vec<Value>>(),
    );
}

#[test]
fn quoted_identifier() {
    let s = r#""foo""bar"
"baz"
"foo\tbar\nbaz""#;
    let tokens = Lexer::tokenise(s).unwrap();
    assert_tokens(
        &s,
        &tokens,
        &[
            quoted_ident("foo"),
            quoted_ident("bar"),
            unewline(),
            quoted_ident("baz"),
            unewline(),
            quoted_ident("foo\\tbar\\nbaz"),
        ],
    );
}

#[test]
fn identifier() {
    let s = "foo\tbar\nbaz\rquux? 1337 \"420\"\n";
    let tokens = Lexer::tokenise(s).unwrap();
    assert_tokens(
        &s,
        &tokens,
        &[
            ident("foo"),
            filler(1, 1),
            ident("bar"),
            unewline(),
            ident("baz"),
            unknown("\r"),
            ident("quux"),
            single_char('?'),
            filler(1, 1),
            numeric("1337"),
            filler(1, 1),
            quoted_ident("420"),
            unewline(),
        ],
    );
}

#[test]
fn comments() {
    let s = r#"
# Hello, World!
comment # Mid-line
"#;

    for n in NEWLINES {
        let actual_s = s.replace("\n", n.into());
        let tokens = Lexer::tokenise(&actual_s).unwrap();
        assert_tokens(
            &actual_s,
            &tokens,
            &[
                newline(n),
                comment("# Hello, World!"),
                newline(n),
                ident("comment"),
                filler(1, 1),
                comment("# Mid-line"),
                newline(n),
            ],
        );
    }
}
