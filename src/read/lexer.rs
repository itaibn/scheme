/// A Scheme lexer following the description in Section 7.1 of R7RS. Currently
/// incomplete and doesn't support Unicode.

use regex::{Captures, Match, Regex};

lazy_static! {
    static ref IDENTIFIER: Regex = Regex::new(
        //"^[[:alpha:]!$%&*/:<=>?@^_~][[:alnum:]!$%&*/:<=>?@^_~]*"
        "^[[:alpha:]!$%&*/:<=>?^_~][[:alnum:]!$%&*/:<=>?^_~+-.@]*"
    ).unwrap();
//    static ref STRING: Regex = Regex::new(
//        "^(:?[^\"\\\\]|\\\\(:?[\"\\\\|abtnr]))*\""
}

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    LeftParen,
    LeftVector,
    LeftBytevector,
    RightParen,
    Dot,
    DatumComment,
    FoldCase(bool),
    PrefixOp(&'static str),
    Identifier(String),
    Boolean(bool),
    Number(i64),
    Character(char),
    String(Vec<char>),
}

#[derive(Debug)]
pub struct Lexer<'a>(&'a str);

//#[derive(Debug)]
//pub struct LexerError;
type LexerError = &'static str;

/// Check whether a character is a delimiter. Unicode whitespace is not support.
fn is_delimiter(c: char) -> bool {
    is_scheme_whitespace(c) | "|()\";".contains(c)
}

/// Check whether a character is whitespace according to the definition in
/// Section 7.1 of R7RS. Unicode is not supported.
fn is_scheme_whitespace(c: char) -> bool {
    " \t\n\r".contains(c)
}

/// Match <initial> pattern. Unicode not supported.
fn is_scheme_identifier_initial(c: char) -> bool {
    c.is_ascii_alphabetic() | "!$%&*/:<=>?^_~".contains(c)
}

/// Match <subsequence> pattern. Unicode not supported.
fn is_scheme_identifier_subsequent(c: char) -> bool {
    is_scheme_identifier_subsequent(c) | c.is_digit(10) | "+-.@".contains(c)
}

impl Token {
    fn from_i64(x: i64) -> Token {
        Token::Number(x)
    }

    fn from_str(s: &str) -> Token {
        Token::String(s.chars().collect())
    }
}

// TODO: Comprehensive todo list, line comments, nested comments, data comments,
// vectors, bytevectors, all number parsing, booleans, case-folding directives,
// abbreviations for (unquote, quasiquote, unquote-splicing), characters,
// strings, pipe notation for identifiers, verifying agreement with lexer
// specifications in Section 7.1.1
impl Lexer<'_> {
    #[deprecated]
    pub fn new(input_str: &str) -> Lexer {
        Lexer::from_str(input_str)
    }

    fn from_str(input_str: &str) -> Lexer {
        Lexer(input_str)
    }

    // Suggestion: Turn all forms of newline into "\n"
    fn get_char(&mut self) -> Option<char> {
        let mut chars = self.0.chars();
        let next_char = chars.next();
        self.0 = chars.as_str();
        next_char
    }

    fn get_match<'t>(&'t mut self, r: &Regex) -> Option<Match<'t>> {
        // I don't think the borrow checker will accept this
        r.find(self.0).map(|matching| {
            self.0 = &self.0[matching.end()..];
            matching
        })
    }

    fn get_captures<'t>(&'t mut self, r: &Regex) -> Option<Captures<'t>> {
        // Copy-pasted from get_match without thought
        // I don't think the borrow checker will accept this
        r.captures(self.0).map(|capture| {
            self.0 = &self.0[capture[0].len()..];
            capture
        })
    }

    /// If the buffer starts with a prefix that matches the string `s`
    /// case-insensitively, consume that prefix and return `true`. Otherwise
    /// return `false`. Only case-insensitive for ASCII characters.
    fn get_str_ci(&mut self, s: &str) -> bool {
        let mut buff_iter = self.0.chars();
        for c in s.chars() {
            if buff_iter.next().map(|c| c.to_ascii_lowercase()) !=
                Some(c.to_ascii_lowercase()) {
                return false;
            }
        }
        self.0 =  buff_iter.as_str();
        true
    }

    fn peek_char(&self, n: usize) -> Option<char> {
        self.0.chars().nth(n)
    }

    fn is_delimited(&self) -> bool {
        self.peek_char(0).map(is_delimiter).unwrap_or(true)
    }

    fn get_token(&mut self) -> Option<Token> {
        self.consume_atmosphere();
        if let Some(ident) = self.get_ident() {
            if self.is_delimited() {
                return Some(ident)
            }
        }
        let (consume, needs_delimitor, out) = match self.peek_char(0) {
            Some('(') => (true, false, Some(Token::LeftParen)),
            Some(')') => (true, false, Some(Token::RightParen)),
            Some('\'') => (true, false, Some(Token::PrefixOp("quote"))),
            Some('`') => (true, false, Some(Token::PrefixOp("quasiquote"))),
            Some(',') => {
                if self.peek_char(1) == Some('@') {
                    self.get_char(); self.get_char();
                    (false, false, Some(Token::PrefixOp("unquote-splicing")))
                } else {
                    self.get_char();
                    (false, false, Some(Token::PrefixOp("unquote")))
                }
            }
            Some('.') => (true, true, Some(Token::Dot)),
            Some('"') => (false, false, self.get_string_literal()),
            Some('-') | Some('+') => (false, true, self.get_number()),
            Some('#') => match self.peek_char(1).map(|c| c.to_ascii_lowercase())
            {
                Some(';') => {
                    self.get_char(); self.get_char();
                    (false, false, Some(Token::DatumComment))
                },
                Some('(') => {
                    self.get_char(); self.get_char();
                    (false, false, Some(Token::LeftVector))
                },
                Some('u') => {
                    // Improvement: Use a match-string pattern:
                    //if (self.peek_char(2),
                    //    self.peek_char(1).map(|c| c.to_ascii_lowercase()))
                    if (self.peek_char(2), self.peek_char(3))
                        == (Some('8'), Some('(')) {

                        self.get_char(); self.get_char();
                        self.get_char(); self.get_char();
                        (false, false, Some(Token::LeftBytevector))
                    } else {
                        return None;
                    }
                },
                Some('e') | Some('i') | Some('b') | Some('o') | Some('d') |
                Some('x') => (false, true, self.get_number()),
                Some('|') => panic!("Recursive comment incorrectly detected"),
                // Booleans; no full-name boolean support,
                Some('t') => {
                    if self.get_str_ci("#true") | self.get_str_ci("#t") {
                        (false, true, Some(Token::Boolean(true)))
                    } else {
                        (false, false, None)
                    }
                },
                Some('f') => {
                    //self.get_char(); self.get_char();
                    //(false, true, Some(Token::Boolean(false)))
                    if self.get_str_ci("#false") | self.get_str_ci("#f") {
                        (false, true, Some(Token::Boolean(false)))
                    } else {
                        (false, false, None)
                    }
                },
                Some('!') => {
                    if self.get_str_ci("#!fold-case") {
                        (false, true, Some(Token::FoldCase(true)))
                    } else if self.get_str_ci("#!no-fold-case") {
                        (false, true, Some(Token::FoldCase(false)))
                    } else {
                        (false, false, None)
                    }
                },
                Some('\\') => {
                    self.get_char(); self.get_char();
                    let c = self.get_char()?;
                    (false, true, Some(Token::Character(c)))
                },
                _ => (false, false, None),
            }
            Some(d) if d.is_digit(10) => (false, true, self.get_number()),
            //Some(c) if 
            _ => (false, false, None),
        };
        if consume {self.get_char();}
        if self.is_delimited() | !needs_delimitor {
            out
        } else {
            None
        }
    }

    /// Consumes whitespace and comments. This is like the <atmosphere> category
    /// in the standard, except it doesn't support datum comments.
    fn consume_atmosphere(&mut self) {
        loop {
            match self.peek_char(0) {
                Some(w) if is_scheme_whitespace(w) => {self.get_char();},
                // Line comment
                Some(';') => {
                    loop {
                        match self.get_char() {
                            Some('\n') | Some('\r') | None => break,
                            _ => {},
                        }
                    }
                },
                Some('#') => {
                    if self.peek_char(1) == Some('|') {
                        self.get_char(); self.get_char();
                        let mut depth = 1;
                        while depth > 0 {
                            match self.get_char() {
                                Some('#') => if self.peek_char(0) == Some('|') {
                                    self.get_char();
                                    depth += 1;
                                },
                                Some('|') => if self.peek_char(0) == Some('#') {
                                    self.get_char();
                                    depth -= 1;
                                },
                                None => unimplemented!(),
                                _ => {},
                            }
                        }
                    } else {
                        break;
                    }
                },
                _ => break,
            }
        }
    }

    fn get_ident(&mut self) -> Option<Token> {
        self.get_match(&*IDENTIFIER).map(|matching| {
            // In later versions some processing will be necessary to permit
            // peculiar identifiers
            Token::Identifier(matching.as_str().to_string())
        })
    }

    fn get_number(&mut self) -> Option<Token> {
        let mut cur: i64 = 0;
        let mut fst_digit = false;
        let mut negative = None;
        loop {
            if self.is_delimited() {
                if fst_digit {
                    break;
                } else {
                    return None;
                }
            }
            match self.get_char() {
                Some(d) if d.is_digit(10) => {
                    fst_digit = true;
                    cur = 10*cur + (d.to_digit(10).unwrap() as i64)
                },
                Some('+') => {
                    if fst_digit | negative.is_some() {
                        return None;
                    }
                    negative = Some(false);
                },
                Some('-') => {
                    if fst_digit | negative.is_some() {
                        return None;
                    }
                    negative = Some(true);
                },
                _ => {return None;}
            }
        }
        if negative == Some(true) {
            cur = -cur;
        }
        Some(Token::from_i64(cur))
    }

    fn get_string_literal(&mut self) -> Option<Token> {
        assert!(self.get_char() == Some('"'), "This method only works when the \
            first char is '\"'");
        let mut string = Vec::new();
        while let Some(c) = self.get_char() {
            if c == '"' {
                break;
            }
            if c == '\\' {
                // TODO: Make case-insensitive
                match self.get_char() {
                    Some('a') => string.push('\u{7}'),
                    Some('b') => string.push('\u{8}'),
                    Some('t') => string.push('\u{9}'),
                    Some('n') => string.push('\u{a}'),
                    Some('r') => string.push('\u{d}'),
                    Some('"') => string.push('"'),
                    Some('\\') => string.push('\\'),
                    Some('|') => string.push('|'),
                    Some('x') => {
                        lazy_static! {
                            static ref HEX_ESCAPE: Regex =
                                Regex::new("^([0-9a-fA-F]+);").unwrap();
                        }
                        // Awkard style; should use "?" and Results?
                        match self.get_captures(&*HEX_ESCAPE)
                                .and_then(|c|
                            u32::from_str_radix(&c[1], 16).ok()
                                ).and_then(|n|
                            std::char::from_u32(n)) {

                            Some(res_char) => string.push(res_char),
                            None => return None,
                        }
                    },
                    Some(mut w) => {
                        // This is a mess. Should I use regular expressions?
                        // Unicode?
                        let mut prev_nl = false;
                        loop {
                            if w == '\n' {
                                prev_nl = true;
                            } else if w == '\r' {
                                if self.peek_char(0) == Some('\n') {
                                    self.get_char();
                                }
                                prev_nl = true;
                            }
                            w = self.peek_char(0)?;
                            if !is_scheme_whitespace(w) {
                                if prev_nl {
                                    break;
                                } else {
                                    return None;
                                }
                            }
                            if prev_nl && (w == '\n' || w == '\r') {
                                return None;
                            }
                            self.get_char();
                        }
                    },
                    None => {return None;},
                }
            } else {
                string.push(c);
            }
        }
        Some(Token::String(string))
    }

    /*
    fn read_line_comment(&mut self) {
        while Some(c) = self.get_char() {
            match c {
                '\r' => {
                    if let Some('\n') = self.peek_char() {
                        self.get_char();
                    }
                '\n' => {
    }
    */
}

impl Iterator for Lexer<'_> {
    type Item = Result<Token, LexerError>;

    // TODO: Distinguist EOF and error
    fn next(&mut self) -> Option<Self::Item> {
        self.get_token().map(Ok)
    }
}

/*
fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || "!$%&*:/<=>?@^_~".contains(c)
}

fn is_ident_subsequent(c: char) -> bool {
    is_ident_start(c) || 
}
*/

#[cfg(test)]
fn test_lexer(inp: &str, out: Token) {
    assert_eq!(Lexer::from_str(inp).get_token(), Some(out));
}

#[test]
fn test_ident() {
    let ident_strs = &["a", "z", "A", "Z", "let*", "!as0", "+", "-", "+@", "+$",
        "+a", "+.+", "..."];
    for ident_str in ident_strs {
        test_lexer(ident_str, Token::Identifier(ident_str.to_string()));
    }
}

#[test]
fn test_pipe_ident() {
    test_lexer("|  0-!@\"5\\\\*\\|\\x100;\\a|",
        Token::Identifier("  0-!@\"5\\*|\u{100}\u{7}".to_string()));
}

#[test]
fn test_simple_tokens() {
    test_lexer("(", Token::LeftParen);
    test_lexer(")", Token::RightParen);
    test_lexer("#(", Token::LeftVector);
    test_lexer("#u8(", Token::LeftBytevector);
    test_lexer("#t", Token::Boolean(true));
    test_lexer("#true", Token::Boolean(true));
    test_lexer("#tRUe", Token::Boolean(true));
    test_lexer("#f", Token::Boolean(false));
    test_lexer("#F", Token::Boolean(false));
    test_lexer("#false", Token::Boolean(false));
    test_lexer("'", Token::PrefixOp("quote"));
    test_lexer("`", Token::PrefixOp("quasiquote"));
    test_lexer(",", Token::PrefixOp("unquote"));
    test_lexer(",@", Token::PrefixOp("unquote-splicing"));
    test_lexer(".", Token::Dot);
    test_lexer("#;", Token::DatumComment);
    test_lexer("#!fold-case", Token::FoldCase(true));
    test_lexer("#!no-fold-case", Token::FoldCase(false));
    test_lexer("#!NO-fOLD-cAse", Token::FoldCase(false));
}

#[test]
fn test_whitespace() {
    test_lexer(" \t\n1", Token::from_i64(1));
    test_lexer("\r\n1", Token::from_i64(1));
    test_lexer("\r1", Token::from_i64(1));
}

#[test]
fn test_comment() {
    test_lexer("; blah ; 10!)#!fold-case \n  1", Token::from_i64(1));
    test_lexer("; 123\r123", Token::from_i64(123));
    test_lexer("#| simple intra-line comment |# 1", Token::from_i64(1));
    test_lexer("#| | # #| a |# 22 |# 1", Token::from_i64(1));
    test_lexer("#| #| |#| |# 1 ;|# 2", Token::from_i64(1));
    test_lexer("#|# 1 |# 2", Token::from_i64(2));
}

#[test]
fn test_character() {
    test_lexer(r"#\ ", Token::Character(' '));
    test_lexer(r"#\a", Token::Character('a'));
    test_lexer(r"#\⅋", Token::Character('⅋'));
    // Unsure of this one
    test_lexer(r"#\x", Token::Character('x'));
}

#[test]
fn test_character_escape() {
    test_lexer(r"#\x0", Token::Character('\u{0}'));
    test_lexer(r"#\x61", Token::Character('a'));
    test_lexer(r"#\X61", Token::Character('a'));
    test_lexer(r"#\x062", Token::Character('b'));
    test_lexer(r"#\x214b", Token::Character('⅋'));
    test_lexer(r"#\X1d538", Token::Character('𝔸'));
    test_lexer(r"#\x100000", Token::Character('\u{100000}'));
    test_lexer(r"#\x000000061", Token::Character('a'));
}

#[test]
fn test_character_name() {
    test_lexer(r"#\alarm", Token::Character('\u{7}'));
    test_lexer(r"#\backspace", Token::Character('\u{8}'));
    test_lexer(r"#\delete", Token::Character('\u{7f}'));
    test_lexer(r"#\escape", Token::Character('\u{1b}'));
    test_lexer(r"#\newline", Token::Character('\n'));
    test_lexer(r"#\null", Token::Character('\u{0}'));
    test_lexer(r"#\return", Token::Character('\r'));
    test_lexer(r"#\space", Token::Character(' '));
    test_lexer(r"#\tab", Token::Character('\t'));
}

#[test]
fn test_string() {
    test_lexer("\"\"", Token::from_str(""));
    test_lexer("\"Hello, world!\"", Token::from_str("Hello, world!"));
}

#[test]
fn test_simple_int() {
    test_lexer("13", Token::from_i64(13));
    test_lexer("-4", Token::from_i64(-4));
}

#[test]
fn test_radix_int() {
    test_lexer("123", Token::from_i64(123));
    test_lexer("#d123", Token::from_i64(123));
    test_lexer("#x123", Token::from_i64(0x123));
    test_lexer("#o123", Token::from_i64(0o123));
    test_lexer("#b101", Token::from_i64(0b101));
}

#[test]
fn test_prefixes() {
    test_lexer("#e123", Token::from_i64(123));
    //test_lexer("#i123", ...);
    test_lexer("#e#x10", Token::from_i64(16));
    test_lexer("#x#e10", Token::from_i64(16));
    //test_lexer("#i#x10", ...);
    //test_lexer("#x#i10", ...);
}

#[test]
fn test_fraction() {
    //test_lexer("1/2", ...);
    //test_lexer("#x1/10", ...);
    //test_lexer("#i1/2", ...);
}

#[test]
fn test_float() {
    //test_lexer("1.234e2", ...);
    test_lexer("#e1e2", Token::from_i64(100));
    test_lexer("#e1e0", Token::from_i64(1));
    test_lexer("#e10e-1", Token::from_i64(1));
    //test_lexer(".10", ...);
    //test_lexer("13e-10", ...);
}

#[test]
fn test_infnan() {
    //test_lexer("+inf.0", ...);
    //test_lexer("-inf.0", ...);
    //test_lexer("+nan.0", ...);
    //test_lexer("-nan.0", ...);
}

#[test]
fn test_complex() {
    //test_lexer("1@-2.0", ...);
    //test_lexer("-2+3i", ...);
    //test_lexer("1-1e0i", ...);
    //test_lexer("#x10+i", ...);
    //test_lexer("1/2-i", ...);
    //test_lexer("+i", ...);
    //test_lexer("-i", ...);
    //test_lexer("+1.0i", ...);
    //test_lexer("#o-11/10i", ...);
    //test_lexer("+inf.0i", ...);
    //test_lexer("-inf.0i", ...);
    //test_lexer("+nan.0i", ...);
    //test_lexer("-nan.0i", ...);
}
