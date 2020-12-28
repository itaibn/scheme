/// A Scheme lexer following the description in Section 7.1 of R7RS. Currently
/// incomplete and doesn't support Unicode.

use std::str::FromStr;

use lazy_static::lazy_static;
use num::{self, BigRational, FromPrimitive, ToPrimitive};
use regex::{Captures, Match, Regex};

use crate::scheme::Scheme;

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
    Number(Number),
    Character(char),
    String(Vec<char>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Exactness  {
    Exact,
    Inexact,
}

/*
pub struct Float {
    num: Int,
    base: u8,
    exp: Int,
}

pub enum Real {
    Rational(Rational),
    Floa
}
*/

//pub struct Complex
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Number {
    exactness: Exactness,
    value: BigRational,
}

#[derive(Debug)]
pub struct Lexer<'a>(&'a str);

//#[derive(Debug)]
//pub struct LexerError;
type LexerError = &'static str;

/// Check whether a character is a delimiter. Unicode whitespace is not support.
fn is_delimiter(c: char) -> bool {
    is_scheme_whitespace(c) || "|()\";".contains(c)
}

/// Check whether a character is whitespace according to the definition in
/// Section 7.1 of R7RS. Unicode is not supported.
fn is_scheme_whitespace(c: char) -> bool {
    " \t\n\r".contains(c)
}

/// Match <initial> pattern. Unicode not supported.
fn is_scheme_identifier_initial(c: char) -> bool {
    c.is_ascii_alphabetic() || "!$%&*/:<=>?^_~".contains(c)
}

/// Match <subsequence> pattern. Unicode not supported.
fn is_scheme_identifier_subsequent(c: char) -> bool {
    is_scheme_identifier_initial(c) || c.is_digit(10) || "+-.@".contains(c)
}

impl Number {
    /// If self is an exact u8 return it, otherwise return Nothing.
    pub fn as_u8(&self) -> Option<u8> {
        // assumes all ints have den = 1.
        if self.exactness == Exactness::Inexact || !self.value.is_integer() {
            None
        } else {
            self.value.to_integer().to_u8()
        }
    }

    /// Convert a number into a Scheme value. Implementation is currently
    /// incomplete.
    pub fn to_scheme(&self) -> Scheme {
        if self.value.is_integer() {
            Scheme::int(self.value.to_integer().to_i64().unwrap())
        } else {
            unimplemented!()
        }
    }

    /// Rational i64 with exactness. Used in testing/
    fn rational_i64(num: i64, den: i64, exact: Exactness) -> Number {
        let rat = BigRational::from_i64(num).unwrap() /
            BigRational::from_i64(den).unwrap();
        Number {exactness: exact, value: rat}
    }
}

impl Token {
    fn from_i64(x: i64) -> Token {
        let rat = BigRational::from_i64(x).unwrap();
        let num = Number {exactness: Exactness::Exact, value: rat};
        Token::Number(num)
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
impl<'lexer> Lexer<'lexer> {
    pub fn from_str(input_str: &str) -> Lexer<'_> {
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

    /// Either consume and output a single token from the input stream, or
    /// output None while consuming an unspecified numbere of characters from
    /// the input stream.
    pub fn get_token(&mut self) -> Option<Token> {
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
            Some('.') => { // TODO: Make this link to get_number?
                if self.peek_char(1).map(|c| is_delimiter(c)).unwrap_or(true) {
                    (true, true, Some(Token::Dot))
                } else {
                    (false, true, self.get_number())
                }
            },
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
                Some('t') => {
                    if self.get_str_ci("#true") {
                        (false, true, Some(Token::Boolean(true)))
                    } else if self.get_str_ci("#t") {
                        (false, true, Some(Token::Boolean(true)))
                    } else {
                        (false, false, None)
                    }
                },
                Some('f') => {
                    //self.get_char(); self.get_char();
                    //(false, true, Some(Token::Boolean(false)))
                    if self.get_str_ci("#false") {
                        (false, true, Some(Token::Boolean(false)))
                    } else if self.get_str_ci("#f") {
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
        if self.is_delimited() || !needs_delimitor {
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

    /// Parses numbers, consuming an unspecified number of characters if the
    /// stream does not contain a valid number. Currently implements base and
    /// exactness prefixes, ints and finite floats (no infinite floats, NaN,
    /// rationals, or complex numbers). This implementation is a messy hack and
    /// probably has bugs.
    fn get_number_old(&mut self) -> Option<Token> {
        let mut possible_ident = true;
        let mut exactness = None;
        let mut base = 10;
        let mut base_specified = false;

        let mut cur: i64 = 0;
        let mut exponent: i64 = 0;
        let mut float_mantissa = None;
        let mut has_dot = false;
        let mut has_digit = false; // has first digit appeared yet?
        let mut negative = None;

        // Parse prefixes
        while self.peek_char(0) == Some('#') {
            self.get_char();
            let c = self.get_char()?.to_ascii_lowercase();
            match c {
                'e' => {
                    if exactness.is_none() {
                        exactness = Some(Exactness::Exact);
                    } else {
                        return None;
                    }
                },
                'i' => {
                    if exactness.is_none() {
                        exactness = Some(Exactness::Inexact);
                    } else {
                        return None;
                    }
                },
                'b' | 'o' | 'd' | 'x' => {
                    if base_specified {
                        return None;
                    }
                    base_specified = true;
                    base = match c {
                        'b' => 2,
                        'o' => 8,
                        'd' => 10,
                        'x' => 16,
                        _ => unreachable!(),
                    }
                },
                _ => {
                    return None;
                }
            }
            possible_ident = false;
        }

        while !self.is_delimited() {
            match self.get_char() {
                Some(d) if d.is_digit(base) => {
                    has_digit = true;
                    if has_dot && float_mantissa.is_none() {
                        exponent -= 1;
                        negative = None;
                    }
                    cur = (base as i64)*cur + (d.to_digit(base).unwrap() as
                        i64);
                },
                Some('+') => {
                    if has_digit || negative.is_some() {
                        return None;
                    }
                    negative = Some(false);
                },
                Some('-') => {
                    if has_digit || negative.is_some() {
                        return None;
                    }
                    negative = Some(true);
                },
                Some('.') => {
                    if base != 10 || has_dot {
                        return None;
                    } else {
                        has_dot = true;
                    }
                },
                Some('e') => {
                    if base != 10 || float_mantissa.is_some() || !has_digit {
                        return None;
                    } else {
                        if negative == Some(true) {
                            cur = -cur;
                        }
                        float_mantissa = Some(cur);
                        negative = None;
                        has_digit = false;
                        cur = 0;
                    }
                }
                _ => {return None;},
            }
        }

        if let Some(n) = float_mantissa {
            assert!(base == 10);
            if negative == Some(true) {
                cur = -cur;
            }
            negative = None;
            exponent += cur;
            cur = n;
        }

        if !has_digit & possible_ident {
            if has_dot {return None;} // This is incorrect
            // Ad hoc rule for allowing +/- as identifiers, does not fully
            // incorporate <peculiar identifier>
            return match negative {
                Some(true) => Some(Token::Identifier("-".to_string())),
                Some(false) => Some(Token::Identifier("+".to_string())),
                None => None,
            }
        }

        if negative == Some(true) {
            cur = -cur;
        }

        let multiplier = if exponent >= 0 {
            num::checked_pow(BigRational::from_u32(base)?,
                exponent.to_usize()?)?
        } else {
            num::checked_pow(BigRational::from_u32(base)?.recip(),
                (-exponent).to_usize()?)?
        };

        let value = BigRational::from_i64(cur)? * multiplier;

        let exactness = exactness.unwrap_or(
            if has_dot || float_mantissa.is_some()
                {Exactness::Inexact}
                else {Exactness::Exact});

        Some(Token::Number(Number {exactness, value}))
    }

    fn get_number(&mut self) -> Option<Token> {
        use nom::{
            branch::{alt, permutation},
            bytes::complete::tag,
            character::complete::{one_of, oct_digit1, digit1, hex_digit1},
            combinator::{opt, map, map_opt, flat_map, success},
            regexp::str::{re_match, re_capture},
            sequence::{preceded, pair},
        };
        use num::{BigInt, Num, Zero};

        // radix and exactness written as functions so they can be copied in
        // prefix.
        fn radix(inp: &str) -> nom::IResult<&str, u32> {
            map(preceded(tag("#"), one_of("bBoOdDxX")), |c| match c {
                'b' | 'B' => 2u32,
                'o' | 'O' => 8,
                'd' | 'D' => 10,
                'x' | 'X' => 16,
                _ => unreachable!(),
            })(inp)
        }
        fn exactness(inp: &str) -> nom::IResult<&str, Exactness> {
            map(preceded(tag("#"), one_of("eEiI")), |c| match c {
                'e' | 'E' => Exactness::Exact,
                'i' | 'I' => Exactness::Inexact,
                _ => unreachable!(),
            })(inp)
        }
        let prefix = alt((
            map(pair(radix, exactness), |(b, e)| (b, Some(e))),
            map(pair(exactness, radix), |(e, b)| (b, Some(e))),
            map(radix, |b| (b, None)),
            map(exactness, |e| (10, Some(e))),
            success((10, None)),
        ));

        let mut num = flat_map(prefix, |(base, exactness)| {
            let uinteger_raw = move |inp: &'lexer str| match base {
                2 => re_match(nom::regex::Regex::new("[01]+").unwrap())(inp),
                8 => oct_digit1(inp),
                10 => digit1(inp),
                16 => hex_digit1(inp),
                _ => unreachable!(),
            };
            let mut uinteger = map_opt(uinteger_raw, move |digits|
                BigInt::from_str_radix(digits, base).ok());
            /*
            let mut decimal = map_opt(re_capture(nom::regex::regex::new(
                    r"^([0-9]*)(\.([0-9])*)?([ee]([+-]?[0-9]+))?"
                ).unwrap()), |s| f64::from_str(s).ok()
                    .and_then(bigrational::from_f64).map(|n|
                        number {
                            exactness: exactness::inexact,
                            value: n
                        }
                    )
            );
            */
            let float_re = nom::regex::Regex::new(
                r"^([0-9]*)(\.([0-9]*))?([eE]([+-]?[0-9]+))?").unwrap();

            // This is really messy.
            let mut decimal = map_opt(re_capture(float_re.clone()), move |c_raw|
            {
                    let c = float_re.captures(c_raw[0]).unwrap();
                    if // This condition is wrong
                        base != 10 ||
                        /*
                        dbg!(c.get(1).map_or(true, |s| s.as_str().len() == 0)) &&
                        dbg!(c.get(3).map_or(true, |s| s.as_str().len() == 0)) &&
                        dbg!(c.get(4).is_none())
                        */
                        c.get(1).unwrap().as_str().len() == 0 &&
                        c.get(3).map_or(true, |m| m.as_str().len() == 0) ||
                        c.get(2).is_none() && c.get(4).is_none()
                    {
                        None
                    } else {
                        let integral_str = c.get(1).unwrap().as_str();
                        /*
                        let mut integral = dbg!(c.get(1)).map_or(BigInt::zero(),
                            |s| BigInt::from_str_radix(dbg!(s.as_str()),
                                10).unwrap());
                        */
                        let mut integral = if integral_str.len() > 0
                            {BigInt::from_str_radix(integral_str, 10).unwrap()}
                            else {BigInt::zero()};
                        let fractional = c.get(3).map_or(
                            BigInt::zero(),
                            |s| if s.as_str().len() > 0 {
                                BigInt::from_str_radix(s.as_str(), 10).unwrap()}
                                else {BigInt::zero()}
                        );
                        let frac_len = c.get(3).map_or(0, |s| s.end() -
                            s.start());
                        integral = integral * BigInt::from_u32(10)?
                            .pow(frac_len.to_u32()?) + fractional;
                        let exponent = c.get(5).map_or(0,
                            |s| isize::from_str(s.as_str()).unwrap());
                        let total_exponent = exponent.to_i32()?
                            .checked_sub(frac_len.to_i32()?)?;
                        let rational = BigRational::from_integer(integral) *
                            BigRational::from_u32(10)?.pow(total_exponent);
                        Some(Number {exactness: Exactness::Inexact, value:
                            rational})
                    }
            });
            //dbg!(decimal(" 20"));
            let ureal = alt((
                decimal,
                map(uinteger,
                    |n| Number {
                        exactness: Exactness::Exact,
                        value: n.into(),
                    }),
            ));
            let mut sign = map(opt(one_of("+-")), |s| match s {
                Some('+') | None => 1i32,
                Some('-') => -1i32,
                _ => unreachable!(),
            });
            let mut real = map(pair(sign, ureal), |(s, mut n)| {
                n.value = n.value * BigRational::from_integer(s.into());
                n
            });

            map(real, move |mut n| {
                n.exactness = exactness.unwrap_or(n.exactness);
                Token::Number(n)
            })
        });

        // For compatibility with old version of number lexer incorporate sign
        // identifier
        let mut num_or_sign_id = alt((
            num, 
            map(one_of("+-"), (|s| Token::Identifier(s.to_string()))),
        ));

        // Tell type inference we use default error type
        let ires: nom::IResult<&str, Token> = num_or_sign_id(self.0);
        let (rest, tok) = ires.ok()?;
        self.0 = rest;
        Some(tok)
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

#[cfg(test)]
fn test_lexer_fail(inp: &str) {
    assert_eq!(Lexer::from_str(inp).get_token(), None)
}

#[ignore]
#[test]
fn test_ident() {
    let ident_strs = &["a", "z", "A", "Z", "let*", "!as0", "+", "-", "+@", "+$",
        "+a", "+.+", "..."];
    for ident_str in ident_strs {
        test_lexer(ident_str, Token::Identifier(ident_str.to_string()));
    }
}

#[ignore]
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
fn test_boolean_double_consume() {
    test_lexer_fail("#true#t");
    test_lexer_fail("#false#f");
    test_lexer_fail("#t#true");
    test_lexer_fail("#f#false");
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
    test_lexer("#|# |# 1", Token::from_i64(1));
}

#[test]
fn test_character() {
    test_lexer(r"#\ ", Token::Character(' '));
    test_lexer(r"#\a", Token::Character('a'));
    test_lexer(r"#\⅋", Token::Character('⅋'));
    // Unsure of this one
    test_lexer(r"#\x", Token::Character('x'));
}

#[ignore]
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

#[ignore]
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

#[cfg(test)]
fn test_rational(inp: &str, num: i64, den: i64, exact: Exactness) {
    test_lexer(inp, Token::Number(Number::rational_i64(num, den, exact)))
}

#[cfg(test)]
use self::Exactness::*;

#[test]
fn test_simple_int() {
    test_lexer("13", Token::from_i64(13));
    test_lexer("-4", Token::from_i64(-4));
    test_lexer("+ 20", Token::Identifier("+".to_string()));
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
    test_rational("#i123", 123, 1, Inexact);
    test_lexer("#e#x10", Token::from_i64(16));
    test_lexer("#x#e10", Token::from_i64(16));
    test_rational("#i#x10", 16, 1, Inexact);
    test_rational("#x#i10", 16, 1, Inexact);
}

#[ignore]
#[test]
fn test_fraction() {
    test_rational("1/2", 1, 2, Exact);
    test_rational("#x1/10", 1, 16, Exact);
    test_rational("#i1/2", 1, 2, Inexact);
    test_lexer_fail("1.0/2");
    test_lexer_fail("1/2.0");
}

#[test]
fn test_float() {
    test_rational("1.234e2", 1234, 10, Inexact);
    test_lexer("#e1e2", Token::from_i64(100));
    test_lexer("#e1e0", Token::from_i64(1));
    test_lexer("#e10e-1", Token::from_i64(1));
    test_rational(".10", 1, 10, Inexact);
    test_rational("1e2", 100, 1, Inexact);
    test_rational("13e-10", 13, 10_000_000_000, Inexact);
    test_rational("1.", 1, 1, Inexact);
    test_rational("-1e1", -10, 1, Inexact);
    test_lexer_fail("1e1e1");
}

#[test]
// Ensure an exact float is not pass a precision-losing 
fn test_exact_float() {
    assert_eq!(1.000000000000000001, 1.0);
    test_rational("#e1.000000000000000001",
                     1000000000000000001,
                     1000000000000000000,
                     Exact);
}

#[ignore]
#[test]
fn test_infnan() {
    //test_lexer("+inf.0", ...);
    //test_lexer("-inf.0", ...);
    //test_lexer("+nan.0", ...);
    //test_lexer("-nan.0", ...);
}

#[ignore]
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
    //test_lexer("1.1e1+12/3i". ...);
}

/*
#[test]
fn test_nom_permutations() {
    use nom::{
        branch::{alt, permutation},
        bytes::complete::tag,
        character::complete::{one_of, oct_digit1, digit1, hex_digit1},
        combinator::{opt, map, map_opt, flat_map},
        regexp::str::re_find,
        sequence::{preceded, pair},
    };

    let radix = map(opt(
        map(preceded(tag("#"), one_of("bBoOdDxX")), |c| match c {
            'b' | 'B' => 2u32,
            'o' | 'O' => 8,
            'd' | 'D' => 10,
            'x' | 'X' => 16,
            _ => unreachable!(),
        })), |r| r.unwrap_or(10u32));
    let exactness = opt(
        map(preceded(tag("#"), one_of("eEiI")), |c| match c {
            'e' | 'E' => Exactness::Exact,
            'i' | 'I' => Exactness::Inexact,
            _ => unreachable!(),
        }));
    let mut prefix = permutation((radix, exactness));

    dbg!(prefix("#e#x"));
    dbg!(prefix("#x#e"));
}
*/
