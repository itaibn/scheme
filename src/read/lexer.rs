/// A Scheme lexer following the description in Section 7.1 of R7RS. Currently
/// incomplete and doesn't support Unicode.

use std::str::FromStr;

use lazy_static::lazy_static;
use nom::{
    self,
    IResult,
    branch::alt,
    bytes::complete::{tag, tag_no_case, take_till, take_while},
    character::complete::{anychar, digit1, hex_digit1, multispace1, none_of,
        oct_digit1, one_of},
    combinator::{eof, flat_map, map, map_opt, opt, peek, recognize, value,
        success},
    multi::{fold_many0, many0},
    regexp::str::{re_find, re_capture},
    sequence::{delimited, preceded, pair, terminated, tuple},
};
use num::{self, BigRational, FromPrimitive, ToPrimitive};

use crate::number::{self, Exactness};
use crate::scheme::Scheme;

/*
lazy_static! {
    static ref IDENTIFIER: Regex = Regex::new(
        //"^[[:alpha:]!$%&*:/<=>?@^_~][[:alnum:]!$%&*:/<=>?@^_~]*"
        "^[[:alpha:]!$%&*:/<=>?^_~][[:alnum:]!$%&*:/<=>?^_~+-.@]*"
    ).unwrap();
//    static ref STRING: Regex = Regex::new(
//        "^(:?[^\"\\\\]|\\\\(:?[\"\\\\|abtnr]))*\""
}
*/

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq)]
pub struct Number(number::Number);

#[derive(Debug)]
pub struct Lexer<'a>(&'a str);

type LexerError = &'static str;

/*
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
    c.is_ascii_alphabetic() || "!$%&*:/<=>?^_~".contains(c)
}

/// Match <subsequence> pattern. Unicode not supported.
fn is_scheme_identifier_subsequent(c: char) -> bool {
    is_scheme_identifier_initial(c) || c.is_digit(10) || "+-.@".contains(c)
}
*/

impl Number {
    /// If self is an exact u8 return it, otherwise return Nothing.
    pub fn as_u8(&self) -> Option<u8> {
    /*
        if self.exactness == Exactness::Inexact || !self.value.is_integer() {
            None
        } else {
            self.value.to_integer().to_u8()
        }
    */
        if self.0.is_exact() {self.0.to_u8()} else {None}
    }

    /// Convert a number into a Scheme value. Implementation is currently
    /// incomplete.
    pub fn to_scheme(&self) -> Scheme {
        Scheme::number(self.0.clone())
    }

    fn big_rational(r: BigRational, exact: Exactness) -> Number {
        let exact_num = number::Number::from_exact_complex(r.into());
        Number(exact_num.to_exactness(exact))
    }

    /// Rational i64 with exactness. Used in testing
    #[cfg(test)]
    fn rational_i64(num: i64, den: i64, exact: Exactness) -> Number {
        let rat = BigRational::from_i64(num).unwrap() /
            BigRational::from_i64(den).unwrap();
        Number::big_rational(rat, exact)
    }
}

// Unsound and probably unnecessary:
impl Eq for Number {}

impl Token {
    #[cfg(test)]
    fn from_i64(x: i64) -> Token {
        let rat = BigRational::from_i64(x).unwrap();
        let num = Number::big_rational(rat, Exactness::Exact);
        Token::Number(num)
    }

    #[cfg(test)]
    fn from_str(s: &str) -> Token {
        Token::String(s.chars().collect())
    }
}

/// Parser which recognizes delimiters without consuming it.
fn delimiter(inp: &str) -> IResult<&str, ()> {
    peek(alt((
        value((), one_of(" \t\n\r|()\";")),
        value((), eof)
    )))(inp)
}

fn radix(inp: &str) -> IResult<&str, u32> {
    map(preceded(tag("#"), one_of("bBoOdDxX")), |c| match c {
        'b' | 'B' => 2u32,
        'o' | 'O' => 8,
        'd' | 'D' => 10,
        'x' | 'X' => 16,
        _ => unreachable!(),
    })(inp)
}

fn exactness(inp: &str) -> IResult<&str, Exactness> {
    map(preceded(tag("#"), one_of("eEiI")), |c| match c {
        'e' | 'E' => Exactness::Exact,
        'i' | 'I' => Exactness::Inexact,
        _ => unreachable!(),
    })(inp)
}

fn prefix(inp: &str) -> IResult<&str, (u32, Option<Exactness>)> {
    alt((
        map(pair(radix, exactness), |(b, e)| (b, Some(e))),
        map(pair(exactness, radix), |(e, b)| (b, Some(e))),
        map(radix, |b| (b, None)),
        map(exactness, |e| (10, Some(e))),
        success((10, None)),
    ))(inp)
}

fn real<'inp>(base: u32, exactness: Option<Exactness>, input: &'inp str) ->
    IResult<&'inp str, Token> {

    use num::{BigInt, Num, Zero};

    let uinteger_raw = move |inp: &'inp str| match base {
        2 => re_find(nom::regex::Regex::new("^[01]+").unwrap())(inp),
        8 => oct_digit1(inp),
        10 => digit1(inp),
        16 => hex_digit1(inp),
        _ => unreachable!(),
    };
    let uinteger = map_opt(uinteger_raw, move |digits|
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
    let decimal = map_opt(re_capture(float_re.clone()), move |c_raw|
    {
            let c = float_re.captures(c_raw[0]).unwrap();
            if
                base != 10 ||
                c.get(1).unwrap().as_str().len() == 0 &&
                c.get(3).map_or(true, |m| m.as_str().len() == 0) ||
                c.get(2).is_none() && c.get(4).is_none()
            {
                None
            } else {
                let integral_str = c.get(1).unwrap().as_str();
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
                Some((Exactness::Inexact, rational))
            }
    });
    let ureal = alt((
        decimal,
        map(uinteger,
            |n| (Exactness::Exact, n.into())
        ),
    ));
    let sign = map(opt(one_of("+-")), |s| match s {
        Some('+') | None => 1i32,
        Some('-') => -1i32,
        _ => unreachable!(),
    });
    let real = map(pair(sign, ureal), |(s, (e, mut value))| {
        value = value * BigRational::from_integer(s.into());
        (e, value)
    });

    map(real, move |mut n| {
        n.0 = exactness.unwrap_or(n.0);
        let num = Number::big_rational(n.1, n.0);
        Token::Number(num)
    })(input)
}

/// nom parser for a number.
///
/// As a hack, also parses the identifiers `+` or `-`.  Currently only supports
/// integers (at any base) and floats. Supports exactness specifiers.
fn number<'inp>(inp: &'inp str) -> IResult<&'inp str, Token> {
    use num::{BigInt, Num, Zero};

    let num = flat_map(prefix, |(base, exactness)| move |inp| real(base,
        exactness, inp));

    // For compatibility with old version of number lexer incorporate sign
    // identifier
    terminated(alt((
        num, 
        map(one_of("+-"), |s| Token::Identifier(s.to_string())),
    )), delimiter)(inp)
}

/// Shared escape codes used in both pipe identifiers and string literals.
/// Corresponds to <inline hex escape> or <mnemonic escape>, as well as \" and
/// \| and \\ as described in R7RS errata.
fn escape_code(inp: &str) -> IResult<&str, char> {
    alt((
        value('\u{7}', tag("\\a")),
        value('\u{8}', tag("\\b")),
        value('\u{9}', tag("\\t")),
        value('\u{a}', tag("\\n")),
        value('\u{d}', tag("\\r")),
        value('\\',    tag("\\\\")),
        value('|',     tag("\\|")),
        delimited(tag("\\x"),
            map_opt(hex_digit1,
                |esc| u32::from_str_radix(esc, 16).ok()
                    .and_then(std::char::from_u32)),
            tag(";"))
    ))(inp)
}

fn string_literal(inp: &str) -> IResult<&str, Token> {
    map(delimited(
        tag("\""),
        fold_many0(alt((
                map(none_of("\r\n\\\""), Some),
                value(Some('\n'), alt((tag("\n"), tag("\r\n"), tag("\r")))),
                map(escape_code, Some),
                value(None, tuple((
                    tag("\\"),
                    take_while(|c| c == ' ' || c == '\t'),
                    alt((tag("\n"), tag("\r\n"), tag("\r"))),
                    take_while(|c| c == ' ' || c == '\t')))),
            )),
            Vec::new(),
            |mut v, maybe_c| {
                maybe_c.map(|c| v.push(c));
                v
            }
        ),
        tag("\"")
    ), |v_char| Token::String(v_char))(inp)
}

/// nom parser which consumes whitespace and comments.
///
/// This is like the <intertoken space> category in the standard, except it
/// doesn't support datum comments, and directives are counted as tokens.
///
/// TODO: Improve the type signature.
fn intertoken_space(inp: &str) -> IResult<&str, Vec<&str>> {
    lazy_static! {
        // A non-nesting part of a nesting comment
        static ref NON_NESTING_COMMENT: nom::regex::Regex =
            nom::regex::Regex::new(r"^([^|#]|#+([^|]|$)|\|+([^#]|$))+")
                .unwrap();
    }

    // A custom version of not_line_ending necessary since the nom version
    // doesn't recognize a lone '\r' (cf. nom issue #1273)
    let not_line_ending = take_till(|c| c == '\n' || c == '\r');

    // Strictly speaking this differs from the standard which would
    // recognize ";<line>\r\n" as a single <comment>, whereas with this
    // definition ";<line>\r" would match <comment> and then "\n" would
    // match as a second <atmosphere>. Since this function matches an entire
    // <intertoken space> this distinction is irrelevant.
    let line_comment = recognize(tuple((tag(";"), not_line_ending,
        one_of("\n\r"))));

    fn nested_comment(inp: &str) -> IResult<&str, &str> {
        let non_nesting_comment = re_find(NON_NESTING_COMMENT.clone());
        recognize(tuple((
            tag("#|"),
            many0(alt((non_nesting_comment, nested_comment))),
            tag("|#")
        )))(inp)
    }

    many0(alt((line_comment, multispace1, nested_comment)))(inp)
}

fn simple_token(inp: &str) -> IResult<&str, Token> {
    alt((
        value(Token::LeftParen, tag("(")),
        value(Token::LeftVector, tag("#(")),
        value(Token::LeftBytevector, tag_no_case("#u8(")),
        value(Token::RightParen, tag(")")),
        value(Token::DatumComment, tag("#;")),
        value(Token::PrefixOp("quote"), tag("'")),
        value(Token::PrefixOp("quasiquote"), tag("`")),
        value(Token::PrefixOp("unquote-splicing"), tag(",@")),
        value(Token::PrefixOp("unquote"), tag(",")),
        terminated(alt((
            value(Token::Dot, tag(".")),
            value(Token::Boolean(true), tag_no_case("#true")),
            value(Token::Boolean(true), tag_no_case("#t")),
            value(Token::Boolean(false), tag_no_case("#false")),
            value(Token::Boolean(false), tag_no_case("#f")),
            value(Token::FoldCase(true), tag_no_case("#!fold-case")),
            value(Token::FoldCase(false), tag_no_case("#!no-fold-case")),
        )), delimiter)
    ))(inp)
}

fn character(inp: &str) -> IResult<&str, Token> {
    delimited(
        tag("#\\"),
        map(alt((
            value('\u{7}', tag_no_case("alarm")),
            value('\u{8}', tag_no_case("backspace")),
            value('\u{7f}', tag_no_case("delete")),
            value('\u{1b}', tag_no_case("escape")),
            value('\u{a}', tag_no_case("newline")),
            value('\u{0}', tag_no_case("null")),
            value('\u{d}', tag_no_case("return")),
            value(' ', tag_no_case("space")),
            value('\u{9}', tag_no_case("tab")),
            map_opt(preceded(tag_no_case("x"), hex_digit1),
                |hex| u32::from_str_radix(hex, 16).ok()
                        .and_then(std::char::from_u32)),
            anychar
        )), Token::Character),
        delimiter
    )(inp)
}

fn simple_identifier(inp: &str) -> IResult<&str, Token> {
    lazy_static! {
        static ref IDENTIFIER: nom::regex::Regex = nom::regex::Regex::new(
            //"^[[:alpha:]!$%&*/:<=>?@^_~][[:alnum:]!$%&*/:<=>?@^_~]*"
            "^[[:alpha:]!$%&*/:<=>?^_~][[:alnum:]!$%&*/:<=>?^_~+-.@]*"
        ).unwrap();
    }

    map(
        terminated(re_find(IDENTIFIER.clone()), delimiter),
        |ident| Token::Identifier(ident.to_string())
    )(inp)
}

fn token(inp: &str) -> IResult<&str, Token> {
    preceded(intertoken_space,
        alt((
            simple_token,
            number,
            string_literal,
            character,
            simple_identifier
    )))(inp)
}

// TODO: Comprehensive todo list, data comments, full number support, peculiar
// identifiers, strings, pipe notation for identifiers, verifying agreement with
// lexer specifications in Section 7.1.1
impl<'a> Lexer<'a> {
    pub fn from_str(input_str: &'a str) -> Lexer<'a> {
        Lexer(input_str)
    }

    /// Either consume and output a single token from the input stream, or
    /// output None while consuming an unspecified numbere of characters from
    /// the input stream.
    pub fn get_token(&mut self) -> Option<Token> {
        let (rest, tok) = token(self.0).ok()?;
        self.0 = rest;
        Some(tok)
    }
}

impl Iterator for Lexer<'_> {
    type Item = Result<Token, LexerError>;

    // TODO: Distinguist EOF and error
    fn next(&mut self) -> Option<Self::Item> {
        self.get_token().map(Ok)
    }
}

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
    test_lexer("#U8(", Token::LeftBytevector);
    test_lexer("#t", Token::Boolean(true));
    test_lexer("#true", Token::Boolean(true));
    test_lexer("#tRUe", Token::Boolean(true));
    test_lexer("#TRUE", Token::Boolean(true));
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
    test_lexer(";\n3", Token::from_i64(3));
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
    test_lexer(r"#\A", Token::Character('A'));
    test_lexer(r"#\⅋", Token::Character('⅋'));
    // Unsure of this one
    test_lexer(r"#\x", Token::Character('x'));
    // Test that characters require a delimiter
    test_lexer_fail(r"#\f12");
    test_lexer_fail(r"#\uident");
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
    test_lexer_fail("\"xx");
}

#[ignore]
#[test]
fn test_string_escapes() {
    test_lexer("\"x\\\"x\"", Token::from_str("x\"x"));
    test_lexer_fail("\"\\\"");
    test_lexer("\"\\\\\"", Token::from_str("\\"));
    test_lexer("\"\\au\"", Token::from_str("\u{7}u"));
    // Mnemonic escapes are case-sensitive, cf. R7RS p. 61
    test_lexer_fail("\"\\A\"");
    test_lexer("\"s\\bs\"", Token::from_str("s\u{8}s"));
    test_lexer("\"4\\tt\"", Token::from_str("4\tt"));
    test_lexer("\" \\n\\n\"", Token::from_str(" \n\n"));
    test_lexer("\"\\r\\n\"", Token::from_str("\r\n"));
    test_lexer("\"\\||\"", Token::from_str("||"));
    test_lexer("\"\\x61;\"", Token::from_str("a"));
    test_lexer("\"\\X0100000;\"", Token::from_str("\u{100000}"));

    test_lexer("\"a\\\nb\"", Token::from_str("ab"));
    test_lexer("\"a\\ \n\tb\"", Token::from_str("ab"));
    test_lexer("\"a\\\t \r  b\"", Token::from_str("ab"));
    test_lexer("\"a\\\t \r\n  b\"", Token::from_str("ab"));
    test_lexer("\"a\\ \n\nb\"", Token::from_str("a\nb"));
}

#[test]
// Any newline corresponds in the string literal corresponds to a '\n' in the
// corresponding string, see R7RS p. 46.
fn test_string_newline() {
    test_lexer("\"a\\ \r\rb\"", Token::from_str("a\nb"));
    test_lexer("\"a\\ \r\r\nc\"", Token::from_str("a\nc"));
    test_lexer("\"a\\ \n\r\nd\"", Token::from_str("a\nd"));
    test_lexer("\"\n\"", Token::from_str("\n"));
    test_lexer("\"\r\"", Token::from_str("\n"));
    test_lexer("\"\r\n\"", Token::from_str("\n"));
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
    test_lexer_fail("#bxxx101");
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
