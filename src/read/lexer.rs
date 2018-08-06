
use std::collections::HashMap;

use regex::{Captures, Regex, RegexBuilder};

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    LeftParen,
    LeftVector,
    LeftBytevector,
    RightParen,
    Dot,
    PrefixOp(&'static str),
    Identifier(String),
    Boolean(bool),
    Number(i64),
    Character(char),
    String(Vec<char>),
}

#[derive(Debug)]
pub struct Lexer<'a>(&'a str);

macro_rules! grammar {
    ($($key:ident -> $value:expr;)*) => {lazy_static! {
        static ref GRAMMAR: HashMap<&'static str, &'static str> = {
        /*
            let mut grammar = HashMap::new();
            $(
                grammar.insert(stringify!($key), $value);
            )*
            grammar
        */
            hashmap!($(stringify!($key) => $value),*)
        };
    }}
}

// No unicode support
grammar! {
    //capture_token -> "(?ix)^<<intertoken_space>><<token>>";
    capture_token -> "^<<intertoken_space>><<token>>";
    check_delimiter -> "^<<delimiter>>";

    // Incomplete
    delimiter -> r"(:?[|()\ \t\n\r]|$)";
    token ->
        r"(?P<token><<delimited_token>>|<<undelimited_token>>)";
    // Incomplete
    delimited_token ->
        r"(?P<needs_delimiter><<identifier>>|<<boolean>>|<<number>>|<<character>>|\.)";
    undelimited_token -> r"(:?<<string>>|\(|\)|\#\(|\#u8\(|'|`|,|,@)";
    // Incomplete
    intraspace_whitespace -> r"[\ \t]";
    // Incomplete
    whitespace -> r"<<intraspace_whitespace>>";
    // Incomplete
    atmosphere -> r"<<whitespace>>";
    intertoken_space -> r"(:?<<atmosphere>>*)";
    // Incomplete
    identifier -> r"(?P<identifier><<initial>><<subsequent>>*)";
    initial -> r"(:?<<letter>>|<<special_initial>>)";
    letter -> r"[a-zA-Z]";
    special_initial -> r"[!$%&*:/<=>?@^_~]";
    subsequent -> r"(:?<<initial>>|<<digit>>|<<special_subsequent>>)";
    digit -> r"[0-9]";
    explicit_sign -> r"[+-]";
    special_subsequent -> r"(:?<<explicit_sign>>|[.@])";
    boolean -> r"(?P<truey>\#true|\#t)|(?P<falsey>\#false|\#f)";
    character -> r"(?:\#\\(?P<char>.))";
    // Incomplete
    string -> "(?P<string>\"\")";
    number -> r"<<uinteger>>";
/*
    number -> r"(?P<number><<prefix>><<complex>>)";
    complex -> r"(:?<<real>>|<<real>>@<<real>>|<<real>>\+<<ureal>>i|\
        <<real>>\-<<ureal>>i|<<real>>\+i|<<real>>\-i|<<real>><<infnan>>i|\
        \+<<ureal>>i|\-<<ureal>>i|<<infnan>>i|\+i|\-i)";
    real -> r"(:?<<sign>><ureal>>|<<infnan>>)";
    ureal -> r"(:?<<uinteger>><<suffix>>|\.<<digit>>+<<suffix>>|
        <<digit>>+\.<<digit>>*<<suffix>>)";
*/
    uinteger -> r"(?P<uint><<digit>>+)";
/*
    prefix -> r"(:?<<radix>><<exactness>>|<<exactness>><<radix>>)";
    infnan -> r"(:?\+inf.0|-inf.0|\+nan.0|-nan.0)";
    suffix -> r"(:?<<exponent_marker>><<sign>><<digit>>+)?";
    exponent_marker -> r"e";
    sign -> r"[+-]?";
    exactness -> r"(:?\#[ei])?";
    radix -> r"(:?\#[bodx])?";
*/
}

lazy_static! {
    static ref REGEX: HashMap<&'static str, (String, Regex)> = {
        let re = Regex::new(r"<<([a-z_]*)>>").unwrap();
        let mut done = false;
        let mut res: HashMap<&'static str, (String, Regex)> = HashMap::new();
        while !done {
            done = true;
            let mut progress = false;
            for (class, expression) in GRAMMAR.iter() {
                let mut success = true;
                if res.contains_key(class) {
                    continue;
                }
                let replacement = re.replace_all(expression, |m:&Captures| {
                    let key = m.get(1).unwrap().as_str();
                    match res.get(key) {
                        Some(value) => {
                            value.0.to_string()
                        },
                        None => {
                            success = false;
                            String::new()
                        }
                    }
                });
                if success {
                    let mut builder = RegexBuilder::new(&replacement);
                    builder.case_insensitive(true).ignore_whitespace(true);
                    let regex = builder.build().unwrap_or_else(|err|
                        panic!("Error parsing lexer regex {}\n\nRegex pattern: \
                            {}\nExpanded: {}\nError: {}", class, expression,
                            replacement, err)
                    );
                    res.insert(class, (replacement.into_owned(), regex));
                    progress = true;
                } else {
                    done = false;
                }
            }
            assert!(progress, "No progress. Matched keys: {:?}", res.keys());
        }
        res
    };
}

fn regex_class(class: &'static str) -> Regex {
    REGEX.get(class).unwrap().1.clone()
}

fn read_token(input: &str) -> Option<(Token, &str)> {
    let captures = match regex_class("capture_token").captures(input) {
        None => return None,
        Some(x) => x,
    };

    let end = captures.get(0).unwrap().end();
    let rest = &input[end..];

    if captures.name("needs_delimiter").is_some()
        && !regex_class("check_delimiter").is_match(rest) {
        return None;
    }

    let token = captures_to_token(captures);
    Some((token, rest))
}

fn captures_to_token(captures: Captures) -> Token {
    let m = captures.name("token").unwrap();
    match m.as_str() {
        "(" => return Token::LeftParen,
        ")" => return Token::RightParen,
        "#(" => return Token::LeftVector,
        "#u8(" | "#U8(" => return Token::LeftBytevector,
        "'" => return Token::PrefixOp("quote"),
        "`" => return Token::PrefixOp("quasiquote"),
        "," => return Token::PrefixOp("unquote"),
        ",@" => return Token::PrefixOp("unquote-splicing"),
        "." => return Token::Dot,
        _ => {},
    };
    if let Some(m) = captures.name("identifier") {
        return Token::Identifier(m.as_str().to_string());
    }
    if let Some(c1) = captures.name("char") {
        let c = c1.as_str().chars().next().unwrap();
        return Token::Character(c);
    }
    if let Some(m) = captures.name("uint") {
        let n = i64::from_str_radix(m.as_str(), 10).unwrap();
        return Token::Number(n);
    }
    // Stub
    if captures.name("string").is_some() {
        return Token::String(Vec::new())
    }
    if captures.name("truey").is_some() {
        return Token::Boolean(true);
    }
    if captures.name("falsey").is_some() {
        return Token::Boolean(false);
    }
    panic!("{:?} recognized as token, but doesn't match any specific class of\
        tokens that I can parse", captures.get(0).unwrap().as_str())
}

impl<'a> Lexer<'a> {
    pub fn new(input: &str) -> Lexer {
        Lexer(input)
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, &'static str>;

    fn next(&mut self) -> Option<Self::Item> {
        read_token(self.0).map(|(token, rest)| {
            self.0 = rest;
            Ok(token)
        })
    }
}

#[test]
pub fn test_regex_strings_gen() {
    ::lazy_static::initialize(&REGEX);
}


// Deprecated
#[test]
fn test_valid_regex() {
    for class in GRAMMAR.keys() {
        let string = &REGEX.get(class)
                        .expect(&format!("REGEX_STRINGS doesn't contain key \
                        {:?}", class)).0;
        RegexBuilder::new(string).case_insensitive(true).ignore_whitespace(true).build()
            .expect(&format!("Regex for {} doesn't compile (regex = {:?})", class,
            string));
    }
}

#[test]
fn test_whitespace_0() {
    let re = regex_class("whitespace");
    assert!(re.is_match(" "));
}

#[test]
fn test_identifier_0() {
    let re = regex_class("identifier");
    let m = re.find(":dT$+.8!#").unwrap();
    assert_eq!((m.start(), m.end()), (0, 8));
}

#[test]
fn test_identifier_1() {
    let re = regex_class("identifier");
    assert!(!re.is_match("54"));
}

#[test]
fn test_identifier_2() {
    let re = regex_class("identifier");
    let m = re.find(".+-09A@3 x").unwrap();
    assert_eq!((m.start(), m.end()), (5, 8));
}

#[test]
fn test_token_0() {
    assert_eq!(read_token("("), Some((Token::LeftParen, "")));
}

#[test]
fn test_token_1() {
    assert_eq!(read_token(" )"), Some((Token::RightParen, "")));
}

#[test]
fn test_token_2() {
    assert_eq!(read_token("blah blub"), Some((Token::Identifier(
        "blah".to_string()), " blub")));
}

#[test]
fn test_token_3() {
    assert_eq!(read_token("0.. ("), None);
}

#[test]
fn test_lexer() {
    assert_eq!(Lexer::new("(x y)").collect::<Result<Vec<_>, _>>(),
        Ok(vec![Token::LeftParen, Token::Identifier("x".to_string()),
        Token::Identifier("y".to_string()), Token::RightParen]));
}
