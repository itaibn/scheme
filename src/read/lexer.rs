
use std::collections::HashMap;

use regex::{Captures, Regex};

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    LeftParen,
    RightParen,
    Identifier(String),
    Number(i64),
}

#[derive(Debug)]
pub struct Lexer<'a>(&'a str);

macro_rules! grammar {
    ($($key:ident -> $value:expr;)*) => {lazy_static! {
        static ref GRAMMAR: HashMap<&'static str, &'static str> = {
            let mut grammar = HashMap::new();
            $(
                grammar.insert(stringify!($key), $value);
            )*
            grammar
        };
    }}
}

// No unicode support
grammar! {
    capture_token -> "^<<intertoken_space>><<token>>";

    // Incomplete
    delimiter -> r"(:?[|() \t\n\r]|$)";
    // Incomplete
    token -> r"(?P<token><<identifier>>|<<number>>|\(|\))";
    // Incomplete
    intraspace_whitespace -> r"[ \t]";
    // Incomplete
    whitespace -> r"<<intraspace_whitespace>>";
    // Incomplete
    atmosphere -> r"<<whitespace>>";
    intertoken_space -> r"<<atmosphere>>*";
    // Incomplete
    identifier -> r"(?P<identifier><<initial>><<subsequent>>*)";
    initial -> r"(:?<<letter>>|<<special_initial>>)";
    letter -> r"[a-zA-Z]";
    special_initial -> r"[!$%&*:/<=>?@^_~]";
    subsequent -> r"(:?<<initial>>|<<digit>>|<<special_subsequent>>)";
    digit -> r"[0-9]";
    explicit_sign -> r"[+-]";
    special_subsequent -> r"(:?<<explicit_sign>>|[.@])";
    // Incomplete
    number -> r"(?P<uint>[0-9]+)";
}

lazy_static! {
    static ref REGEX_STRINGS: HashMap<&'static str, String> = {
        let re = Regex::new(r"<<([a-z_]*)>>").unwrap();
        let mut done = false;
        let mut res: HashMap<&'static str, String> = HashMap::new();
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
                            value.to_string()
                        },
                        None => {
                            success = false;
                            String::new()
                        }
                    }
                });
                if success {
                    res.insert(class, replacement.into_owned());
                    progress = true;
                } else {
                    done = false;
                }
            }
            assert!(progress);
        }
        res
    };
}

fn regex_class(class: &'static str) -> Regex {
    Regex::new(REGEX_STRINGS.get(class).unwrap()).unwrap()
}

fn read_token(input: &str) -> Option<(Token, &str)> {
    let captures = match regex_class("capture_token").captures(input) {
        None => return None,
        Some(x) => x,
    };

    let end = captures.get(0).unwrap().end();
    let rest = &input[end..];
    let token = captures_to_token(captures);

    Some((token, rest))
}

fn captures_to_token(captures: Captures) -> Token {
    println!("captures_to_token");
    let m = captures.name("token").unwrap();
    match m.as_str() {
        "(" => return Token::LeftParen,
        ")" => return Token::RightParen,
        _ => {},
    };
    if let Some(m) = captures.name("identifier") {
        return Token::Identifier(m.as_str().to_string());
    }
    if let Some(m) = captures.name("uint") {
        let n = i64::from_str_radix(m.as_str(), 10).unwrap();
        return Token::Number(n);
    }
    panic!("{:?} recognized as token, but doesn't match any specific class of\
        token", captures.get(0).unwrap().as_str())
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
    ::lazy_static::initialize(&REGEX_STRINGS);
}

#[test]
fn test_valid_regex() {
    for class in GRAMMAR.keys() {
        let string = REGEX_STRINGS.get(class)
                        .expect(&format!("REGEX_STRINGS doesn't contain key \
                        {:?}", class));
        Regex::new(string).expect(
            &format!("Regex for {} doesn't compile (regex = {:?})", class,
            string));
    }
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
