
use std::collections::HashMap;

use regex::{Captures, Regex};

#[derive(Debug)]
pub enum Token {
    LeftParen,
    RightParen,
    Identifier(String),
}

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

grammar! {
    // Incomplete
    delimiter -> r"(:?[|() \t\n\r]|$)";

    // Incomplete
    identifier -> r"<<initial>><<subsequent>>*";

    initial -> r"(:?<<letter>>|<<special_initial>>)";

    letter -> r"[a-zA-Z]";

    special_initial -> r"[!$%&*:/<=>?@^_~]";

    subsequent -> r"(:?<<initial>>|<<digit>>|<<special_subsequent>>)";

    digit -> r"[0-9]";

    explicit_sign -> r"[+-]";

    special_subsequent -> r"(:?<<explicit_sign>>|[.@])";
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
