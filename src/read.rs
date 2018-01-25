
use regex::Regex;

#[derive(Debug)]
pub enum Token {
    LeftParen,
    RightParen,
    Identifier(String),
}

lazy_static! {
    // Incomplete
    static ref delimiter: String = format!(r"(:?[|() \t\n\r]|$)");

    // Incomplete
    static ref identifier: String = format!(r"{initial}{subsequent}*",
        initial=&*initial, subsequent=&*subsequent);

    static ref initial: String = format!(r"(:?{letter}|{special_initial})",
        letter=&*letter, special_initial=&*special_initial);

    static ref letter: String = format!(r"[a-zA-Z]");

    static ref special_initial: String = format!(r"[!$%&*:/<=>?@^_~]");

    static ref subsequent: String = format!(
        r"(:?{initial}|{digit}|{special_subsequent})", initial=&*initial,
        digit=&*digit, special_subsequent=&*special_subsequent);

    static ref digit: String = format!(r"[0-9]");

    static ref explicit_sign: String = format!(r"[+-]");

    static ref special_subsequent: String = format!(r"(:?{explicit_sign}|[.@])",
        explicit_sign=&*explicit_sign);
}

#[test]
fn test_identifier_0() {
    let re = Regex::new(&*identifier).unwrap();
    let m = re.find(":dT$+.8!#").unwrap();
    assert_eq!((m.start(), m.end()), (0, 8));
}

#[test]
fn test_identifier_1() {
    let re = Regex::new(&*identifier).unwrap();
    assert!(!re.is_match("54"));
}

#[test]
fn test_identifier_2() {
    let re = Regex::new(&*identifier).unwrap();
    let m = re.find(".+-09A@3 x").unwrap();
    assert_eq!((m.start(), m.end()), (5, 8));
}
