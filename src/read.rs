
use std::str;

use nom::{IResult, ErrorKind};
use nom::{is_alphabetic, is_alphanumeric};

#[derive(Debug)]
pub enum Token {
    LeftParen,
    RightParen,
    Identifier(String),
}

fn delimiter(rest: &[u8]) -> IResult<&[u8], ()> {
    if rest.len() == 0 {
        return IResult::Done(rest, ());
    }
    if b"|() \t\n\r".contains(&rest[0]) {
        IResult::Done(rest, ())
    } else {
        IResult::Error(ErrorKind::OneOf)
    }
}

named!(pub token<Token>,
    alt!(
        map!(tag!(b"("), |_| Token::LeftParen) |
        map!(tag!(b")"), |_| Token::RightParen) |
        terminated!(identifier, delimiter)
    )
);

/*
named!(identifier<Token>,
    do_parse!(
        // Initial character
        initial: alt!(is_alphabetic/* | one_of!(b"!$%&/:*<=>?^_~" as &[_])*/) >>
        // Subsequent characters
        //subsequent: many0!(alt!(is_alphanumeric | one_of!(b"!$%&*:/<=>?^_~+-.@"
        //    as &[_]))) >>
        ({
            let mut ident = initial.to_string();
            for c in subsequent {
                ident.push(c);
            }
            Token::Identifier(ident)
        })
    )
);
*/
named!(identifier<Token>,
    map!(re_match!(r"[[:alpha:]!$%&*:/<=>?@^_~][[:alpha:]\d!$%&*/:<=>?@^_~+-.@]*"),
        |s| Token::Identifier(str::from_utf8(s).unwrap().to_string())
    )
);
