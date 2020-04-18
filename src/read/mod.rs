mod lexer;

use crate::scheme::Scheme;
use self::lexer::{Lexer, Token};

use std::mem;

pub fn read(input: &str) -> Result<Scheme, &'static str> {
    Reader::from_str(input).read_expr()
}

pub struct Reader<'a> {
    // Fuse?
    lexer: Lexer<'a>,
    cur_token: Option<Token>,
}

impl<'a> Reader<'a> {
    pub fn from_str(input: &'a str) -> Self {
        Reader {
            lexer: Lexer::from_str(input),
            cur_token: None,
        }
    }

    fn fill_cur_token(&mut self) -> Result<(), &'static str> {
        if self.cur_token.is_some() {
            return Ok(());
        }

        match self.lexer.next() {
            Some(Ok(tok)) => self.cur_token = Some(tok),
            Some(Err(err)) => return Err(err),
            None => {},
        }

        Ok(())
    }

    /// Output the next token without consuming it
    pub fn peek_token(&mut self) -> Result<Option<&Token>, &'static str> {
        self.fill_cur_token()?;

        Ok(self.cur_token.as_ref())
    }

    /// Output the next token and remove it from the queue
    pub fn read_token(&mut self) -> Result<Option<Token>, &'static str> {
        self.fill_cur_token()?;
        dbg!(Ok(mem::replace(&mut self.cur_token, None)))
    }

    /// Output the next expression and remove all its tokens from the queue
    pub fn read_expr(&mut self) -> Result<Scheme, &'static str> {
        match self.read_token()? {
            Some(Token::Identifier(ident)) => Ok(Scheme::symbol(ident)),
            Some(Token::Boolean(b)) => Ok(Scheme::boolean(b)),
            Some(Token::Character(c)) => Ok(Scheme::character(c)),
            Some(Token::String(s)) => Ok(Scheme::string(s)),
            Some(Token::Number(n)) => Ok(n.to_scheme()),
            Some(Token::LeftParen) => self.read_list(),
            Some(Token::LeftVector) => self.read_vector(),
            Some(Token::LeftBytevector) => self.read_bytevector(),
            Some(Token::PrefixOp(op)) => {
                let operand = self.read_expr()?;
                Ok(Scheme::cons(Scheme::symbol(op.to_string()),
                    Scheme::cons(operand, Scheme::null())))
            }
            _ => Err("Invalid expression"),
        }
    }

    /// Parse a list or a dotted list whose initial left parenthesis has been
    /// consumed.
    fn read_list(&mut self) -> Result<Scheme, &'static str> {
        let mut list = Vec::new();
        let mut list_expr = Scheme::null();

        while self.peek_token()? != Some(&Token::RightParen) {
            if self.peek_token()? == Some(&Token::Dot) {
                self.read_token()?;
                list_expr = self.read_expr()?;
                break;
            }
            list.push(self.read_expr()?);
        }

        for element in list.into_iter().rev() {
            list_expr = Scheme::cons(element, list_expr);
        }

        if self.read_token()? == Some(Token::RightParen) {
            Ok(list_expr)
        } else {
            Err("List doesn't end in right parenthesis")
        }
    }

    /// Parse a vector whose initial left parenthesis has been consumed.
    fn read_vector(&mut self) -> Result<Scheme, &'static str> {
        let mut vector = Vec::new();

        while self.peek_token()? != Some(&Token::RightParen) {
            vector.push(self.read_expr()?);
        }

        if self.read_token() == Ok(Some(Token::RightParen)) {
            Ok(Scheme::vector(vector))
        } else {
            Err("Vector doesn't end in right parenthesis")
        }
    }

    /// Parse a bytevector whose initial left parenthesis has been consumed.
    fn read_bytevector(&mut self) -> Result<Scheme, &'static str> {
        let mut bytevector = Vec::new();
        loop {
            match self.read_token()? {
                // TODO: Better conversion with num crate
                Some(Token::Number(n)) => {
                    match n.as_u8() {
                        Some(k) => bytevector.push(k),
                        None => return Err("non-byte in bytevector"),
                    }
                }
                Some(Token::RightParen) => return Ok(
                    Scheme::bytevector(bytevector)),
                _ => return Err("Unexpected token in bytevector"),
            }
        }
    }
}

#[test]
fn test_read_0() {
    read("0").unwrap();
}

#[test]
fn test_read_vector() {
    assert_eq!(read("#(1 a #t)"), Ok(Scheme::vector(vec![Scheme::int(1),
        Scheme::symbol("a"), Scheme::boolean(true)])))
}

#[test]
fn test_read_bytevector() {
    assert_eq!(read("#U8(0 1 2 3 254 255)"), Ok(Scheme::bytevector(vec![0, 1, 2,
        3, 254, 255])));
}
