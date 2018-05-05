mod lexer;

use scheme::Scheme;
use self::lexer::{Lexer, Token};

use std::mem;

pub fn read(input: &str) -> Result<Scheme, &'static str> {
    Reader::new(input).read_expr()
}

pub struct Reader<'a> {
    // Fuse?
    lexer: Lexer<'a>,
    cur_token: Option<Token>,
}

impl<'a> Reader<'a> {
    pub fn new(input: &'a str) -> Self {
        Reader {
            lexer: Lexer::new(input),
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

    pub fn peek_token(&mut self) -> Result<Option<&Token>, &'static str> {
        self.fill_cur_token()?;

        Ok(self.cur_token.as_ref())
    }

    pub fn read_token(&mut self) -> Result<Option<Token>, &'static str> {
        self.fill_cur_token()?;
        Ok(mem::replace(&mut self.cur_token, None))
    }

    pub fn read_expr(&mut self) -> Result<Scheme, &'static str> {
        match self.read_token()? {
            Some(Token::Identifier(ident)) => Ok(Scheme::symbol(ident)),
            Some(Token::LeftParen) => self.read_list(),
            Some(Token::PrefixOp(op)) => {
                let operand = self.read_expr()?;
                Ok(Scheme::cons(Scheme::symbol(op.to_string()),
                    Scheme::cons(operand, Scheme::null())))
            }
            Some(Token::Boolean(b)) => Ok(Scheme::boolean(b)),
            Some(Token::Character(c)) => Ok(Scheme::character(c)),
            Some(Token::Number(n)) => Ok(Scheme::int(n)),
            _ => Err("Invalid expression"),
        }
    }

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

        assert_eq!(self.read_token(), Ok(Some(Token::RightParen)));

        for term in list.into_iter().rev() {
            list_expr = Scheme::cons(term, list_expr);
        }

        Ok(list_expr)
    }
}

#[test]
fn test_read_0() {
    read("0").unwrap();
}
