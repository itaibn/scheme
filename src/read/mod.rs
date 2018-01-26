mod lexer;

use scheme::Scheme;
use self::lexer::{Lexer, Token};

use std::mem;

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
            Some(Token::Identifier(ident)) => {
                Ok(Scheme::Symbol(ident))
            },
            Some(Token::LeftParen) => self.read_list(),
            _ => Err("Invalid expression"),
        }
    }

    fn read_list(&mut self) -> Result<Scheme, &'static str> {
        let mut list = Vec::new();

        while self.peek_token()? != Some(&Token::RightParen) {
            list.push(self.read_expr()?);
        }

        assert_eq!(self.read_token(), Ok(Some(Token::RightParen)));

        let mut list_expr = Scheme::Nil;
        for term in list.into_iter().rev() {
            list_expr = Scheme::Cons(Box::new(term), Box::new(list_expr));
        }

        Ok(list_expr)
    }
}
