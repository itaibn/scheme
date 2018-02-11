
use std::collections::HashMap;
use std::iter::DoubleEndedIterator;

#[derive(Debug, PartialEq)]
pub enum Scheme {
    Nil,
    Cons(Box<Scheme>, Box<Scheme>),
    Symbol(String),
    Int(i64),
    Builtin(Builtin),
}

type Builtin = fn(Vec<Scheme>) -> Scheme;

pub struct Environment(HashMap<String, Scheme>);

impl Scheme {
    // Use iterators
    fn into_vec(mut self) -> Option<Vec<Scheme>> {
        let mut cur_elems = Vec::new();

        loop {
            match self {
                Scheme::Cons(car, cdr) => {
                    cur_elems.push(*car);
                    self = *cdr;
                },
                Scheme::Nil => {
                    return Some(cur_elems);
                },
                _ => {
                    return None;
                },
            }
        }
    }

    fn list_from_iter<I: IntoIterator<Item=Scheme>>(iter: I) -> Scheme where
        I::IntoIter : DoubleEndedIterator {
        
        let mut res = Scheme::Nil;
        for elem in iter.into_iter().rev() {
            res = Scheme::Cons(Box::new(elem), Box::new(res));
        }
        res
    }

    // Incorporate errors to type signature
    pub fn eval(self) -> Scheme {
        match self {
            Scheme::Symbol(s) => {
                if &s == "sum" {
                    Scheme::Builtin(sum_builtin)
                } else {
                    Scheme::Symbol(s.clone())
                }
            }
            itself @ Scheme::Cons(_, _) => {
                let args = itself.into_vec();
                // TODO: Special forms
                let mut exprs = args.unwrap()
                                    .into_iter()
                                    .map(|arg| arg.eval())
                                    .collect::<Vec<_>>();
                let args = exprs.split_off(1);
                exprs.into_iter().next().unwrap().apply(args)
            },
            // Temp
            _ => self,
        }
    }

    fn apply(self, args: Vec<Scheme>) -> Scheme {
        if let Scheme::Builtin(builtin) = self {
            builtin(args)
        } else {
            Scheme::Cons(Box::new(self), Box::new(Scheme::list_from_iter(args)))
        }
    }
}

fn sum_builtin(args: Vec<Scheme>) -> Scheme {
    let mut total = 0;
    for arg in args {
        match arg {
            Scheme::Int(n) => total += n,
            _ => {},
        }
    }
    Scheme::Int(total)
}

impl Environment {
    fn lookup(&self, variable: &str) -> Option<&Scheme> {
        self.0.get(variable)
    }
}
