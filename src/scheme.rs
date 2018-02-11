
use std::collections::HashMap;
use std::iter::DoubleEndedIterator;

#[derive(Debug, PartialEq)]
pub enum SchemeData {
    Null,
    Cons(Box<Scheme>, Box<Scheme>),
    Symbol(String),
    Int(i64),
    Builtin(Builtin),
}

pub type Scheme = SchemeData;

type Builtin = fn(Vec<Scheme>) -> Scheme;

pub struct Environment(HashMap<String, Scheme>);

impl SchemeData {
    // Use iterators
    fn into_vec(mut self) -> Option<Vec<Scheme>> {
        let mut cur_elems = Vec::new();

        loop {
            match self {
                SchemeData::Cons(car, cdr) => {
                    cur_elems.push(*car);
                    self = *cdr;
                },
                SchemeData::Null => {
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
        
        let mut res = Scheme::null();
        for elem in iter.into_iter().rev() {
            res = Scheme::cons(elem, res);
        }
        res
    }

    // Incorporate errors to type signature
    pub fn eval(self) -> Scheme {
        match self {
            SchemeData::Symbol(s) => {
                if &s == "sum" {
                    Scheme::builtin(sum_builtin)
                } else {
                    Scheme::symbol(s.clone())
                }
            }
            itself @ SchemeData::Cons(_, _) => {
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
        if let SchemeData::Builtin(builtin) = self {
            builtin(args)
        } else {
            Scheme::cons(self, SchemeData::list_from_iter(args))
        }
    }
}

impl Scheme {
    pub fn null() -> Scheme {
        SchemeData::Null
    }

    pub fn cons(fst: Scheme, snd: Scheme) -> Scheme {
        SchemeData::Cons(Box::new(fst), Box::new(snd))
    }

    pub fn symbol(s: String) -> Scheme {
        SchemeData::Symbol(s)
    }

    pub fn int(n: i64) -> Scheme {
        SchemeData::Int(n)
    }

    fn builtin(func: Builtin) -> Scheme {
        SchemeData::Builtin(func)
    }

    pub fn is_null(&self) -> bool {
        *self == SchemeData::Null
    }

    pub fn as_pair(&self) -> Option<(&Scheme, &Scheme)> {
        if let &SchemeData::Cons(ref x, ref y) = self {
            Some((x, y))
        } else {
            None
        }
    }

    pub fn as_symbol(&self) -> Option<&str> {
        if let &SchemeData::Symbol(ref s) = self {
            Some(&*s)
        } else {
            None
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        if let &SchemeData::Int(n) = self {
            Some(n)
        } else {
            None
        }
    }

    fn as_builtin(&self) -> Option<Builtin> {
        if let &SchemeData::Builtin(func) = self {
            Some(func)
        } else {
            None
        }
    }
}

fn sum_builtin(args: Vec<Scheme>) -> Scheme {
    let mut total = 0;
    for arg in args {
        match arg {
            SchemeData::Int(n) => total += n,
            _ => {},
        }
    }
    Scheme::int(total)
}

impl Environment {
    fn lookup(&self, variable: &str) -> Option<&Scheme> {
        self.0.get(variable)
    }
}

// Only a valid test while "sum" is an alias for "+"
#[test]
fn test_sums() {
    use read::Reader;
    let expr = Reader::new("(sum 1 5 (sum 20) 1)").read_expr().unwrap();
    assert_eq!(expr.eval(), Scheme::int(27));
}
