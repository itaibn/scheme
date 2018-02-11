
use std::collections::HashMap;
use std::iter::DoubleEndedIterator;

#[derive(Clone, Debug, PartialEq)]
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

    // Use iterators
    fn into_vec(&self) -> Option<Vec<Scheme>> {
        let mut cur_elems = Vec::new();
        let mut head = self;

        loop {
            if let Some((car, cdr)) = head.as_pair() {
                cur_elems.push(car.clone());
                head = cdr;
            } else if head.is_null() {
                return Some(cur_elems);
            } else {
                return None;
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
    pub fn eval(&self) -> Scheme {
        if let Some(s) = self.as_symbol() {
            if s == "sum" {
                Scheme::builtin(sum_builtin)
            } else {
                Scheme::symbol(s.to_string())
            }
        } else if self.as_pair().is_some() {
            let args = self.into_vec();
            // TODO: Special forms
            let mut exprs = args.unwrap()
                                .into_iter()
                                .map(|arg| arg.eval())
                                .collect::<Vec<_>>();
            let args = exprs.split_off(1);
            exprs.into_iter().nth(0).unwrap().apply(args)
        } else {
            // Temp
            self.clone()
        }
    }

    fn apply(&self, args: Vec<Scheme>) -> Scheme {
        if let Some(builtin) = self.as_builtin() {
            builtin(args)
        } else {
            Scheme::cons(self.clone(), SchemeData::list_from_iter(args))
        }
    }
}

fn sum_builtin(args: Vec<Scheme>) -> Scheme {
    let mut total = 0;
    for arg in args {
        if let Some(n) = arg.as_int() {
            total += n;
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
