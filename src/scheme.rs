
use std::collections::HashMap;
use std::iter::DoubleEndedIterator;
use std::sync::Arc;

#[derive(Debug, PartialEq)]
enum SchemeData {
    Null,
    Cons(Scheme, Scheme),
    Symbol(String),
    Int(i64),
    Builtin(Builtin),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Scheme(Arc<SchemeData>);

type Builtin = fn(Vec<Scheme>) -> Scheme;

pub struct Environment(HashMap<String, Scheme>);

impl Scheme {
    fn from_data(data: SchemeData) -> Scheme {
        Scheme(Arc::new(data))
    }

    pub fn null() -> Scheme {
        Scheme::from_data(SchemeData::Null)
    }

    pub fn cons(fst: Scheme, snd: Scheme) -> Scheme {
        Scheme::from_data(SchemeData::Cons(fst, snd))
    }

    pub fn symbol(s: String) -> Scheme {
        Scheme::from_data(SchemeData::Symbol(s))
    }

    pub fn int(n: i64) -> Scheme {
        Scheme::from_data(SchemeData::Int(n))
    }

    fn builtin(func: Builtin) -> Scheme {
        Scheme::from_data(SchemeData::Builtin(func))
    }

    pub fn is_null(&self) -> bool {
        *self.0 == SchemeData::Null
    }

    pub fn as_pair(&self) -> Option<(&Scheme, &Scheme)> {
        if let SchemeData::Cons(ref x, ref y) = *self.0 {
            Some((x, y))
        } else {
            None
        }
    }

    pub fn as_symbol(&self) -> Option<&str> {
        if let SchemeData::Symbol(ref s) = *self.0 {
            Some(&*s)
        } else {
            None
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        if let SchemeData::Int(n) = *self.0 {
            Some(n)
        } else {
            None
        }
    }

    fn as_builtin(&self) -> Option<Builtin> {
        if let SchemeData::Builtin(func) = *self.0 {
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
    pub fn eval(&self, env: &Environment) -> Scheme {
        if let Some(s) = self.as_symbol() {
            if let Some(res) = env.lookup(&s) {
                res.clone()
            } else {
                Scheme::symbol(s.to_string())
            }
        } else if self.as_pair().is_some() {
            let args = self.into_vec();
            // TODO: Special forms
            let mut exprs = args.unwrap()
                                .into_iter()
                                .map(|arg| arg.eval(env))
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
            Scheme::cons(self.clone(), Scheme::list_from_iter(args))
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

lazy_static! {
    pub static ref INITIAL_ENVIRONMENT: Environment = {
        let mut hashmap = HashMap::new();
        hashmap.insert("sum".to_string(), Scheme::builtin(sum_builtin));
        Environment(hashmap)
    };
}

// Only a valid test while "sum" is an alias for "+"
#[test]
fn test_sums() {
    use read::Reader;
    let expr = Reader::new("(sum 1 5 (sum 20) 1)").read_expr().unwrap();
    assert_eq!(expr.eval(&*INITIAL_ENVIRONMENT), Scheme::int(27));
}
