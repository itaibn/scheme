
use std::collections::HashMap;
use std::fmt;
use std::iter::DoubleEndedIterator;
use std::sync::Arc;

// TODO: Rethink derive(PartialEq)
#[derive(Debug, PartialEq)]
enum SchemeData {
    Null,
    Cons(Scheme, Scheme),
    Symbol(String),
    Int(i64),
    Builtin(Builtin),
    Lambda(Lambda),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Scheme(Arc<SchemeData>);

#[derive(Debug)]
pub struct Error;

type Builtin = fn(Vec<Scheme>) -> Result<Scheme, Error>;

#[derive(Debug, PartialEq, Clone)]
struct Lambda {
    binder: Formals,
    body: Scheme,
}

#[derive(Debug, PartialEq, Clone)]
struct Formals {
    head_vars: Vec<String>,
    tail_var: Option<String>,
}

#[derive(Clone, Debug)]
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

    fn lambda(lam: Lambda) -> Scheme {
        Scheme::from_data(SchemeData::Lambda(lam))
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

    fn as_lambda(&self) -> Option<Lambda> {
        if let SchemeData::Lambda(ref lam) = *self.0 {
            Some(lam.clone())
        } else {
            None
        }
    }

    // Use iterators
    fn into_vec(&self) -> Result<Vec<Scheme>, Error> {
        let mut cur_elems = Vec::new();
        let mut head = self;

        loop {
            if let Some((car, cdr)) = head.as_pair() {
                cur_elems.push(car.clone());
                head = cdr;
            } else if head.is_null() {
                return Ok(cur_elems);
            } else {
                return Err(Error);
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
    pub fn eval(&self, env: &Environment) -> Result<Scheme, Error> {
        if let Some(s) = self.as_symbol() {
            if let Some(res) = env.lookup(&s) {
                Ok(res.clone())
            } else {
                Err(Error)
            }
        } else if let Some((operator, operands_linked)) = self.as_pair() {
            // TODO: Special forms
            if let Some("lambda") = operator.as_symbol() {
                let (formals, body) = operands_linked.as_pair().ok_or(Error)?;
                //let binder = formals.as_symbol().ok_or(Error)?;
                let (expr, null) = body.as_pair().ok_or(Error)?;
                if !null.is_null() {
                    return Err(Error);
                }
                Ok(Scheme::lambda(Lambda {
                    binder: Formals::from_object(formals.clone())?,
                    body: expr.clone(),
                }))
            } else {
                // Procedure call
                let operands = operands_linked.into_vec()?;
                let procedure = operator.eval(env)?;
                let arguments = operands.into_iter()
                                        .map(|arg| arg.eval(env))
                                        .collect::<Result<Vec<_>, _>>()?;
                procedure.apply(arguments, env)
            }
        } else if self.as_int().is_some() {
            Ok(self.clone())
        } else {
            Err(Error)
        }
    }

    fn apply(&self, args: Vec<Scheme>, env: &Environment) -> Result<Scheme,
        Error> {

        if let Some(builtin) = self.as_builtin() {
            builtin(args)
        } else if let Some(lambda) = self.as_lambda() {
            let mut new_env = env.clone();
            lambda.binder.match_with_args(args, &mut new_env)?;
            lambda.body.eval(&new_env)
        } else {
            Err(Error)
        }
    }
}

impl fmt::Display for Scheme {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some((a, b)) = self.as_pair() {
            let mut head = b;
            let mut items = vec![a];
            while let Some((a, b)) = head.as_pair() {
                items.push(a);
                head = b;
            }
            write!(f, "(")?;
            for (n, x) in items.into_iter().enumerate() {
                if n > 0 {
                    write!(f, " ")?;
                }
                write!(f, "{}", x)?;
            }
            if head.is_null() {
                write!(f, ")")
            } else {
                write!(f, " . {})", head)
            }
        } else if self.is_null() {
            write!(f, "()")
        } else if let Some(s) = self.as_symbol() {
            write!(f, "{}", s)
        } else if let Some(n) = self.as_int() {
            write!(f, "{}", n)
        } else if let Some(bltin) = self.as_builtin() {
            write!(f, "<builtin at 0x{:x}>", bltin as usize)
        } else if let Some(_) = self.as_lambda() {
            write!(f, "<closure>")
        } else {
            write!(f, "<unrecognized data type>")
        }
    }
}

impl Formals {
    fn from_object(mut head: Scheme) -> Result<Formals, Error> {
        let mut head_vars = Vec::new();
        let tail_var: Option<String>;

        while let Some((a, b)) = head.clone().as_pair() {
            if let Some(ref s) = a.as_symbol() {
                if head_vars.iter().find(|v| s == &*v).is_some() {
                    return Err(Error);
                } else {
                    head_vars.push(s.to_string());
                }
            } else {
                return Err(Error);
            }
            head = b.clone();
        }

        if head.is_null() {
            tail_var = None;
        } else if let Some(ref s) = head.as_symbol() {
            if head_vars.iter().find(|v| s == &*v).is_some() {
                return Err(Error);
            } else {
                tail_var = Some(s.to_string());
            }
        } else {
            return Err(Error);
        }

        Ok(Formals {
            head_vars: head_vars,
            tail_var: tail_var,
        })
    }

    // Current implementation may modify env even if it returns an error
    fn match_with_args(&self, args: Vec<Scheme>, env: &mut Environment) ->
        Result<(), Error> {

        let n = self.head_vars.len();

        if args.len() < n {
            return Err(Error);
        } else {
            for i in 0..self.head_vars.len() {
                env.insert(&self.head_vars[i], args[i].clone());
            }
        }

        match self.tail_var {
            Some(ref varname) => {
                env.insert(varname, Scheme::list_from_iter(
                    args[n..].to_vec()));
                Ok(())
            },
            None => {
                if args.len() == n {
                    Ok(())
                } else {
                    Err(Error)
                }
            }
        }
    }
}

fn sum_builtin(args: Vec<Scheme>) -> Result<Scheme, Error> {
    let mut total = 0;
    for arg in args {
        if let Some(n) = arg.as_int() {
            total += n;
        } else {
            return Err(Error);
        }
    }
    Ok(Scheme::int(total))
}

fn cons_builtin(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() == 2 {
        Ok(Scheme::cons(args[0].clone(), args[1].clone()))
    } else {
        Err(Error)
    }
}

impl Environment {
    fn lookup(&self, variable: &str) -> Option<&Scheme> {
        self.0.get(variable)
    }

    fn insert(&mut self, variable: &str, val: Scheme) {
        self.0.insert(variable.to_string(), val);
    }
}

lazy_static! {
    pub static ref INITIAL_ENVIRONMENT: Environment = {
        let mut hashmap = HashMap::new();
        hashmap.insert("sum".to_string(), Scheme::builtin(sum_builtin));
        hashmap.insert("cons".to_string(), Scheme::builtin(cons_builtin));
        Environment(hashmap)
    };
}

// Only a valid test while "sum" is an alias for "+"
#[test]
fn test_sums() {
    use read::Reader;
    let expr = Reader::new("(sum 1 5 (sum 20) 1)").read_expr().unwrap();
    assert_eq!(expr.eval(&*INITIAL_ENVIRONMENT).unwrap(), Scheme::int(27));
}
