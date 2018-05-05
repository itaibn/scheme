
// For some reason importing std::borrow::Borrow produces a name collision with
// RefCell::borrow but just importing std::borrow doesn't.
use std::borrow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::iter::DoubleEndedIterator;
use std::rc::Rc;

// TODO: Rethink derive(PartialEq)
#[derive(Clone, Debug, PartialEq)]
enum SchemeData {
    Null,
    Cons(Scheme, Scheme),
    Symbol(String),
    Boolean(bool),
    Int(i64),
    Character(char),
    Builtin(Builtin),
    Lambda(Lambda),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Scheme(Rc<SchemeData>);

#[derive(Debug)]
pub struct Error;

type Builtin = fn(Vec<Scheme>, Environment) -> Result<Scheme, Error>;

#[derive(Debug, Clone, PartialEq)]
struct Lambda {
    binder: Formals,
    body: Scheme,
    environment: Environment,
}

#[derive(Debug, Clone, PartialEq)]
struct Formals {
    head_vars: Vec<String>,
    tail_var: Option<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Environment(Rc<RefCell<EnvironmentData>>);

#[derive(Clone, Debug, PartialEq)]
pub struct EnvironmentData {
    parent: Option<Environment>,
    local: HashMap<String, Binding>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Binding {
    Variable(Scheme),
    Syntax(BuiltinSyntax),
}

type BuiltinSyntax = Builtin;

impl Scheme {
    fn from_data(data: SchemeData) -> Scheme {
        Scheme(Rc::new(data))
    }

    pub fn null() -> Scheme {
        Scheme::from_data(SchemeData::Null)
    }

    pub fn cons(fst: Scheme, snd: Scheme) -> Scheme {
        Scheme::from_data(SchemeData::Cons(fst, snd))
    }

    pub fn symbol<S:ToString>(s: S) -> Scheme {
        Scheme::from_data(SchemeData::Symbol(s.to_string()))
    }

    pub fn boolean(b: bool) -> Scheme {
        Scheme::from_data(SchemeData::Boolean(b))
    }

    pub fn character(c: char) -> Scheme {
        Scheme::from_data(SchemeData::Character(c))
    }

    pub fn int(n: i64) -> Scheme {
        Scheme::from_data(SchemeData::Int(n))
    }

    pub(crate) fn builtin(func: Builtin) -> Scheme {
        Scheme::from_data(SchemeData::Builtin(func))
    }

    fn lambda(lam: Lambda) -> Scheme {
        Scheme::from_data(SchemeData::Lambda(lam))
    }

    pub fn is_null(&self) -> bool {
        *self.0 == SchemeData::Null
    }

    pub fn is_literal(&self) -> bool {
           self.as_boolean().is_some()
        || self.as_int().is_some()
        || self.as_character().is_some()
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

    pub fn as_boolean(&self) -> Option<bool> {
        if let SchemeData::Boolean(b) = *self.0 {
            Some(b)
        } else {
            None
        }
    }

    pub fn as_character(&self) -> Option<char> {
        if let SchemeData::Character(c) = *self.0 {
            Some(c)
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

    pub fn truey(&self) -> bool {
        self.as_boolean() != Some(false)
    }

    // Use iterators
    pub fn into_vec(&self) -> Result<Vec<Scheme>, Error> {
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

    pub fn list<E: borrow::Borrow<Scheme>, I: IntoIterator<Item=E>>(iter: I) ->
        Scheme where I::IntoIter : DoubleEndedIterator {

        let mut res = Scheme::null();
        for elem in iter.into_iter().rev() {
            res = Scheme::cons(elem.borrow().clone(), res);
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
            if let Some(x) = operator.as_symbol() {
                if let Some(Binding::Syntax(form)) = env.lookup_binding(x) {
                    return form(operands_linked.into_vec()?, env.clone())
                }
            }
            // Procedure call
            let operands = operands_linked.into_vec()?;
            let procedure = operator.eval(env)?;
            let arguments = operands.into_iter()
                                    .map(|arg| arg.eval(env))
                                    .collect::<Result<Vec<_>, _>>()?;
            procedure.apply(arguments, env)
        } else if self.is_literal() {
            Ok(self.clone())
        } else {
            Err(Error)
        }
    }

    fn apply(&self, args: Vec<Scheme>, env: &Environment) -> Result<Scheme,
        Error> {

        if let Some(builtin) = self.as_builtin() {
            builtin(args, env.clone())
        } else if let Some(lambda) = self.as_lambda() {
            let new_env = lambda.environment.make_child();
            lambda.binder.match_with_args(args, &new_env)?;
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
        } else if let Some(b) = self.as_boolean() {
            let c = if b {'t'} else {'f'};
            write!(f, "#{}", c)
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

/*
impl fmt::Debug for SchemeData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", Scheme::from_data(self.clone()))
    }
}
*/

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
    fn match_with_args(&self, args: Vec<Scheme>, env: &Environment) ->
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
                env.insert(varname, Scheme::list(&args[n..]));
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

impl Environment {
    fn from_data(data: EnvironmentData) -> Environment {
        Environment(Rc::new(RefCell::new(data)))
    }

    // Rethink structure
    pub fn from_hashmap(hmap: HashMap<String, Binding>) -> Environment {
        Environment::from_data(EnvironmentData {
            parent: None,
            local: hmap,
        })
    }

    fn lookup(&self, variable: &str) -> Option<Scheme> {
        match self.lookup_binding(variable) {
            Some(Binding::Variable(val)) => Some(val),
            _ => None,
        }
    }

    fn lookup_binding(&self, variable: &str) -> Option<Binding> {
        let EnvironmentData {ref parent, ref local} = *self.0.borrow();
        local.get(variable).cloned()
             .or_else(||
                parent.as_ref().and_then(|env| env.lookup_binding(variable)))
    }

    fn insert(&self, variable: &str, val: Scheme) {
        self.0.borrow_mut().local.insert(variable.to_string(),
            Binding::Variable(val));
    }

    fn make_child(&self) -> Environment {
        Environment::from_data(EnvironmentData {
            parent: Some(self.clone()),
            local: HashMap::new(),
        })
    }
}

pub fn lambda(operands: Vec<Scheme>, env: Environment) -> Result<Scheme, Error>
{
    let operands_linked = Scheme::list(operands);
    let (formals, body) = operands_linked.as_pair().ok_or(Error)?;
    //let binder = formals.as_symbol().ok_or(Error)?;
    let (expr, null) = body.as_pair().ok_or(Error)?;
    if !null.is_null() {
        return Err(Error);
    }
    Ok(Scheme::lambda(Lambda {
        binder: Formals::from_object(formals.clone())?,
        body: expr.clone(),
        environment: env.clone(),
    }))
}

#[cfg(test)]
mod test {
    use builtin::initial_environment;
    use read::read;
    use super::Scheme;

    fn comparison(input: &str, output: Scheme) {
        let expr = read(input).unwrap();
        assert_eq!(expr.eval(&initial_environment()).unwrap(), output);
    }

    // Only a valid test while "sum" is an alias for "+"
    #[test]
    fn test_sums() {
        comparison("(sum 1 5 (sum 20) 1)", Scheme::int(27));
    }

    #[test]
    fn test_lambda_0() {
        comparison("((lambda (x) x) 3)", Scheme::int(3));
    }

    #[test]
    fn test_lambda_1() {
        comparison("(((lambda (x) (lambda (y) x)) 1) 2)", Scheme::int(1));
    }

    #[test]
    fn test_lambda_2() {
        comparison("(((lambda (y) ((lambda (x) (lambda (y) x)) y)) 1) 2)",
            Scheme::int(1));
    }

    #[test]
    fn test_lambda_3() {
        comparison("((lambda (x . y) (cons y x)) 2 3 4)", Scheme::cons(
            Scheme::cons(Scheme::int(3), Scheme::cons(Scheme::int(4),
            Scheme::null())), Scheme::int(2)));
    }

    #[test]
    fn test_quote() {
        comparison("''foo", Scheme::cons(Scheme::symbol("quote".to_string()),
            Scheme::cons(Scheme::symbol("foo".to_string()), Scheme::null())));
    }

    #[test]
    fn test_bool() {
        comparison("#TrUe", Scheme::boolean(true));
    }

    #[test]
    fn test_length() {
        comparison("(length (cons 1 (list 2 3 4 5)))", Scheme::int(5));
    }

    #[test]
    fn test_character() {
        comparison("#\\n", Scheme::character('n'));
    }

    #[test]
    fn test_pair_syntax() {
        comparison("'(a . b)", Scheme::cons(Scheme::symbol("a"),
            Scheme::symbol("b")));
    }
}
