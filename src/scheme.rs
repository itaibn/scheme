
// For some reason importing std::borrow::Borrow produces a name collision with
// RefCell::borrow but just importing std::borrow doesn't.
use std::borrow;
use std::fmt;
use std::iter::DoubleEndedIterator;

use gc::Gc;

// Temp
pub use runtime::{Binding, Environment, Procedure};

// TODO: Rethink derive(PartialEq)
#[derive(Clone, Debug, Finalize, PartialEq, Trace)]
enum SchemeData {
    Boolean(bool),
    Character(char),
    Null,
    Cons(Scheme, Scheme),
    Procedure(Procedure),
    Symbol(String),
    Bytevector(Vec<u8>),
    Int(i64),
    String(Vec<char>),
    Vector(Vec<Scheme>),
}

#[derive(Clone, Debug, Finalize, PartialEq, Trace)]
pub struct Scheme(Gc<SchemeData>);

#[derive(Clone, Debug)]
pub struct Error;

impl Scheme {
    fn from_data(data: SchemeData) -> Scheme {
        Scheme(Gc::new(data))
    }

    pub fn boolean(b: bool) -> Scheme {
        Scheme::from_data(SchemeData::Boolean(b))
    }

    pub fn as_boolean(&self) -> Option<bool> {
        if let SchemeData::Boolean(b) = *self.0 {
            Some(b)
        } else {
            None
        }
    }

    pub fn character(c: char) -> Scheme {
        Scheme::from_data(SchemeData::Character(c))
    }

    pub fn as_character(&self) -> Option<char> {
        if let SchemeData::Character(c) = *self.0 {
            Some(c)
        } else {
            None
        }
    }

    pub fn null() -> Scheme {
        Scheme::from_data(SchemeData::Null)
    }

    pub fn is_null(&self) -> bool {
        *self.0 == SchemeData::Null
    }

    pub fn cons(fst: Scheme, snd: Scheme) -> Scheme {
        Scheme::from_data(SchemeData::Cons(fst, snd))
    }

    pub fn as_pair(&self) -> Option<(&Scheme, &Scheme)> {
        if let SchemeData::Cons(ref x, ref y) = *self.0 {
            Some((x, y))
        } else {
            None
        }
    }

    pub(crate) fn procedure(procc: Procedure) -> Scheme {
        Scheme::from_data(SchemeData::Procedure(procc))
    }

    pub(crate) fn as_procedure(&self) -> Option<Procedure> {
        if let SchemeData::Procedure(ref procc) = *self.0 {
            Some(procc.clone())
        } else {
            None
        }
    }

    pub fn symbol<S:ToString>(s: S) -> Scheme {
        Scheme::from_data(SchemeData::Symbol(s.to_string()))
    }

    pub fn as_symbol(&self) -> Option<&str> {
        if let SchemeData::Symbol(ref s) = *self.0 {
            Some(&*s)
        } else {
            None
        }
    }

    pub fn bytevector(bvec: Vec<u8>) -> Scheme {
        Scheme::from_data(SchemeData::Bytevector(bvec))
    }

    pub fn as_bytevector(&self) -> Option<&[u8]> {
        if let SchemeData::Bytevector(ref bvec) = *self.0 {
            Some(&*bvec)
        } else {
            None
        }
    }

    pub fn int(n: i64) -> Scheme {
        Scheme::from_data(SchemeData::Int(n))
    }

    pub fn as_int(&self) -> Option<i64> {
        if let SchemeData::Int(n) = *self.0 {
            Some(n)
        } else {
            None
        }
    }

    pub fn string(s: Vec<char>) -> Scheme {
        Scheme::from_data(SchemeData::String(s))
    }

    pub fn as_string(&self) -> Option<&[char]> {
        if let SchemeData::String(ref s) = *self.0 {
            Some(&*s)
        } else {
            None
        }
    }

    pub fn vector(vec: Vec<Scheme>) -> Scheme {
        Scheme::from_data(SchemeData::Vector(vec))
    }

    pub fn as_vector(&self) -> Option<&[Scheme]> {
        if let SchemeData::Vector(ref vec) = *self.0 {
            Some(&*vec)
        } else {
            None
        }
    }

    pub fn is_literal(&self) -> bool {
           self.as_boolean().is_some()
        || self.as_int().is_some()
        || self.as_character().is_some()
        || self.as_bytevector().is_some()
        || self.as_string().is_some()
        || self.as_vector().is_some()
    }

    pub fn truey(&self) -> bool {
        self.as_boolean() != Some(false)
    }

    // Use iterators
    // May get into infinite loops
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
        } else if let Some(c) = self.as_character() {
            // TODO: escaping appropriate characters
            write!(f, "#\\{}", c)
        } else if let Some(s) = self.as_string() {
            let to_string: String = s.iter().collect();
            // TODO: Scheme-specific escaping
            write!(f, "{:?}", to_string)
        } else if let Some(vec) = self.as_vector() {
            write!(f, "#(")?;
            for (i, x) in vec.iter().enumerate() {
                write!(f, "{}{}", x,
                    if i < vec.len()-1 {' '} else {')'})?;
            }
            Ok(())
        } else if let Some(bvec) = self.as_bytevector() {
            write!(f, "#u8(")?;
            for (i, x) in bvec.iter().enumerate() {
                write!(f, "{}{}", x,
                    if i < bvec.len()-1 {' '} else {')'})?;
            }
            Ok(())
        } else if let Some(procc) = self.as_procedure() {
            //write!(f, "<builtin at 0x{:x}>", bltin as usize)
            write!(f, "{:?}", procc)
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

    #[test]
    fn test_product() {
        comparison("(* 2 2)", Scheme::int(4));
    }

    #[test]
    fn test_if() {
        comparison("(if (= (* 2 2) 4) 3 4)", Scheme::int(3));
    }

    #[test]
    fn test_call_cc() {
        comparison("(call-with-current-continuation (lambda (cont) (* 3 (cont\
            (* 5 6)))))", Scheme::int(30));
    }
}
