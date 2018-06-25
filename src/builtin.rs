
use std::collections::HashMap;

use runtime;
use scheme::{self, Scheme, Environment, Error};

fn quote(operands: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if operands.len() != 1 {
        Err(Error)
    } else {
        Ok(operands[0].clone())
    }
}

fn syntax_if(operands: Vec<Scheme>, env: Environment) -> Result<Scheme, Error> {
    if operands.len() != 3 {
        Err(Error)
    } else {
        let mut iter = operands.into_iter();
        let cond = iter.next().unwrap();
        let if_true = iter.next().unwrap();
        let if_false = iter.next().unwrap();
        assert_eq!(iter.next(), None);

        if cond.eval(&env)?.truey() {
            if_true.eval(&env)
        } else {
            if_false.eval(&env)
        }
    }
}

// A predicate which is false for any argument, and gives an error when given
// zero or more than one arguments. Currently a few predicates alias to this
// since I don't support the full set of Scheme types.
fn false_predicate(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(false))
    } else {
        Err(Error)
    }
}

// Temporary: Integers are the only numerical types, so all other type
// predicates are aliases of integer?
fn is_integer(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].as_int().is_some()))
    } else {
        Err(Error)
    }
}

fn num_eq(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() < 2 {
        return Err(Error)
    }
    let fst = match args[0].as_int() {
        Some(n) => n,
        None => return Err(Error),
    };
    for elem in &args[1..] {
        match elem.as_int() {
            Some(other) => {
                if fst == other {
                    continue;
                } else {
                    return Ok(Scheme::boolean(false));
                }
            },
            None => return Err(Error),
        }
    }
    Ok(Scheme::boolean(true))
}

fn sum(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
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

fn minus(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if !args.is_empty() {
        let fst_num: i64;
        if let Some(n) = args[0].as_int() {
            fst_num = n;
        } else {
            return Err(Error);
        }
        if args.len() > 1 {
            let mut total = fst_num;
            for arg in &args[1..] {
                if let Some(n) = arg.as_int() {
                    total -= n;
                } else {
                    return Err(Error);
                }
            }
            Ok(Scheme::int(total))
        } else {
            Ok(Scheme::int(-fst_num))
        }
    } else {
        Err(Error)
    }
}

fn times(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    let mut total = 1;
    for arg in args {
        if let Some(n) = arg.as_int() {
            total -= n;
        } else {
            return Err(Error);
        }
    }
    Ok(Scheme::int(total))
}

fn is_pair(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].as_pair().is_some()))
    } else {
        Err(Error)
    }
}

fn is_null(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].is_null()))
    } else {
        Err(Error)
    }
}

fn cons(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 2 {
        Ok(Scheme::cons(args[0].clone(), args[1].clone()))
    } else {
        Err(Error)
    }
}

fn car(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        let arg = args[0].clone();
        if let Some((a, _)) = arg.as_pair() {
            Ok(a.clone())
        } else {
            Err(Error)
        }
    } else {
        Err(Error)
    }
}

fn cdr(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        if let Some((_, b)) = args[0].as_pair() {
            Ok(b.clone())
        } else {
            Err(Error)
        }
    } else {
        Err(Error)
    }
}

fn list(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    Ok(Scheme::list(args))
}

fn length(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::int(args[0].into_vec()?.len() as i64))
    } else {
        Err(Error)
    }
}

fn is_symbol(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].as_symbol().is_some()))
    } else {
        Err(Error)
    }
}

fn is_boolean(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].as_boolean().is_some()))
    } else {
        Err(Error)
    }
}

fn not(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(!args[0].truey()))
    } else {
        Err(Error)
    }
}

pub fn initial_environment() -> Environment {
    let mut hashmap = HashMap::new();

    {
        let mut add_fn = |name: &'static str, func| hashmap.insert(
            name.to_string(), scheme::Binding::Variable(Scheme::builtin(func)));
            
        add_fn("integer?", is_integer);
        // Temporary: Integers are the only numerical types, so all other type
        // predicates and some other numerical predicates are aliases of
        // integer?
        add_fn("number?", is_integer);
        add_fn("complex?", is_integer);
        add_fn("real?", is_integer);
        add_fn("exact?", is_integer);
        add_fn("inexact?", false_predicate);
        add_fn("exact-integer?", is_integer);
        add_fn("finite?", is_integer);
        add_fn("infinite?", false_predicate);
        add_fn("nan?", false_predicate);
        add_fn("=", num_eq);
        // Rename
        add_fn("sum", sum);
        // Rename
        add_fn("minus", minus);
        add_fn("*", times);
        add_fn("pair?", is_pair);
        add_fn("null?", is_null);
        add_fn("cons", cons);
        add_fn("car", car);
        add_fn("cdr", cdr);
        add_fn("list", list);
        add_fn("length", length);
        add_fn("symbol?", is_symbol);
        add_fn("boolean?", is_boolean);
        add_fn("not", not);
    }
    hashmap.insert("lambda".to_string(),
        scheme::Binding::Syntax(runtime::lambda));
    hashmap.insert("quote".to_string(),
        scheme::Binding::Syntax(quote));
    hashmap.insert("if".to_string(),
        scheme::Binding::Syntax(syntax_if));

    Environment::from_hashmap(hashmap)
}
