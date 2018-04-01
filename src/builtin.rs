
use std::collections::HashMap;

use scheme::{Binding, Scheme, Environment, Error};

fn is_integer(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].as_int().is_some()))
    } else {
        Err(Error)
    }
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
            name.to_string(), Binding::Variable(Scheme::builtin(func)));
            
        add_fn("integer?", is_integer);
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
        add_fn("boolean?", is_boolean);
        add_fn("not", not);
    }

    Environment::from_hashmap(hashmap)
}
