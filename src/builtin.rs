
use std::collections::HashMap;

use scheme::{Scheme, Environment, Error};

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
        let arg = args[0].clone();
        if let Some((_, b)) = arg.as_pair() {
            Ok(b.clone())
        } else {
            Err(Error)
        }
    } else {
        Err(Error)
    }
}

pub fn initial_environment() -> Environment {
    let mut hashmap = HashMap::new();
    // Rename
    hashmap.insert("sum".to_string(), Scheme::builtin(sum));
    // Rename
    hashmap.insert("minus".to_string(), Scheme::builtin(minus));
    hashmap.insert("*".to_string(), Scheme::builtin(times));
    hashmap.insert("cons".to_string(), Scheme::builtin(cons));
    hashmap.insert("car".to_string(), Scheme::builtin(car));
    hashmap.insert("cdr".to_string(), Scheme::builtin(cdr));
    Environment::from_hashmap(hashmap)
}
