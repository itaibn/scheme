
use std::cmp;
use std::collections::HashMap;

use either::{Either, Left, Right};

use runtime::{self, Continuation, Environment, Expression, Task};
use scheme::{self, Scheme, Error};

fn quote(operands: Vec<Expression>, _: Environment, c: Continuation) ->
    Result<Task, Error> {

    if operands.len() != 1 {
        Err(Error)
    } else {
        Ok(c.pass_value(operands[0].0.clone()))
    }
}

fn syntax_if(operands: Vec<Expression>, env: Environment, c: Continuation) ->
    Result<Task, Error> {

    if operands.len() != 3 {
        Err(Error)
    } else {
        let mut iter = operands.into_iter();
        let cond = iter.next().unwrap();
        let if_true = iter.next().unwrap();
        let if_false = iter.next().unwrap();

        let if_true_task = Task::eval(if_true, env.clone(), c.clone());
        let if_false_task = Task::eval(if_false, env.clone(), c);
        let new_continuation = Continuation::if_then_else(if_true_task,
            if_false_task);

        Ok(Task::eval(cond, env, new_continuation))
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

fn comparison<F>(args: Vec<Scheme>, cmp: F) -> Result<Scheme, Error>
    where F: Fn(i64, i64) -> bool {

    if args.len() < 2 {
        return Err(Error);
    }
    let mut previous = match args[0].as_int() {
        Some(n) => n,
        None => return Err(Error),
    };
    let mut condition = true;
    for elem in &args[1..] {
        match elem.as_int() {
            Some(next) => {
                if cmp(previous, next) {
                    previous = next;
                } else {
                    condition = false;
                }
            },
            None => return Err(Error),
        }
    }
    Ok(Scheme::boolean(condition))
}

fn num_eq(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    comparison(args, |n, m| n == m)
}

fn less(args: Vec<Scheme>,  _: Environment) -> Result<Scheme, Error> {
    comparison(args, |n, m| n < m)
}

fn greater(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    comparison(args, |n, m| n > m)
}

fn less_equal(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    comparison(args, |n, m| n <= m)
}

fn greater_equal(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    comparison(args, |n, m| n >= m)
}

fn is_zero(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() != 1 || args[0].as_int().is_none() {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].as_int() == Some(0)))
}

fn is_positive(args: Vec<Scheme>,  _: Environment) -> Result<Scheme, Error> {
    if args.len() != 1 || args[0].as_int().is_none() {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].as_int().unwrap() > 0))
}

fn is_negative(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() != 1 || args[0].as_int().is_none() {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].as_int().unwrap() < 0))
}

fn is_odd(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() != 1 || args[0].as_int().is_none() {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].as_int().unwrap() % 2 == 1))
}

fn is_even(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() != 1 || args[0].as_int().is_none() {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].as_int().unwrap() % 2 == 0))
}

fn max(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() <= 1 {
        return Err(Error);
    }
    let mut max = match args[0].as_int() {
        Some(n) => n,
        None => return Err(Error),
    };
    for element in &args[1..] {
        match element.as_int() {
            Some(n) => {
                max = cmp::max(max, n);
            },
            None => {
                return Err(Error);
            },
        }
    }
    Ok(Scheme::int(max))
}

fn min(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() <= 1 {
        return Err(Error);
    }
    let mut min = match args[0].as_int() {
        Some(n) => n,
        None => return Err(Error),
    };
    for element in &args[1..] {
        match element.as_int() {
            Some(n) => {
                min = cmp::min(min, n);
            },
            None => {
                return Err(Error);
            },
        }
    }
    Ok(Scheme::int(min))
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

fn times(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    let mut total = 1;
    for arg in args {
        if let Some(n) = arg.as_int() {
            total *= n;
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

// The rest of the numerical procedures are unimplemented

// Section 6.3: Booleans

fn not(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(!args[0].truey()))
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

fn boolean_equal(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() < 2 {
        return Err(Error);
    }
    let bool_value = args[0].as_boolean().ok_or(Error)?;
    let mut equal_so_far = true;
    for elem in &args[1..] {
        let as_bool = elem.as_boolean().ok_or(Error)?;
        equal_so_far = equal_so_far && (as_bool == bool_value);
    }
    Ok(Scheme::boolean(equal_so_far))
}

// Section 6.4: Pairs and lists

fn is_pair(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].as_pair().is_some()))
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

// set-car! and set-cdr! unimplemented since there's mutable pair support.
// caar...cddddr unimplemented because they're tedious

fn is_null(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].is_null()))
    } else {
        Err(Error)
    }
}

fn is_list(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() != 1 {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].into_vec().is_ok()))
}

fn make_list(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 0 || args.len() > 2 {
        return Err(Error);
    }
    let length = args[0].as_int().ok_or(Error)?;
    if length < 0 {
        return Err(Error);
    }
    let fill = if args.len() == 2 {
        args[1].clone()
    } else {
        // Unspecified
        Scheme::int(0)
    };
    let mut new_list = Scheme::null();
    for _ in 0..length {
        new_list = Scheme::cons(fill.clone(), new_list);
    }
    Ok(new_list)
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

fn append(mut args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    let mut tail = args.pop().unwrap_or_else(|| Scheme::null());
    for list in args.iter().rev() {
        for item in list.into_vec()?.iter().rev() {
            tail = Scheme::cons(item.clone(), tail);
        }
    }
    Ok(tail)
}

fn reverse(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() != 1 {
        return Err(Error);
    }
    let mut list = args[0].clone();
    let mut reversed = Scheme::null();
    loop {
        let new_list;
        if list.is_null() {
            return Ok(reversed);
        } else if let Some((item, rest)) = list.as_pair() {
            reversed = Scheme::cons(item.clone(), reversed);
            // Borrow checking nonsense
            new_list = rest.clone();
        } else {
            return Err(Error);
        }
        list = new_list;
    }
}

fn list_tail(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() != 2 {
        return Err(Error);
    }
    let mut list = args[0].clone();
    let k = args[1].as_int().ok_or(Error)?;
    if k < 0 {
        return Err(Error);
    }
    for _ in 0..k {
        let new_list;
        if let Some((_, rest)) = list.as_pair() {
            // Borrow checking nonsense
            new_list = rest.clone();
        } else {
            return Err(Error);
        }
        list = new_list;
    }
    Ok(list)
}

fn list_ref(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() != 2 {
        return Err(Error);
    }
    let mut list = args[0].clone();
    let k = args[1].as_int().ok_or(Error)?;
    if k < 0 {
        return Err(Error);
    }
    for _ in 0..k {
        let new_list;
        if let Some((_, rest)) = list.as_pair() {
            // Borrow check nonsense
            new_list = rest.clone();
        } else {
            return Err(Error);
        }
        list = new_list;
    }
    if let Some((item, _)) = list.as_pair() {
        Ok(item.clone())
    } else {
        Err(Error)
    }
}

// Omitted: list-set! memq memv member assq assv assoc list-copy

fn is_symbol(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].as_symbol().is_some()))
    } else {
        Err(Error)
    }
}

fn symbol_to_string(args: Vec<Scheme>, _: Environment) -> Result<Scheme, Error>
{
    if args.len() != 1 {
        return Err(Error);
    }
    if let Some(symb_str) = args[0].as_symbol() {
        let string: Vec<char> = symb_str.chars().collect();
        Ok(Scheme::string(string))
    } else {
        Err(Error)
    }
}

pub fn initial_environment() -> Environment {
    let mut hashmap = HashMap::new();

    {
        let mut add_fn = |name: &'static str, func| hashmap.insert(
            name.to_string(), scheme::Binding::Variable(
                                Scheme::procedure(
                                    runtime::Procedure::builtin(func))));
            
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
        add_fn("<", less);
        add_fn(">", greater);
        add_fn("<=", less_equal);
        add_fn(">=", greater_equal);
        add_fn("zero?", is_zero);
        add_fn("positive?", is_positive);
        add_fn("negative?", is_negative);
        add_fn("odd?", is_odd);
        add_fn("even?", is_even);
        add_fn("max", max);
        add_fn("min", min);
        // Rename
        add_fn("sum", sum);
        add_fn("*", times);
        // Rename
        add_fn("minus", minus);
        add_fn("not", not);
        add_fn("boolean?", is_boolean);
        add_fn("boolean=?", boolean_equal);
        add_fn("pair?", is_pair);
        add_fn("cons", cons);
        add_fn("car", car);
        add_fn("cdr", cdr);
        add_fn("null?", is_null);
        add_fn("list?", is_list);
        add_fn("make-list", make_list);
        add_fn("list", list);
        add_fn("length", length);
        add_fn("append", append);
        add_fn("reverse", reverse);
        add_fn("list-tail", list_tail);
        add_fn("list-ref", list_ref);
        add_fn("symbol?", is_symbol);
        add_fn("symbol->string", symbol_to_string);
    }
    hashmap.insert("lambda".to_string(),
        scheme::Binding::Syntax(runtime::lambda));
    hashmap.insert("quote".to_string(),
        scheme::Binding::Syntax(quote));
    hashmap.insert("if".to_string(),
        scheme::Binding::Syntax(syntax_if));

    Environment::from_hashmap(hashmap)
}
