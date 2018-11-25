
use std::cmp;

use crate::runtime::{self,
    Continuation,
    Environment,
    Expression,
    Task
};
use crate::scheme::{Error, Scheme};

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

        let new_continuation = Continuation::if_then_else(if_true, if_false,
            env.clone(), c);

        Ok(Task::eval(cond, env, new_continuation))
    }
}

fn set(operands: Vec<Expression>, env: Environment, c: Continuation) ->
    Result<Task, Error> {

    if operands.len() != 2 {
        Err(Error)
    } else {
        if let Some(var) = operands[0].as_symbol() {
            let set_continuation = Continuation::set(var.to_string(),
                env.clone(), c);
            Ok(Task::eval(operands[1].clone(), env, set_continuation))
        } else {
            Err(Error)
        }
    }
}

// A predicate which is false for any argument, and gives an error when given
// zero or more than one arguments. Currently a few predicates alias to this
// since I don't support the full set of Scheme types.
fn false_predicate(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(false))
    } else {
        Err(Error)
    }
}

// Temporary: Integers are the only numerical types, so all other type
// predicates are aliases of integer?
fn is_integer(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn num_eq(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, |n, m| n == m)
}

fn less(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, |n, m| n < m)
}

fn greater(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, |n, m| n > m)
}

fn less_equal(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, |n, m| n <= m)
}

fn greater_equal(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, |n, m| n >= m)
}

fn is_zero(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() != 1 || args[0].as_int().is_none() {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].as_int() == Some(0)))
}

fn is_positive(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() != 1 || args[0].as_int().is_none() {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].as_int().unwrap() > 0))
}

fn is_negative(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() != 1 || args[0].as_int().is_none() {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].as_int().unwrap() < 0))
}

fn is_odd(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() != 1 || args[0].as_int().is_none() {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].as_int().unwrap() % 2 == 1))
}

fn is_even(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() != 1 || args[0].as_int().is_none() {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].as_int().unwrap() % 2 == 0))
}

fn max(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn min(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn sum(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn times(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn minus(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn not(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(!args[0].truey()))
    } else {
        Err(Error)
    }
}

fn is_boolean(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].as_boolean().is_some()))
    } else {
        Err(Error)
    }
}

fn boolean_equal(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn is_pair(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].as_pair().is_some()))
    } else {
        Err(Error)
    }
}

fn cons(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() == 2 {
        Ok(Scheme::cons(args[0].clone(), args[1].clone()))
    } else {
        Err(Error)
    }
}

fn car(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn cdr(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn set_car(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() == 2 {
        let (car, _) = args[0].as_pair_mut().ok_or(Error)?;
        car.replace(args[1].clone());
        Ok(Scheme::unspecified())
    } else {
        Err(Error)
    }
}

fn set_cdr(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() == 2 {
        let (_, cdr) = args[0].as_pair_mut().ok_or(Error)?;
        cdr.replace(args[1].clone());
        Ok(Scheme::unspecified())
    } else {
        Err(Error)
    }
}

// caar...cddddr unimplemented because they're tedious

fn is_null(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].is_null()))
    } else {
        Err(Error)
    }
}

fn is_list(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() != 1 {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].into_vec().is_ok()))
}

fn make_list(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn list(args: Vec<Scheme>) -> Result<Scheme, Error> {
    Ok(Scheme::list(args))
}

fn length(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::int(args[0].into_vec()?.len() as i64))
    } else {
        Err(Error)
    }
}

fn append(mut args: Vec<Scheme>) -> Result<Scheme, Error> {
    let mut tail = args.pop().unwrap_or_else(|| Scheme::null());
    for list in args.iter().rev() {
        for item in list.into_vec()?.iter().rev() {
            tail = Scheme::cons(item.clone(), tail);
        }
    }
    Ok(tail)
}

fn reverse(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn list_tail(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn list_ref(args: Vec<Scheme>) -> Result<Scheme, Error> {
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

fn is_symbol(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].as_symbol().is_some()))
    } else {
        Err(Error)
    }
}

fn symbol_to_string(args: Vec<Scheme>) -> Result<Scheme, Error>
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

fn call_with_current_continuation(args: Vec<Scheme>, env: Environment, ctx:
    Continuation) -> Result<Task, Error> {

    if args.len() != 1 {
        return Err(Error);
    }
    let cont_obj =
        Scheme::procedure(runtime::Procedure::continuation(ctx.clone()));
    Ok(Task::apply(args[0].clone(), vec![cont_obj], env, ctx))
}

pub fn initial_environment() -> Environment {
    use crate::runtime::{Binding, Builtin, BuiltinSyntax, SimpleBuiltin};

    fn simple(f: SimpleBuiltin) -> Binding {
        Binding::variable(Scheme::procedure(runtime::Procedure::simple_builtin(f)))
    }

    fn complex(f: Builtin) -> Binding {
        Binding::variable(Scheme::procedure(runtime::Procedure::builtin(f)))
    }

    fn syntax(f: BuiltinSyntax) -> Binding {
        Binding::Syntax(f)
    }

    let hashmap = hashmap! {
        "integer?".to_string() => simple(is_integer),
        // Temporary: Integers are the only numerical types, so all other type
        // predicates and some other numerical predicates are aliases of
        // integer?
        "number?".to_string() => simple(is_integer),
        "complex?".to_string() => simple(is_integer),
        "real?".to_string() => simple(is_integer),
        "exact?".to_string() => simple(is_integer),
        "inexact?".to_string() => simple(false_predicate),
        "exact-integer?".to_string() => simple(is_integer),
        "finite?".to_string() => simple(is_integer),
        "infinite?".to_string() => simple(false_predicate),
        "nan?".to_string() => simple(false_predicate),
        "=".to_string() => simple(num_eq),
        "<".to_string() => simple(less),
        ">".to_string() => simple(greater),
        "<=".to_string() => simple(less_equal),
        ">=".to_string() => simple(greater_equal),
        "zero?".to_string() => simple(is_zero),
        "positive?".to_string() => simple(is_positive),
        "negative?".to_string() => simple(is_negative),
        "odd?".to_string() => simple(is_odd),
        "even?".to_string() => simple(is_even),
        "max".to_string() => simple(max),
        "min".to_string() => simple(min),
        // Rename
        "sum".to_string() => simple(sum),
        "*".to_string() => simple(times),
        // Rename
        "minus".to_string() => simple(minus),
        "not".to_string() => simple(not),
        "boolean?".to_string() => simple(is_boolean),
        "boolean=?".to_string() => simple(boolean_equal),
        "pair?".to_string() => simple(is_pair),
        "cons".to_string() => simple(cons),
        "car".to_string() => simple(car),
        "cdr".to_string() => simple(cdr),
        "set-car!".to_string() => simple(set_car),
        "set-cdr!".to_string() => simple(set_cdr),
        "null?".to_string() => simple(is_null),
        "list?".to_string() => simple(is_list),
        "make-list".to_string() => simple(make_list),
        "list".to_string() => simple(list),
        "length".to_string() => simple(length),
        "append".to_string() => simple(append),
        "reverse".to_string() => simple(reverse),
        "list-tail".to_string() => simple(list_tail),
        "list-ref".to_string() => simple(list_ref),
        "symbol?".to_string() => simple(is_symbol),
        "symbol->string".to_string() => simple(symbol_to_string),
        "call-with-current-continuation".to_string() =>
            complex(call_with_current_continuation),

        "lambda".to_string() => syntax(runtime::lambda),
        "quote".to_string() => syntax(quote),
        "if".to_string() => syntax(syntax_if),
        "set!".to_string() => syntax(set)
    };

    Environment::from_hashmap(hashmap)
}
