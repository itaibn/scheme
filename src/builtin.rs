
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

fn begin(operands: Vec<Expression>, env: Environment, c: Continuation) ->
    Result<Task, Error> {

    let (first, rest) = operands.split_first().ok_or(Error)?;
    let cont = Continuation::begin(rest.to_vec(), env.clone(), c);
    Ok(Task::eval(first.clone(), env, cont))
}

// TODO: include, include-ci, cond, case, and, or, when, unless, cond-expand,
// let, let*, letrec, let-values, let*-values, begin, do, let, (lazy delay),
// (lazy delay-force), (lazy force), (lazy promise?), (lazy make-promise),
// make-parameter, parameterize, guard, quasiquote, (case-lambda case-lambda),
// let-syntax, letrec-syntax, syntax-error 

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

fn comparison<A, Conv, Comp>(args: Vec<Scheme>, convert: Conv, cmp: Comp) ->
        Result<Scheme, Error>
    where
        Conv: Fn(&Scheme) -> Option<A>,
        Comp: Fn(&A, &A) -> bool {

    if args.len() < 2 {
        return Err(Error);
    }
    let mut previous = match convert(&args[0]) {
        Some(n) => n,
        None => return Err(Error),
    };
    let mut condition = true;
    for elem in &args[1..] {
        match convert(elem) {
            Some(next) => {
                if cmp(&previous, &next) {
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

fn int_comparison<F>(args: Vec<Scheme>, cmp: F) -> Result<Scheme, Error>
    where F: Fn(i64, i64) -> bool {

    comparison(args, |x| x.as_int(), |n, m| cmp(*n, *m))
}

// TODO: Replace below function implementations with direct calls to comparison,
// & remove int_comparison.

fn num_eq(args: Vec<Scheme>) -> Result<Scheme, Error> {
    int_comparison(args, |n, m| n == m)
}

fn less(args: Vec<Scheme>) -> Result<Scheme, Error> {
    int_comparison(args, |n, m| n < m)
}

fn greater(args: Vec<Scheme>) -> Result<Scheme, Error> {
    int_comparison(args, |n, m| n > m)
}

fn less_equal(args: Vec<Scheme>) -> Result<Scheme, Error> {
    int_comparison(args, |n, m| n <= m)
}

fn greater_equal(args: Vec<Scheme>) -> Result<Scheme, Error> {
    int_comparison(args, |n, m| n >= m)
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
        Scheme::unspecified()
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

// Section 6.5: Symbols

// Note: Standard is unclear what to return or error when the output is not #t.
fn is_symbol(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() == 1 {
        Ok(Scheme::boolean(args[0].as_symbol().is_some()))
    } else {
        Err(Error)
    }
}

fn symbol_eq(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() < 2 {
        return Err(Error);
    }
    if let Some(symb_str) = args[0].as_symbol() {
        let mut res = true;
        for symb in &args[1..] {
            if let Some(other_symb_str) = symb.as_symbol() {
                if symb_str != other_symb_str {
                    res = false
                }
            } else {
                return Err(Error)
            }
        }
        Ok(Scheme::boolean(res))
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

fn string_to_symbol(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() != 1 {
        return Err(Error);
    }
    if let Some(scheme_string) = args[0].as_string() {
        let string: String = scheme_string.iter().collect();
        Ok(Scheme::symbol(string))
    } else {
        Err(Error)
    }
}

// Section 6.6: Characters

fn is_char(args: Vec<Scheme>) -> Result<Scheme, Error> {
    if args.len() != 1 {
        return Err(Error);
    }
    Ok(Scheme::boolean(args[0].as_character().is_some()))
}

fn char_eq(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, |x| x.as_character(), char::eq)
}

fn char_lt(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, |x| x.as_character(), char::lt)
}

fn char_gt(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, |x| x.as_character(), char::gt)
}

fn char_le(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, |x| x.as_character(), char::le)
}

fn char_ge(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, |x| x.as_character(), char::ge)
}

// TODO: Full Unicode compliance
fn convert_char_ci(x: &Scheme) -> Option<char> {
    if let Some(c) = x.as_character() {
        // NOTE: A proper implementation should use foldcase, not lowercase.
        let mut lowercase = c.to_lowercase();
        let res = lowercase.next().expect(&format!("I didn't know Unicode \
            characters could have the empty string as a lowercase form ({})",
            c));
        assert!(lowercase.next().is_none(), "'{}' converts into a \
            multi-character lowercase string and probably has behavior I don't \
            know how to handle.");
        Some(res)
    } else {
        None
    }
}

// char library procedure
fn char_ci_eq(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, convert_char_ci, char::eq)
}

// char library procedure
fn char_ci_lt(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, convert_char_ci, char::lt)
}

// char library procedure
fn char_ci_gt(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, convert_char_ci, char::gt)
}

// char library procedure
fn char_ci_le(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, convert_char_ci, char::le)
}

// char library procedure
fn char_ci_ge(args: Vec<Scheme>) -> Result<Scheme, Error> {
    comparison(args, convert_char_ci, char::ge)
}

// TODO: (char digit-value) char->integer integer->char (char char-upcase) (char
// char-downcase) (char char-foldcase)

// TODO: Section 6.7 Strings, 6.8 Vectors, 6.9 Bytevectors, 6.10 Control
// features, 6.11 Exceptions 6.12 Environments and evaluation 6.13 Input and
// output, 6.14 System interface

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

    let pre_hashmap = hashmap! {
        "lambda" => syntax(runtime::lambda),
        "quote" => syntax(quote),
        "if" => syntax(syntax_if),
        "set!" => syntax(set),
        "begin" => syntax(begin),

        "integer?" => simple(is_integer),
        // Temporary: Integers are the only numerical types, so all other type
        // predicates and some other numerical predicates are aliases of
        // integer?
        "number?" => simple(is_integer),
        "complex?" => simple(is_integer),
        "real?" => simple(is_integer),
        "exact?" => simple(is_integer),
        "inexact?" => simple(false_predicate),
        "exact-integer?" => simple(is_integer),
        "finite?" => simple(is_integer),
        "infinite?" => simple(false_predicate),
        "nan?" => simple(false_predicate),
        "=" => simple(num_eq),
        "<" => simple(less),
        ">" => simple(greater),
        "<=" => simple(less_equal),
        ">=" => simple(greater_equal),
        "zero?" => simple(is_zero),
        "positive?" => simple(is_positive),
        "negative?" => simple(is_negative),
        "odd?" => simple(is_odd),
        "even?" => simple(is_even),
        "max" => simple(max),
        "min" => simple(min),
        "+" => simple(sum),
        "*" => simple(times),
        "-" => simple(minus),
        "not" => simple(not),
        "boolean?" => simple(is_boolean),
        "boolean=?" => simple(boolean_equal),
        "pair?" => simple(is_pair),
        "cons" => simple(cons),
        "car" => simple(car),
        "cdr" => simple(cdr),
        "set-car!" => simple(set_car),
        "set-cdr!" => simple(set_cdr),
        "null?" => simple(is_null),
        "list?" => simple(is_list),
        "make-list" => simple(make_list),
        "list" => simple(list),
        "length" => simple(length),
        "append" => simple(append),
        "reverse" => simple(reverse),
        "list-tail" => simple(list_tail),
        "list-ref" => simple(list_ref),
        "symbol?" => simple(is_symbol),
        "symbol=?" => simple(symbol_eq),
        "symbol->string" => simple(symbol_to_string),
        "string->symbol" => simple(string_to_symbol),
        "char?" => simple(is_char),
        "char=?" => simple(char_eq),
        "char<?" => simple(char_lt),
        "char>?" => simple(char_gt),
        "char<=?" => simple(char_le),
        "char>=?" => simple(char_ge),
        // char library procedure
        "char-ci=?" => simple(char_ci_eq),
        // char library procedure
        "char-ci<?" => simple(char_ci_lt),
        // char library procedure
        "char-ci>?" => simple(char_ci_gt),
        // char library procedure
        "char-ci<=?" => simple(char_ci_le),
        // char library procedure
        "char-ci>=?" => simple(char_ci_ge),
        "call-with-current-continuation" =>
            complex(call_with_current_continuation),
        "call/cc" => complex(call_with_current_continuation),
    };

    let mut hashmap = std::collections::HashMap::new();
    for (key, value) in pre_hashmap {
        hashmap.insert(key.to_string(), value);
    }

    Environment::from_hashmap(hashmap)
}
