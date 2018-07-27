
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use either::{Either, Left, Right};

use scheme::{Error, Scheme};

/// Wrapper type for unevaluated Scheme expressions.
#[derive(Clone, Debug, PartialEq)]
pub struct Expression(pub Scheme);

// Clone-by-reference environment
#[derive(Clone, Debug, PartialEq)]
pub struct Environment(Rc<RefCell<EnvironmentData>>);

/*
// TEMP: Make Environment in Debug easier to read but less informative
impl fmt::Debug for Environment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<environment {:x}>", self.deref() as *const _ as usize)
    }
}
*/

#[derive(Clone, Debug, PartialEq)]
pub struct EnvironmentData {
    parent: Option<Environment>,
    local: HashMap<String, Binding>,
}

// pub?
#[derive(Clone, Debug, PartialEq)]
pub enum Binding {
    Variable(Scheme),
    Syntax(BuiltinSyntax),
}

#[derive(Debug, Clone)]
pub struct Continuation(Rc<ContinuationData>);

#[derive(Debug)]
enum ContinuationData {
    // Left-to-right evaluation order for now
    Application {
        values: Vec<Scheme>,
        expressions: Vec<Expression>,
        environment: Environment,
        next_continuation: Continuation,
    },
    // TODO: Only allow evaluation tasks in this continuation
    IfThenElse {
        if_true: Task,
        if_false: Task,
    },
    End,
}

#[derive(Clone, Debug)]
pub struct Task(TaskEnum);

#[derive(Clone, Debug)]
enum TaskEnum {
    Eval {
        expression: Expression,
        environment: Environment,
        continuation: Continuation,
    },
    Apply {
        procedure: Scheme,
        arguments: Vec<Scheme>,
        environment: Environment,
        continuation: Continuation,
    },
    Done(Scheme),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Procedure(ProcEnum);

#[derive(Clone, Debug, PartialEq)]
enum ProcEnum {
    Builtin(Builtin),
    Lambda(Lambda),
}

// pub?
pub type Builtin = fn(Vec<Scheme>, Environment) -> Result<Scheme, Error>;

// pub?
pub type BuiltinSyntax = fn(Vec<Expression>, Environment, Continuation) ->
    Result<Task, Error>;

// pub?
#[derive(Debug, Clone, PartialEq)]
pub struct Lambda {
    binder: Formals,
    body: Expression,
    environment: Environment,
}

#[derive(Debug, Clone, PartialEq)]
struct Formals {
    head_vars: Vec<String>,
    tail_var: Option<String>,
}

impl Continuation {
    fn from_data(data: ContinuationData) -> Continuation {
        Continuation(Rc::new(data))
    }

    pub fn if_then_else(if_true: Task, if_false: Task) -> Continuation {
        Continuation::from_data(ContinuationData::IfThenElse {
            if_true, if_false
        })
    }

    pub fn pass_value(self, value: Scheme) -> Task {
        match *self.0 {
            ContinuationData::Application {ref values, ref expressions,
                ref environment, ref next_continuation} => {

                let mut new_values = values.clone();
                let mut new_expressions = expressions.clone();
                new_values.push(value);
                match new_expressions.pop() {
                    Some(expr) => {
                        let new_continuation = Continuation::from_data(
                            ContinuationData::Application {
                                values: new_values,
                                expressions: new_expressions,
                                environment: environment.clone(),
                                next_continuation: next_continuation.clone(),
                            });
                        Task::eval(expr, environment.clone(),
                            new_continuation)
                    },
                    None => {
                        Task::apply(new_values[0].clone(),
                            new_values[1..].to_vec(), environment.clone(),
                            next_continuation.clone())
                    },
                }
            },
            ContinuationData::IfThenElse {ref if_true, ref if_false} => {
                if value.truey() {
                    if_true.clone()
                } else {
                    if_false.clone()
                }
            },
            ContinuationData::End => Task::done(value),
        }
    }
}

impl Default for Continuation {
    fn default() -> Continuation {
        Continuation::from_data(ContinuationData::End)
    }
}

impl Task {
    /// Construct the task for evaluating `expr` in environment `env` & passing
    /// the result to continuation `cont`. Does not do any work in evaluating
    /// `expr`.
    pub fn eval(expr: Expression, env: Environment, cont: Continuation) -> Task
    {
        Task(TaskEnum::Eval {
            expression: expr,
            environment: env,
            continuation: cont,
        })
    }

    /// Construct the task for applying the procedure `procedure` to arguments
    /// `args` in environment `env` and passing the result to continuation
    /// `cont`. Does not apply the function to the argument.
    pub fn apply(procedure: Scheme, args: Vec<Scheme>, env: Environment, cont:
        Continuation) -> Task {
        Task(TaskEnum::Apply {
            procedure: procedure,
            arguments: args,
            environment: env,
            continuation: cont,
        })
    }

    pub fn done(val: Scheme) -> Task {
        Task(TaskEnum::Done(val))
    }

    pub fn complete(self) -> Result<Scheme, Error> {
        let mut cur_task = self;
        loop {
            match cur_task.step()? {
                Left(next_task) => cur_task = next_task,
                Right(result) => return Ok(result),
            }
        }
    }

    pub fn step(self) -> Result<Either<Task, Scheme>, Error> {
        match self.0 {
            TaskEnum::Eval {expression: expr, environment: env, continuation:
                cont} => {

                if let Some(s) = expr.as_symbol() {
                    if let Some(res) = env.lookup(&s) {
                        Ok(Left(cont.pass_value(res.clone())))
                    } else {
                        Err(Error)
                    }
                } else if let Some((operator, operands_linked)) =
                        expr.0.as_pair() {
                    if let Some(x) = operator.as_symbol() {
                        if let Some(Binding::Syntax(form)) =
                            env.lookup_binding(x) {
                            let operands =
                                operands_linked.into_vec()?
                                               .into_iter()
                                               .map(|val| Expression(val))
                                               .collect();
                            return Ok(Left(form(operands, env.clone(), cont)?));
                        }
                    }
                    // Procedure call
                    let operands = operands_linked.into_vec()?;
                    let expressions: Vec<_> = operands.into_iter().rev()
                            .map(|val| Expression(val)).collect();
                    let new_continuation = Continuation::from_data(
                        ContinuationData::Application {
                            values: Vec::new(),
                            expressions: expressions,
                            environment: env.clone(),
                            next_continuation: cont,
                        });
                    Ok(Left(Task::eval(Expression(operator.clone()), env,
                        new_continuation)))
                } else if expr.0.is_literal() {
                    Ok(Left(cont.pass_value(expr.0.clone())))
                } else {
                    Err(Error)
                }
            },
            TaskEnum::Apply {procedure, arguments, environment, continuation} =>
            {
                if let Some(procc) = procedure.as_procedure() {
                    Ok(Left(procc.apply(arguments, environment,
                        continuation)?))
                } else {
                    Err(Error)
                }
            }
            TaskEnum::Done(val) => Ok(Right(val)),
        }
    }
}

impl Scheme {
    pub fn eval(&self, env: &Environment) -> Result<Scheme, Error> {
        let continuation = Continuation::default();
        let task = Task::eval(Expression(self.clone()), env.clone(),
            continuation);
        task.complete()
    }

    fn apply(&self, args: Vec<Scheme>, env: &Environment) -> Result<Scheme,
        Error> {

        if let Some(procc) = self.as_procedure() {
            procc.apply(args, env.clone(), Continuation::default())?.complete()
        } else {
            Err(Error)
        }
    }
}

impl Procedure {
    pub fn builtin(bltin: Builtin) -> Procedure {
        Procedure(ProcEnum::Builtin(bltin))
    }

    fn lambda(lam: Lambda) -> Procedure {
        Procedure(ProcEnum::Lambda(lam))
    }

    fn apply(self, args: Vec<Scheme>, env: Environment, ctx: Continuation) ->
        Result<Task, Error> {

        match self.0 {
            ProcEnum::Builtin(builtin) => {
                let res = builtin(args, env)?;
                Ok(ctx.pass_value(res))
            },
            ProcEnum::Lambda(lamb) => {
                let new_env = lamb.environment.make_child();
                lamb.binder.match_with_args(args, &new_env)?;
                Ok(Task::eval(lamb.body, new_env, ctx))
            },
        }
    }
}

impl Expression {
    pub fn is_literal(&self) -> bool {
        self.0.is_literal()
    }

    pub fn as_symbol(&self) -> Option<&str> {
        self.0.as_symbol()
    }

    pub fn as_pair(&self) -> Option<(Expression, Expression)> {
        self.0.as_pair().map(|(a, b)|
            (Expression(a.clone()), Expression(b.clone())))
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

    // pub?
    pub fn insert(&self, variable: &str, val: Scheme) {
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

pub fn lambda(operands: Vec<Expression>, env: Environment, c: Continuation) ->
    Result<Task, Error> {

    let operands_linked = Scheme::list(operands.into_iter().map(|expr| expr.0));
    let (formals, body) = operands_linked.as_pair().ok_or(Error)?;
    //let binder = formals.as_symbol().ok_or(Error)?;
    let (expr, null) = body.as_pair().ok_or(Error)?;
    if !null.is_null() {
        return Err(Error);
    }
    let procc = Procedure::lambda(Lambda {
        binder: Formals::from_object(formals.clone())?,
        body: Expression(expr.clone()),
        environment: env.clone(),
    });
    Ok(c.pass_value(Scheme::procedure(procc)))
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
