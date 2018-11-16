
use std::collections::HashMap;

use either::{Either, Left, Right};
use gc::{Gc, GcCell};

use scheme::{Error, Scheme, SchemeMut};

/// Wrapper type for unevaluated Scheme expressions.
#[derive(Clone, Debug, Finalize, PartialEq, Trace)]
pub struct Expression(pub Scheme);

// Clone-by-reference environment
#[derive(Clone, Debug, Finalize, PartialEq, Trace)]
pub struct Environment(Gc<GcCell<EnvironmentData>>);

/*
// TEMP: Make Environment in Debug easier to read but less informative
impl fmt::Debug for Environment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<environment {:x}>", self.deref() as *const _ as usize)
    }
}
*/

#[derive(Clone, Debug, Finalize, PartialEq, Trace)]
pub struct EnvironmentData {
    parent: Option<Environment>,
    local: HashMap<String, Binding>,
}

// TODO: Add a `None` option and remove extraneous Option in lookup type
// pub?
#[derive(Clone, Debug, Finalize, PartialEq, Trace)]
pub enum Binding {
    Variable(SchemeMut),
    Syntax(BuiltinSyntax),
}

// derive(PartialEq)?
#[derive(Debug, Clone, Finalize, PartialEq, Trace)]
pub struct Continuation(Gc<ContinuationData>);

// derive(PartialEq)?
#[derive(Debug, Finalize, PartialEq, Trace)]
enum ContinuationData {
    // Left-to-right evaluation order for now
    Application {
        values: Vec<Scheme>,
        expressions: Vec<Expression>,
        environment: Environment,
        next_continuation: Continuation,
    },
    IfThenElse {
        if_true: Expression,
        if_false: Expression,
        environment: Environment,
        next_continuation: Continuation,
    },
    End,
}

// derive(PartialEq)?
#[derive(Clone, Debug, PartialEq)]
pub struct Task(TaskEnum);

// derive(PartialEq)?
// derive(Finalize, Trace)?
#[derive(Clone, Debug, PartialEq)]
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

#[derive(Clone, Debug, Finalize, PartialEq, Trace)]
pub struct Procedure(ProcEnum);

#[derive(Clone, Debug, Finalize, PartialEq, Trace)]
enum ProcEnum {
    Builtin(Builtin), // Deprecate this?
    SimpleBuiltin(SimpleBuiltin),
    Lambda(Lambda),
    Continuation(Continuation),
    // A procedure that takes one argument and sets a variable to equal that
    // argument. Used to implement "set!".
    Set(String),
}

pub type Builtin = fn(Vec<Scheme>, Environment, Continuation) -> Result<Task,
    Error>;

pub type SimpleBuiltin = fn(Vec<Scheme>) -> Result<Scheme, Error>;

pub type BuiltinSyntax = fn(Vec<Expression>, Environment, Continuation) ->
    Result<Task, Error>;

// pub?
#[derive(Debug, Clone, Finalize, PartialEq, Trace)]
pub struct Lambda {
    binder: Formals,
    body: Expression,
    environment: Environment,
}

#[derive(Debug, Clone, Finalize, PartialEq, Trace)]
struct Formals {
    head_vars: Vec<String>,
    tail_var: Option<String>,
}

impl Continuation {
    fn from_data(data: ContinuationData) -> Continuation {
        Continuation(Gc::new(data))
    }

    pub fn if_then_else(if_true: Expression, if_false: Expression, environment:
        Environment, next_continuation: Continuation) -> Continuation {

        Continuation::from_data(ContinuationData::IfThenElse {
            if_true, if_false, environment, next_continuation
        })
    }

    pub fn pass_value(&self, value: Scheme) -> Task {
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
            ContinuationData::IfThenElse {ref if_true, ref if_false, ref
                environment, ref next_continuation} => {
                
                if value.truey() {
                    Task::eval(if_true.clone(), environment.clone(),
                        next_continuation.clone())
                } else {
                    Task::eval(if_false.clone(), environment.clone(),
                        next_continuation.clone())
                }
            }
            ContinuationData::End => Task::done(value),
        }
    }

    /// A continuation that takes a value, sets `variable` to this value in
    /// `environment`, and then passes an unspecified value to
    /// `next_continuation`. Used to implement set!.
    pub(crate) fn set(variable: String, environment: Environment, next_continuation:
        Continuation) -> Continuation {

        let set_proc = Scheme::procedure(Procedure::set(variable));
        Continuation::from_data(ContinuationData::Application {
            values: vec![set_proc],
            expressions: Vec::new(),
            environment: environment,
            next_continuation: next_continuation,
        })
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
        // TODO: When Task/TaskEnum lose Finalize/Trace support, return to a
        // pass-by-value implementation of below (remove will-be extraneous
        // "ref" in patterns).
        match self.0 {
            TaskEnum::Eval {expression: ref expr, environment: ref env,
                continuation: ref cont} => {

                if let Some(s) = expr.as_symbol() {
                    if let Some(res) = env.lookup(&s) {
                        Ok(Left(cont.pass_value(res.into())))
                    } else {
                        Err(Error)
                    }
                } else if let Some((operator, operands_linked)) =
                        expr.as_pair() {
                    if let Some(symb) = operator.as_symbol() {
                        if let Some(Binding::Syntax(form)) =
                            env.lookup_binding(symb) {
                            let operands =
                                operands_linked.0.into_vec()?
                                               .into_iter()
                                               .map(|val| Expression(val))
                                               .collect();
                            return Ok(Left(form(operands, env.clone(),
                                cont.clone())?));
                        }
                    }
                    // Procedure call
                    let operands = operands_linked.0.into_vec()?;
                    let expressions: Vec<_> = operands.into_iter().rev()
                            .map(|val| Expression(val)).collect();
                    let new_continuation = Continuation::from_data(
                        ContinuationData::Application {
                            values: Vec::new(),
                            expressions: expressions,
                            environment: env.clone(),
                            next_continuation: cont.clone(),
                        });
                    Ok(Left(Task::eval(operator.clone(), env.clone(),
                        new_continuation)))
                } else if expr.is_literal() {
                    Ok(Left(cont.pass_value(expr.0.clone())))
                } else {
                    Err(Error)
                }
            },
            TaskEnum::Apply {ref procedure, ref arguments, ref environment, ref
                continuation} =>
            {
                if let Some(procc) = procedure.as_procedure() {
                    // NOTE: Cloning `arguments` is expensive and only necessary
                    // to satisfy the typechecker.
                    Ok(Left(procc.apply(arguments.clone(), environment.clone(),
                        continuation.clone())?))
                } else {
                    Err(Error)
                }
            }
            TaskEnum::Done(ref val) => Ok(Right(val.clone())),
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
}

impl Procedure {
    pub fn builtin(bltin: Builtin) -> Procedure {
        Procedure(ProcEnum::Builtin(bltin))
    }

    pub fn simple_builtin(builtin: SimpleBuiltin) -> Procedure {
        Procedure(ProcEnum::SimpleBuiltin(builtin))
    }

    fn lambda(lam: Lambda) -> Procedure {
        Procedure(ProcEnum::Lambda(lam))
    }

    pub fn continuation(cont: Continuation) -> Procedure {
        Procedure(ProcEnum::Continuation(cont))
    }

    pub(crate) fn set(var: String) -> Procedure {
        Procedure(ProcEnum::Set(var))
    }

    fn apply(self, args: Vec<Scheme>, env: Environment, ctx: Continuation) ->
        Result<Task, Error> {

        match self.0 {
            ProcEnum::Builtin(builtin) => {
                builtin(args, env, ctx)
            },
            ProcEnum::SimpleBuiltin(builtin) => {
                Ok(ctx.pass_value(builtin(args)?))
            },
            ProcEnum::Lambda(ref lamb) => {
                let new_env = lamb.environment.make_child();
                lamb.binder.match_with_args(args, &new_env)?;
                Ok(Task::eval(lamb.body.clone(), new_env, ctx))
            },
            ProcEnum::Continuation(ref cont) => {
                if args.len() == 1 {
                    Ok(cont.pass_value(args[0].clone()))
                } else {
                    Err(Error)
                }
            },
            ProcEnum::Set(ref var) => {
                let loc = env.lookup(var).ok_or(Error)?;
                if args.len() == 1 {
                    loc.replace(args[0].clone());
                    Ok(ctx.pass_value(Scheme::unspecified()))
                } else {
                    Err(Error)
                }
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

impl Binding {
    pub fn variable(x: Scheme) -> Binding {
        Binding::Variable(SchemeMut::new(x))
    }
}

impl Environment {
    fn from_data(data: EnvironmentData) -> Environment {
        Environment(Gc::new(GcCell::new(data)))
    }

    // Rethink structure
    pub fn from_hashmap(hmap: HashMap<String, Binding>) -> Environment {
        Environment::from_data(EnvironmentData {
            parent: None,
            local: hmap,
        })
    }

    // TODO: Return SchemeMut
    fn lookup(&self, variable: &str) -> Option<SchemeMut> {
        match self.lookup_binding(variable) {
            Some(Binding::Variable(ref val)) => Some(val.clone()),
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
            Binding::Variable(SchemeMut::new(val)));
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

    let operands_linked = Scheme::list(operands.into_iter().map(|expr|
        expr.0.clone()));
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
