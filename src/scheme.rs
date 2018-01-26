
#[derive(Debug)]
pub enum Scheme {
    Symbol(String),
    Nil,
    Cons(Box<Scheme>, Box<Scheme>),
}
