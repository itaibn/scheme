
#[macro_use]
extern crate lazy_static;
extern crate regex;

mod read;

#[derive(Debug)]
pub enum Scheme {
    Symbol(String),
    Nil,
    Cons(Box<Scheme>, Box<Scheme>),
}

fn main() {
    let mut input_buffer = String::new();
    std::io::stdin().read_line(&mut input_buffer).expect("IO error reading \
        input");
    println!("{:?}", read::Reader::new(&input_buffer).read_expr().expect(
        "Invalid expression"));
}
