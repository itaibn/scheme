
#[macro_use]
extern crate lazy_static;
extern crate regex;

mod read;
mod scheme;

fn main() {
    let mut input_buffer = String::new();
    std::io::stdin().read_line(&mut input_buffer).expect("IO error reading \
        input");
    println!("{:?}", read::Reader::new(&input_buffer).read_expr().expect(
        "Invalid expression"));
}
