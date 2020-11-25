
mod builtin;
mod number;
mod port;
mod read;
mod runtime;
mod scheme;

fn main() {
    let mut input_buffer = String::new();
    std::io::stdin().read_line(&mut input_buffer).expect("IO error reading \
        input");
    let in_expr = read::read(&input_buffer).expect("Invalid expression");
    let out_expr = in_expr.eval(&builtin::initial_environment());
    println!("{}", out_expr.expect("Scheme expression returns error"));
}
