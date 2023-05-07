use b_locrian::parser::Parser;
use b_locrian::pretty_print::AstPrinter;
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    if let Ok(src) = fs::read_to_string(&args[1]) {
        let mut parser = Parser::new(&src);
        let tree = parser.parse();
        AstPrinter::new(&tree).print_tree();
    } else {
        println!("No such file {}", args[1]);
    };
}
