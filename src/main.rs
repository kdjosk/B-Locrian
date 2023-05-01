use b_locrian::parser::Parser;
use b_locrian::scanner::{Scanner, TokenType};
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    if let Ok(src) = fs::read_to_string(&args[1]) {
        println!("{}", src);
        let mut lex = Scanner::new(&src);
        loop {
            match lex.scan_token() {
                Ok(t) => {
                    println!("{:?}", t);
                    if t.ty == TokenType::Eof {
                        break;
                    }
                }
                Err(e) => {
                    println!("{:?}", e);
                    break;
                }
            }
        }

        let mut parser = Parser::new(&src);
        let tree = parser.parse();
        println!("{:#?}", tree);
    } else {
        println!("No such file {}", args[1]);
    };
}
