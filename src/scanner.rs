use std::{process, str::Chars};

pub struct Scanner<'a> {
    chars: Chars<'a>,
    text: &'a str,
    // current position in the text
    current: usize,
    // start of current token
    start: usize,
    // current line
    line: usize,
}

const EOF: char = '\0';

impl<'a> Scanner<'a> {
    pub fn new(input: &'a str) -> Scanner<'a> {
        Scanner {
            chars: input.chars(),
            text: input,
            current: 0,
            start: 0,
            line: 1,
        }
    }

    fn advance(&mut self) -> char {
        self.current += 1;
        let c = self.chars.next().unwrap_or(EOF);
        if !c.is_ascii() {
            eprintln!("Can't process non ascii character '{c}'");
            process::exit(1);
        }
        c
    }

    fn peek(&self) -> char {
        self.chars.clone().next().unwrap_or(EOF)
    }

    fn peek_next(&self) -> char {
        let mut iter = self.chars.clone();
        iter.next();
        iter.next().unwrap_or(EOF)
    }

    fn make_token(&self, ty: TokenType) -> Token {
        Token {
            ty,
            start: self.start,
            length: self.current - self.start,
            line: self.line,
        }
    }

    fn make_error(&self, message: &'static str) -> LexicalError {
        LexicalError {
            message,
            line: self.line,
            start: self.start,
            len: self.current - self.start,
        }
    }

    fn skip_whitespace(&mut self) {
        loop {
            let c = self.peek();
            match c {
                ' ' | '\t' | '\r' => {
                    self.advance();
                }
                '\n' => {
                    self.advance();
                    self.line += 1;
                }
                '/' => {
                    if self.peek_next() == '/' {
                        loop {
                            match self.peek() {
                                '\n' | EOF => break,
                                _ => {
                                    self.advance();
                                }
                            }
                        }
                    } else {
                        return;
                    }
                }
                _ => return,
            }
        }
    }

    fn is_alpha(&self, c: char) -> bool {
        matches!(c, 'a'..='z' | 'A'..='Z')
    }

    fn is_digit(&self, c: char) -> bool {
        matches!(c, '0'..='9')
    }

    fn is_alnum(&self, c: char) -> bool {
        self.is_digit(c) || self.is_alpha(c) || c == '_'
    }

    fn check_keyword(
        &self,
        suffix: &'static str,
        chars: impl Iterator<Item = char> + std::fmt::Debug,
        ty: TokenType,
    ) -> TokenType {
        let suffix = suffix.chars();
        if chars.eq(suffix) {
            ty
        } else {
            TokenType::Identifier
        }
    }

    /*and, array, bool, char, else, false, for, fn, if,
     int, not, or, print, return, string, true, void, while,
    */

    fn identifier_type(&self) -> TokenType {
        let mut chars = self.text[self.start..self.current].chars();
        match chars.next().unwrap() {
            'a' => {
                if self.current - self.start > 1 {
                    match chars.next().unwrap() {
                        'r' => self.check_keyword("ray", chars, TokenType::TyArray),
                        'n' => self.check_keyword("d", chars, TokenType::And),
                        _ => TokenType::Identifier,
                    }
                } else {
                    TokenType::Identifier
                }
            }
            'b' => self.check_keyword("ool", chars, TokenType::TyBool),
            'c' => self.check_keyword("har", chars, TokenType::TyChar),
            'e' => self.check_keyword("lse", chars, TokenType::Else),
            'f' => {
                if self.current - self.start > 1 {
                    match chars.next().unwrap() {
                        'o' => self.check_keyword("r", chars, TokenType::For),
                        'a' => self.check_keyword("lse", chars, TokenType::False),
                        'n' => TokenType::Fun,
                        _ => TokenType::Identifier,
                    }
                } else {
                    TokenType::Identifier
                }
            }
            'i' => {
                if self.current - self.start > 1 {
                    match chars.next().unwrap() {
                        'f' => TokenType::If,
                        'n' => self.check_keyword("t", chars, TokenType::TyInt),
                        _ => TokenType::Identifier,
                    }
                } else {
                    TokenType::Identifier
                }
            }
            'n' => self.check_keyword("ot", chars, TokenType::Not),
            'o' => self.check_keyword("r", chars, TokenType::Or),
            'p' => self.check_keyword("rint", chars, TokenType::Print),
            'r' => self.check_keyword("eturn", chars, TokenType::Return),
            's' => self.check_keyword("tring", chars, TokenType::TyString),
            't' => self.check_keyword("rue", chars, TokenType::True),
            'v' => {
                if self.current - self.start > 1 {
                    match chars.next().unwrap() {
                        'a' => self.check_keyword("r", chars, TokenType::Var),
                        'o' => self.check_keyword("id", chars, TokenType::TyVoid),
                        _ => TokenType::Identifier,
                    }
                } else {
                    TokenType::Identifier
                }
            }
            'w' => self.check_keyword("hile", chars, TokenType::While),
            _ => TokenType::Identifier,
        }
    }

    fn identifier(&mut self) -> Token {
        while self.is_alnum(self.peek()) {
            self.advance();
        }

        self.make_token(self.identifier_type())
    }

    fn number(&mut self) -> Result<Token, LexicalError> {
        while self.is_digit(self.peek()) {
            self.advance();
        }

        if self.is_alpha(self.peek()) {
            return Err(self.make_error("Number literal followed by a letter"));
        }

        Ok(self.make_token(TokenType::NumberLit))
    }

    fn string(&mut self) -> Result<Token, LexicalError> {
        loop {
            match self.peek() {
                '"' => break,
                EOF => return Err(self.make_error("Unterminated string")),
                '\n' => {
                    self.line += 1;
                    self.advance();
                }
                _ => {
                    self.advance();
                }
            }
        }

        self.eat('"');

        Ok(self.make_token(TokenType::StringLit))
    }

    fn eat(&mut self, c: char) -> bool {
        match self.peek() {
            c_ if c_ == c => {
                self.advance();
                true
            }
            _ => false,
        }
    }

    fn eat_two_char(&mut self, c: char, t1: TokenType, t2: TokenType) -> Token {
        if self.eat(c) {
            self.make_token(t2)
        } else {
            self.make_token(t1)
        }
    }

    pub fn scan_token(&mut self) -> Result<Token, LexicalError> {
        self.skip_whitespace();
        self.start = self.current;

        let c = self.advance();

        if self.is_alpha(c) {
            return Ok(self.identifier());
        }

        if self.is_digit(c) {
            return self.number();
        }

        if c == '"' {
            return self.string();
        }

        match c {
            EOF => Ok(self.make_token(TokenType::Eof)),
            '+' => Ok(self.make_token(TokenType::Plus)),
            '*' => Ok(self.make_token(TokenType::Star)),
            '/' => Ok(self.make_token(TokenType::Slash)),
            ';' => Ok(self.make_token(TokenType::Semicolon)),
            ':' => Ok(self.make_token(TokenType::Colon)),
            ',' => Ok(self.make_token(TokenType::Comma)),
            '^' => Ok(self.make_token(TokenType::Hat)),
            '{' => Ok(self.make_token(TokenType::LBrace)),
            '}' => Ok(self.make_token(TokenType::RBrace)),
            '(' => Ok(self.make_token(TokenType::LParen)),
            ')' => Ok(self.make_token(TokenType::RParen)),
            '[' => Ok(self.make_token(TokenType::LBracket)),
            ']' => Ok(self.make_token(TokenType::RBracket)),
            '-' => Ok(self.eat_two_char('>', TokenType::Minus, TokenType::RArrow)),
            '=' => Ok(self.eat_two_char('=', TokenType::Equal, TokenType::EqualEqual)),
            '>' => Ok(self.eat_two_char('=', TokenType::Greater, TokenType::GreaterEqual)),
            '<' => Ok(self.eat_two_char('=', TokenType::Less, TokenType::LessEqual)),
            '!' => Ok(self.eat_two_char('=', TokenType::Bang, TokenType::BangEqual)),
            _ => Err(self.make_error("Unexpected character")),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct LexicalError {
    pub message: &'static str,
    // location in text
    pub line: usize,
    pub start: usize,
    pub len: usize,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Token {
    pub ty: TokenType,
    pub start: usize,
    pub length: usize,
    pub line: usize,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum TokenType {
    And,
    Bang,
    BangEqual,
    Colon,
    Comma,
    Else,
    Eof,
    Equal,
    EqualEqual,
    False,
    For,
    Fun,
    Greater,
    GreaterEqual,
    Hat,
    Identifier,
    If,
    LBrace,
    LBracket,
    LParen,
    Less,
    LessEqual,
    Minus,
    Not,
    NumberLit,
    Or,
    Plus,
    Print,
    RArrow,
    RBrace,
    RBracket,
    RParen,
    Return,
    Semicolon,
    Slash,
    Star,
    StringLit,
    True,
    TyArray,
    TyBool,
    TyChar,
    TyInt,
    TyString,
    TyVoid,
    Var,
    While,
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_identifier() {
        let mut scanner = Scanner::new("the_999iDENT");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::Identifier,);
    }

    #[test]
    fn test_incorrect_identifier() {
        let mut scanner = Scanner::new("9incorrect");
        assert_eq!(
            scanner.scan_token(),
            Err(LexicalError {
                message: "Number literal followed by a letter",
                line: 1,
                start: 0,
                len: 1
            })
        );
    }

    #[test]
    fn test_string() {
        let mut scanner = Scanner::new("\"Hello\"");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::StringLit);
    }

    #[test]
    fn test_unterminated_string() {
        let mut scanner = Scanner::new("\"Hello");
        assert_eq!(
            scanner.scan_token(),
            Err(LexicalError {
                message: "Unterminated string",
                line: 1,
                start: 0,
                len: 6
            })
        )
    }

    #[test]
    fn test_number() {
        let mut scanner = Scanner::new("0000232813000");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::NumberLit);
    }

    #[test]
    fn test_equal_equal() {
        let mut scanner = Scanner::new("== =");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::EqualEqual);
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::Equal);
    }

    #[test]
    fn test_greater_equal() {
        let mut scanner = Scanner::new(">= >");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::GreaterEqual);
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::Greater);
    }

    #[test]
    fn test_less_equal() {
        let mut scanner = Scanner::new("<= <");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::LessEqual);
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::Less);
    }

    #[test]
    fn test_bang_equal() {
        let mut scanner = Scanner::new("!= !");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::BangEqual);
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::Bang);
    }

    /*and, array, bool, char, else, false, for, fn, if,
     int, or, print, return, string, true, void, while,
    */
    #[test]
    fn test_and() {
        let mut scanner = Scanner::new("and");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::And);
    }

    #[test]
    fn test_array() {
        let mut scanner = Scanner::new("array");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::TyArray);
    }

    #[test]
    fn test_bool() {
        let mut scanner = Scanner::new("bool");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::TyBool);
    }

    #[test]
    fn test_char() {
        let mut scanner = Scanner::new("char");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::TyChar);
    }

    #[test]
    fn test_else() {
        let mut scanner = Scanner::new("else");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::Else);
    }

    #[test]
    fn test_false() {
        let mut scanner = Scanner::new("false");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::False);
    }

    #[test]
    fn test_for() {
        let mut scanner = Scanner::new("for");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::For);
    }

    #[test]
    fn test_fn() {
        let mut scanner = Scanner::new("fn");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::Fun);
    }

    #[test]
    fn test_if() {
        let mut scanner = Scanner::new("if");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::If);
    }

    #[test]
    fn test_int() {
        let mut scanner = Scanner::new("int");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::TyInt);
    }

    #[test]
    fn test_not() {
        let mut scanner = Scanner::new("not");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::Not);
    }

    #[test]
    fn test_or() {
        let mut scanner = Scanner::new("or");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::Or);
    }

    #[test]
    fn test_print() {
        let mut scanner = Scanner::new("print");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::Print);
    }

    #[test]
    fn test_return() {
        let mut scanner = Scanner::new("return");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::Return);
    }

    #[test]
    fn test_string_type() {
        let mut scanner = Scanner::new("string");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::TyString);
    }

    #[test]
    fn test_true() {
        let mut scanner = Scanner::new("true");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::True);
    }

    #[test]
    fn test_void() {
        let mut scanner = Scanner::new("void");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::TyVoid);
    }

    #[test]
    fn test_while() {
        let mut scanner = Scanner::new("while");
        assert_eq!(scanner.scan_token().unwrap().ty, TokenType::While);
    }
}
