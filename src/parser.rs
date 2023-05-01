use crate::ast::{BinOp, Expr, ExprKind, UnOp};
use crate::scanner::{Scanner, Token, TokenType};

pub struct Parser<'a> {
    src: &'a str,
    scanner: Scanner<'a>,
    current: Option<Token>,
    prev: Option<Token>,
    had_error: bool,
}

enum Precedence {
    None = -100,
    Term = 10,
    Factor = 11,
    Unary = 30,
}

impl<'a> Parser<'a> {
    pub fn new(src: &'a str) -> Parser {
        let scanner = Scanner::new(src);
        Parser {
            src,
            scanner,
            current: None,
            prev: None,
            had_error: false,
        }
    }

    fn advance(&mut self) {
        self.prev = self.current.take();
        let mut t = self.scanner.scan_token();
        loop {
            match t {
                Ok(t) => {
                    self.current = Some(t);
                    break;
                }
                Err(e) => {
                    eprintln!("Lexical error: {} at line {}", e.message, e.line);
                    self.had_error = true;
                    t = self.scanner.scan_token();
                }
            }
        }
    }

    fn consume(&mut self, token_ty: TokenType, msg: &'static str) {
        if self.current.as_ref().unwrap().ty == token_ty {
            self.advance();
            return;
        }

        self.error_at_current(msg);
    }

    fn error_at_current(&self, msg: &'static str) {
        self.error_at(self.current.as_ref().unwrap(), msg);
    }

    fn error_at(&self, token: &Token, msg: &'static str) {
        eprintln!("Syntax error: {}, at line {}", msg, token.line);
    }

    fn number(&mut self) -> Expr {
        let token = self.prev.as_ref().unwrap();
        let text = &self.src[token.start..token.start + token.length];
        let num: i64 = text.parse().unwrap();
        Expr {
            kind: ExprKind::IntegerLit(num),
        }
    }

    fn string(&mut self) -> Expr {
        let token = self.prev.as_ref().unwrap();
        let text = &self.src[token.start + 1..token.start + token.length - 1];
        Expr {
            kind: ExprKind::StringLit(text.to_string()),
        }
    }

    fn grouping(&mut self) -> Expr {
        let expr = self.expression();
        self.consume(TokenType::RParen, "Unclosed grouping");
        expr
    }

    fn unary(&mut self) -> Expr {
        let op = self.prev.as_ref().unwrap().ty;
        let op = match op {
            TokenType::Minus => UnOp::Neg,
            TokenType::Bang => UnOp::Not,
            _ => panic!(),
        };
        let expr = self.parse_precedence(Precedence::Unary as i32);
        Expr {
            kind: ExprKind::Unary(op, Box::new(expr)),
        }
    }

    fn bool_literal(&mut self) -> Expr {
        let val = self.prev.as_ref().unwrap().ty;
        let val = match val {
            TokenType::True => true,
            TokenType::False => false,
            _ => panic!(),
        };
        Expr {
            kind: ExprKind::BoolLit(val),
        }
    }

    fn binary(&mut self, lhs: Expr) -> Expr {
        let op = self.prev.as_ref().unwrap().ty;
        let op = self.get_bin_op(op).unwrap();
        let rhs = self.parse_precedence(self.precedence(op) as i32 + 1);
        Expr {
            kind: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)),
        }
    }

    fn get_bin_op(&self, token_ty: TokenType) -> Option<BinOp> {
        match token_ty {
            TokenType::Plus => Some(BinOp::Add),
            TokenType::Minus => Some(BinOp::Sub),
            TokenType::Slash => Some(BinOp::Div),
            TokenType::Star => Some(BinOp::Mul),
            _ => None,
        }
    }

    fn precedence(&self, op: BinOp) -> Precedence {
        match op {
            BinOp::Add | BinOp::Sub => Precedence::Term,
            BinOp::Div | BinOp::Mul => Precedence::Factor,
        }
    }

    fn get_current_precedence(&self) -> Precedence {
        let token_ty = self.current.as_ref().unwrap().ty;

        if let Some(op) = self.get_bin_op(token_ty) {
            self.precedence(op)
        } else {
            Precedence::None
        }
    }

    fn get_prefix_rule(&self, token_ty: TokenType) -> fn(&mut Self) -> Expr {
        match token_ty {
            TokenType::NumberLit => Self::number,
            TokenType::StringLit => Self::string,
            TokenType::LParen => Self::grouping,
            TokenType::Minus => Self::unary,
            TokenType::False | TokenType::True => Self::bool_literal,
            _ => panic!(),
        }
    }


    #[rustfmt::skip]
    fn get_infix_rule(&self, token_ty: TokenType) -> fn(&mut Self, Expr) -> Expr {
        match token_ty {
            TokenType::Plus
            | TokenType::Minus
            | TokenType::Slash
            | TokenType::Star => Self::binary,
            _ => panic!(),
        }
    }

    fn expression(&mut self) -> Expr {
        self.parse_precedence(Precedence::Term as i32)
    }

    fn parse_precedence(&mut self, precedence: i32) -> Expr {
        self.advance();
        let prefix_rule = self.get_prefix_rule(self.prev.as_ref().unwrap().ty);

        let mut expr = prefix_rule(self);

        while precedence <= self.get_current_precedence() as i32 {
            self.advance();
            let infix_rule = self.get_infix_rule(self.prev.as_ref().unwrap().ty);
            expr = infix_rule(self, expr);
        }
        expr
    }

    pub fn parse(&mut self) -> Expr {
        self.advance();
        let expr = self.expression();
        self.consume(TokenType::Eof, "Expected end of expression.");
        expr
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn literal(val: i64) -> Expr {
        Expr {
            kind: ExprKind::IntegerLit(val),
        }
    }

    fn binary(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
        Expr {
            kind: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)),
        }
    }

    fn unary(op: UnOp, val: Expr) -> Expr {
        Expr {
            kind: ExprKind::Unary(op, Box::new(val)),
        }
    }

    #[test]
    fn test_addition() {
        let expr = Parser::new("2 + 3").parse();
        assert_eq!(expr, binary(BinOp::Add, literal(2), literal(3)))
    }

    #[test]
    fn test_subtraction() {
        let expr = Parser::new("2 - 3").parse();
        assert_eq!(expr, binary(BinOp::Sub, literal(2), literal(3)))
    }

    #[test]
    fn test_multiplication() {
        let expr = Parser::new("2 * 3").parse();
        assert_eq!(expr, binary(BinOp::Mul, literal(2), literal(3)))
    }

    #[test]
    fn test_division() {
        let expr = Parser::new("2 / 3").parse();
        assert_eq!(expr, binary(BinOp::Div, literal(2), literal(3)))
    }

    #[test]
    fn test_grouping() {
        let expr = Parser::new("(2 + 3) * 4").parse();
        assert_eq!(
            expr,
            binary(
                BinOp::Mul,
                binary(BinOp::Add, literal(2), literal(3)),
                literal(4),
            )
        )
    }

    #[test]
    fn test_raising_precedence() {
        let expr = Parser::new("2 + 3 * -4").parse();
        assert_eq!(
            expr,
            binary(
                BinOp::Add,
                literal(2),
                binary(BinOp::Mul, literal(3), unary(UnOp::Neg, literal(4)))
            )
        )
    }

    #[test]
    fn test_descending_precedence() {
        let expr = Parser::new("-4 * 3 + 2").parse();
        assert_eq!(
            expr,
            binary(
                BinOp::Add,
                binary(BinOp::Mul, unary(UnOp::Neg, literal(4)), literal(3)),
                literal(2),
            )
        )
    }
}
