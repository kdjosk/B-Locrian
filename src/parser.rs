use crate::ast::{BinOp, Decl, DeclKind, Expr, ExprKind, Ty, TyKind, UnOp, VarDecl};
use crate::scanner::{Scanner, Token, TokenType};

pub struct Parser<'a> {
    src: &'a str,
    scanner: Scanner<'a>,
    current: Token,
    prev: Token,
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
        let before_start_token = Token {
            ty: TokenType::Eof,
            start: 0,
            length: 0,
            line: 0,
        };

        Parser {
            src,
            scanner,
            current: before_start_token.clone(),
            prev: before_start_token.clone(),
            had_error: false,
        }
    }

    fn advance(&mut self) {
        self.prev = self.current;
        let mut t = self.scanner.scan_token();
        loop {
            match t {
                Ok(t) => {
                    self.current = t;
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
        if self.current.ty == token_ty {
            self.advance();
            return;
        }

        self.error_at_current(msg);
    }

    fn error_at_current(&self, msg: &'static str) {
        self.error_at(&self.current, msg);
    }

    fn error_at(&self, token: &Token, msg: &'static str) {
        eprintln!("Syntax error: {}, at line {}", msg, token.line);
    }

    fn number(&mut self) -> Expr {
        let token = &self.prev;
        let text = &self.src[token.start..token.start + token.length];
        let num: i64 = text.parse().unwrap();
        Expr {
            kind: ExprKind::IntegerLit(num),
        }
    }

    fn string(&mut self) -> Expr {
        let token = self.prev;
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
        let op = self.prev.ty;
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
        let val = self.prev.ty;
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
        let op = self.prev.ty;
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
        let token_ty = self.current.ty;

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
            t => panic!("Expression can't begin with {:?}", t),
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
        let prefix_rule = self.get_prefix_rule(self.prev.ty);

        let mut expr = prefix_rule(self);

        while precedence <= self.get_current_precedence() as i32 {
            self.advance();
            let infix_rule = self.get_infix_rule(self.prev.ty);
            expr = infix_rule(self, expr);
        }
        expr
    }

    /// arg (, arg)*
    fn parse_argtypes(&mut self) -> Vec<Box<Ty>> {
        // parse type list
        let mut argtypes = Vec::new();
        argtypes.push(Box::new(self.type_expr()));
        while self.current.ty == TokenType::Comma {
            self.advance();
            self.type_expr();
        }
        argtypes
    }

    fn type_expr(&mut self) -> Ty {
        self.advance();
        match self.prev.ty {
            // arr [10] int
            TokenType::TyArray => {
                self.consume(TokenType::LBracket, "");
                let length = self.expression();
                self.consume(TokenType::RBracket, "");
                let ty = self.type_expr();
                Ty {
                    kind: TyKind::Array {
                        len: length,
                        ty: Box::new(ty),
                    },
                }
            }
            // fn (int, char) -> string
            TokenType::Fun => {
                self.consume(TokenType::LParen, "");
                let mut argtypes = None;
                if self.current.ty != TokenType::RParen {
                    argtypes = Some(self.parse_argtypes());
                }
                self.consume(TokenType::RParen, "");
                self.consume(TokenType::RArrow, "");
                let ret_ty = self.type_expr();
                Ty {
                    kind: TyKind::Function {
                        ret_type: Box::new(ret_ty),
                        args: argtypes,
                    },
                }
            }
            TokenType::TyBool => Ty { kind: TyKind::Bool },
            TokenType::TyInt => Ty {
                kind: TyKind::Int64,
            },
            TokenType::TyChar => Ty { kind: TyKind::Char },
            TokenType::TyString => Ty {
                kind: TyKind::String,
            },
            TokenType::TyVoid => Ty { kind: TyKind::Void },
            _ => panic!(),
        }
    }

    /// var ident: ty (= expr)?;
    fn var_decl(&mut self) -> Decl {
        self.consume(TokenType::Var, "");
        self.consume(TokenType::Identifier, "");
        let name = &self.prev;
        let name = &self.src[name.start..name.start + name.length];
        self.consume(TokenType::Colon, "");

        let ty = self.type_expr();

        let mut val = None;
        if self.current.ty == TokenType::Equal {
            self.advance();
            val = Some(self.expression());
        }
        self.consume(TokenType::Semicolon, "");

        Decl {
            kind: DeclKind::VarDecl(VarDecl {
                name: name.to_string(),
                ty,
                val,
            }),
        }
    }

    fn declaration(&mut self) -> Decl {
        match self.current.ty {
            TokenType::Var => self.var_decl(),
            _ => panic!(),
        }
    }

    pub fn parse(&mut self) -> Vec<Decl> {
        self.advance();

        let mut program = Vec::new();
        while self.current.ty != TokenType::Eof {
            program.push(self.declaration());
        }

        program
    }

    /// for use in REPL and testing convenience
    pub fn parse_expression(&mut self) -> Expr {
        self.advance();
        let expr = self.expression();
        self.consume(TokenType::Eof, "Expected end of expression.");
        expr
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Decl, DeclKind, Ty, TyKind, VarDecl};

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
        let expr = Parser::new("2 + 3").parse_expression();
        assert_eq!(expr, binary(BinOp::Add, literal(2), literal(3)))
    }

    #[test]
    fn test_subtraction() {
        let expr = Parser::new("2 - 3").parse_expression();
        assert_eq!(expr, binary(BinOp::Sub, literal(2), literal(3)))
    }

    #[test]
    fn test_multiplication() {
        let expr = Parser::new("2 * 3").parse_expression();
        assert_eq!(expr, binary(BinOp::Mul, literal(2), literal(3)))
    }

    #[test]
    fn test_division() {
        let expr = Parser::new("2 / 3").parse_expression();
        assert_eq!(expr, binary(BinOp::Div, literal(2), literal(3)))
    }

    #[test]
    fn test_grouping() {
        let expr = Parser::new("(2 + 3) * 4").parse_expression();
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
        let expr = Parser::new("2 + 3 * -4").parse_expression();
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
        let expr = Parser::new("-4 * 3 + 2").parse_expression();
        assert_eq!(
            expr,
            binary(
                BinOp::Add,
                binary(BinOp::Mul, unary(UnOp::Neg, literal(4)), literal(3)),
                literal(2),
            )
        )
    }

    #[test]
    fn test_var_decl_with_init() {
        let decl = &Parser::new("var ident: int = 10;").parse()[0];
        assert_eq!(
            decl,
            &Decl {
                kind: DeclKind::VarDecl(VarDecl {
                    name: "ident".to_string(),
                    ty: Ty {
                        kind: TyKind::Int64
                    },
                    val: Some(literal(10))
                })
            }
        )
    }

    #[test]
    fn test_var_decl_no_init() {
        let decl = &Parser::new("var ident: int;").parse()[0];
        assert_eq!(
            decl,
            &Decl {
                kind: DeclKind::VarDecl(VarDecl {
                    name: "ident".to_string(),
                    ty: Ty {
                        kind: TyKind::Int64
                    },
                    val: None
                })
            }
        )
    }
}
