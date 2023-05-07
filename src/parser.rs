use crate::ast::{
    BinOp, Decl, DeclKind, Expr, ExprKind, FunDecl, Stmt, StmtKind, Ty, TyKind, UnOp, VarDecl,
};
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

    fn variable(&mut self) -> Expr {
        let ident = self.src[self.prev.start..self.prev.start + self.prev.length].to_string();
        Expr {
            kind: ExprKind::Var(ident),
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
            TokenType::Identifier => Self::variable,
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
    fn parse_argtypes(&mut self) -> Vec<Ty> {
        // parse type list
        let mut argtypes = Vec::new();
        argtypes.push(self.type_expr());
        while self.current.ty == TokenType::Comma {
            self.advance();
            argtypes.push(self.type_expr());
        }
        argtypes
    }

    fn type_expr(&mut self) -> Ty {
        self.advance();
        match self.prev.ty {
            // [10; int]
            TokenType::LBracket => {
                let length = self.expression();
                self.consume(
                    TokenType::Semicolon,
                    "Expected a ';' after array length expression",
                );
                let ty = self.type_expr();
                self.consume(
                    TokenType::RBracket,
                    "Missing closing ']' in array type declaration",
                );
                Ty {
                    kind: TyKind::Array {
                        len: length,
                        ty: Box::new(ty),
                    },
                }
            }
            // fn (int, char) -> string
            TokenType::Fun => {
                self.consume(TokenType::LParen, "Expected a '(' after 'fn' keyword");
                let mut argtypes = None;
                if self.current.ty != TokenType::RParen {
                    argtypes = Some(self.parse_argtypes());
                }
                self.consume(TokenType::RParen, "Expected a ')' after argument type list");
                self.consume(TokenType::RArrow, "Expecter a '->' after argument list");
                let ret_ty = self.type_expr();
                Ty {
                    kind: TyKind::Function {
                        ret_type: Box::new(ret_ty),
                        args: match argtypes {
                            None => None,
                            Some(argt) => Some(Box::new(argt)),
                        },
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
            t => panic!("Token {:?} does not name a type", t),
        }
    }

    /// var ident: ty (= expr)?;
    fn var_decl(&mut self) -> Decl {
        self.consume(
            TokenType::Var,
            "Variable declaration has to begin with 'var' keyword",
        );
        self.consume(
            TokenType::Identifier,
            "Missing identifier after 'var' keyword",
        );
        let name = &self.prev;
        let name = &self.src[name.start..name.start + name.length];
        self.consume(
            TokenType::Colon,
            "Expected a colon after an identifier in a variable declaration.",
        );

        let ty = self.type_expr();

        let mut val = None;
        if self.current.ty == TokenType::Equal {
            self.advance();
            val = Some(self.expression());
        }
        self.consume(
            TokenType::Semicolon,
            "Missing semicolon after variable declaration.",
        );

        Decl {
            kind: DeclKind::VarDecl(VarDecl {
                name: name.to_string(),
                ty,
                val,
            }),
        }
    }

    fn string_from_src(&self, start: usize, len: usize) -> String {
        self.src[start..start + len].to_string()
    }

    // ident: ty (, ident: ty)*
    fn parse_args(&mut self) -> (Vec<Ty>, Vec<String>) {
        let mut names = Vec::new();
        let mut types = Vec::new();
        self.consume(TokenType::Identifier, "");
        names.push(self.string_from_src(self.prev.start, self.prev.length));
        self.consume(TokenType::Colon, "");
        types.push(self.type_expr());

        while self.current.ty == TokenType::Comma {
            self.advance();
            self.consume(TokenType::Identifier, "");
            names.push(self.string_from_src(self.prev.start, self.prev.length));
            self.consume(TokenType::Colon, "");
            types.push(self.type_expr());
        }

        (types, names)
    }

    /// fn ident (args?) -> ty;
    fn fun_decl(&mut self) -> Decl {
        self.consume(
            TokenType::Fun,
            "Function declaration has to begin with 'fn' keyword.",
        );
        self.consume(
            TokenType::Identifier,
            "Expected a function name after the 'fn' keyword.",
        );
        let name = self.string_from_src(self.prev.start, self.prev.length);

        self.consume(TokenType::LParen, "Expected a '(' after 'fn' keyword");
        let (mut types, mut names) = (None, None);
        if self.current.ty != TokenType::RParen {
            let (t, n) = self.parse_args();
            (types, names) = (Some(Box::new(t)), Some(n));
        }

        self.consume(TokenType::RParen, "Expected a ')' after parameter list.");
        self.consume(TokenType::RArrow, "Expected a '->' after ')'.");

        let ty = self.type_expr();

        self.consume(
            TokenType::Semicolon,
            "Expected a ';' after a function declaration.",
        );

        Decl {
            kind: DeclKind::FunDecl(FunDecl {
                name,
                ty: Ty {
                    kind: TyKind::Function {
                        ret_type: Box::new(ty),
                        args: types,
                    },
                },
                param_names: names,
                code: None,
            }),
        }
    }

    fn block(&mut self) -> Decl {
        self.consume(TokenType::LBrace, "Block statement has to begin with a '{'");
        let mut decls = Vec::new();
        while self.current.ty != TokenType::RBrace {
            decls.push(self.declaration());
        }

        Decl {
            kind: DeclKind::Stmt(Stmt {
                kind: StmtKind::Block(Box::new(decls)),
            }),
        }
    }

    fn print_stmt(&mut self) -> Decl {
        self.consume(TokenType::Print, "");
        Decl {
            kind: DeclKind::Stmt(Stmt {
                kind: StmtKind::Print(self.expression()),
            }),
        }
    }

    fn declaration(&mut self) -> Decl {
        match self.current.ty {
            TokenType::Var => self.var_decl(),
            TokenType::Fun => self.fun_decl(),
            TokenType::LBrace => self.block(),
            TokenType::Print => self.print_stmt(),
            t => panic!("Declaration can't begin with token {:?}", t),
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
    use crate::ast::{Decl, DeclKind, FunDecl, Stmt, StmtKind, Ty, TyKind, VarDecl};

    use super::*;

    fn literal(val: i64) -> Expr {
        Expr {
            kind: ExprKind::IntegerLit(val),
        }
    }

    fn string_literal(val: &'static str) -> Expr {
        Expr {
            kind: ExprKind::StringLit(val.to_string()),
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

    fn var_expr(name: &'static str) -> Expr {
        Expr {
            kind: ExprKind::Var(name.to_string()),
        }
    }

    fn var_decl(name: String, ty: Ty, val: Option<Expr>) -> Decl {
        Decl {
            kind: DeclKind::VarDecl(VarDecl { name, ty, val }),
        }
    }

    fn function_type(ret_type: Ty, args: Option<Box<Vec<Ty>>>) -> Ty {
        Ty {
            kind: TyKind::Function {
                ret_type: Box::new(ret_type),
                args,
            },
        }
    }

    fn array_type(len: Expr, ty: Ty) -> Ty {
        Ty {
            kind: TyKind::Array {
                len,
                ty: Box::new(ty),
            },
        }
    }

    fn string_type() -> Ty {
        Ty {
            kind: TyKind::String,
        }
    }

    fn char_type() -> Ty {
        Ty { kind: TyKind::Char }
    }

    fn int_type() -> Ty {
        Ty {
            kind: TyKind::Int64,
        }
    }

    fn return_stmt_decl(expr: Expr) -> Decl {
        Decl {
            kind: DeclKind::Stmt(Stmt {
                kind: StmtKind::Return(expr),
            }),
        }
    }

    fn print_stmt_decl(expr: Expr) -> Decl {
        Decl {
            kind: DeclKind::Stmt(Stmt {
                kind: StmtKind::Print(expr),
            }),
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
    fn test_var_expr() {
        let expr = Parser::new("a").parse_expression();
        assert_eq!(expr, var_expr("a"));
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

    #[test]
    fn test_var_decl_array_type() {
        let decl = &Parser::new("var name: [10; char];").parse()[0];
        assert_eq!(
            decl,
            &var_decl(
                "name".to_string(),
                array_type(literal(10), char_type()),
                None
            )
        )
    }

    #[test]
    fn test_var_decl_fun_type() {
        let decl = &Parser::new("var lambda: fn(char, int) -> string;").parse()[0];
        assert_eq!(
            decl,
            &var_decl(
                "lambda".to_string(),
                function_type(string_type(), Some(Box::new(vec![char_type(), int_type()]))),
                None
            )
        )
    }

    #[test]
    fn test_block_stmt() {
        let decl = &Parser::new(
            "{
                print \"hello world\";
                var a: int = 10;
            }",
        )
        .parse()[0];

        assert_eq!(
            decl,
            &Decl {
                kind: DeclKind::Stmt(Stmt {
                    kind: StmtKind::Block(Box::new(vec![
                        print_stmt_decl(string_literal("hello world")),
                        var_decl("a".to_string(), int_type(), Some(literal(10))),
                    ]))
                })
            }
        )
    }

    #[test]
    fn test_fun_decl_no_body() {
        let decl = &Parser::new("fn foo(a: int, b: int) -> int;").parse()[0];
        assert_eq!(
            decl,
            &Decl {
                kind: DeclKind::FunDecl(FunDecl {
                    name: "foo".to_string(),
                    ty: function_type(int_type(), Some(Box::new(vec![int_type(), int_type()]))),
                    param_names: Some(vec!["a".to_string(), "b".to_string()]),
                    code: None
                })
            }
        )
    }

    #[test]
    fn test_fun_decl() {
        let decl = &Parser::new("fn foo(a: int, b: int) -> int { return a * b;}").parse()[0];
        assert_eq!(
            decl,
            &Decl {
                kind: DeclKind::FunDecl(FunDecl {
                    name: "foo".to_string(),
                    ty: function_type(int_type(), Some(Box::new(vec![int_type(), int_type()]))),
                    param_names: Some(vec!["a".to_string(), "b".to_string()]),
                    code: Some(Box::new(vec![return_stmt_decl(binary(
                        BinOp::Mul,
                        var_expr("a"),
                        var_expr("b")
                    ))]))
                })
            }
        )
    }
}
