use crate::ast::{
    BinOp, Decl, DeclKind, Expr, ExprKind, FunDecl, IfStmt, Stmt, StmtKind, Ty, TyKind, UnOp,
    VarDecl, ForLoop, WhileLoop,
};
use crate::scanner::{Scanner, Token, TokenType};

pub struct Parser<'a> {
    src: &'a str,
    scanner: Scanner<'a>,
    current: Token,
    prev: Token,
    pub had_error: bool,
    panic_mode: bool,
}

enum Precedence {
    None = -100,
    Assignment = 5,
    LogicOr = 6,
    LogicAnd = 7,
    Equality = 8,
    Comparison = 9,
    Term = 10,
    Factor = 11,
    Unary = 30,
    // includes (), []
    Call = 31,
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
            panic_mode: false,
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

    fn error_at_current(&mut self, msg: &'static str) {
        self.error_at(&self.current.clone(), msg);
    }

    fn error_at(&mut self, token: &Token, msg: &'static str) {
        if self.panic_mode {
            // suppress cascading errors
            return;
        }
        self.panic_mode = true;
        self.had_error = true;

        eprintln!(
            "Syntax error: {}, at line {}, on token '{}'",
            msg, 
            token.line,
            self.string_from_src(token.start, token.length)
        )
    }

    fn synchronize(&mut self) {
        self.panic_mode = false;

        while self.current.ty != TokenType::Eof {
            if self.prev.ty == TokenType::Semicolon {
                // we finished the previous declaration and can
                // try to resume parsing
                return;
            };
            match self.current.ty {
                TokenType::Fun
                | TokenType::Var
                | TokenType::If
                | TokenType::For
                | TokenType::While
                | TokenType::Print        
                | TokenType::Return => { 
                    // we found a beginning of a new declaration
                    // and can resume parsing safely
                    return; 
                }
                _ => ()
            }

            self.advance()
        }
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
            TokenType::Not => UnOp::Not,
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
        let op = self.get_bin_op(self.prev.ty);
        let rhs = self.parse_precedence(self.precedence(self.prev.ty) as i32 + 1);
        Expr {
            kind: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)),
        }
    }

    /// expr (, expr)*
    fn args(&mut self) -> Vec<Expr> {
        let mut args = Vec::new();
        args.push(self.expression());
        while self.current.ty == TokenType::Comma {
            self.advance();  // go through ','
            args.push(self.expression())
        }
        args
    }

    /// expr (args?)
    fn call(&mut self, lhs: Expr) -> Expr {
        let mut args = Vec::new();
        if self.current.ty != TokenType::RParen {
            args = self.args();
        }
        self.consume(TokenType::RParen, "Missing closing ')' in a call expression");
        Expr {
            kind: ExprKind::Call(Box::new(lhs), args)
        }
        
    }

    /// expr [expr]
    fn subscript(&mut self, lhs: Expr) -> Expr {
        let idx = self.expression();
        self.consume(TokenType::RBracket, "Expected a closing ']' in subscript expression");
        Expr {
            kind: ExprKind::Subscript(Box::new(lhs), Box::new(idx))
        }
    }

    fn get_bin_op(&self, token_ty: TokenType) -> BinOp {
        match token_ty {
            TokenType::Plus => BinOp::Add,
            TokenType::Minus => BinOp::Sub,
            TokenType::Slash => BinOp::Div,
            TokenType::Star => BinOp::Mul,
            TokenType::Less => BinOp::Less,
            TokenType::Greater => BinOp::Greater,
            TokenType::LessEqual => BinOp::LessOrEqual,
            TokenType::GreaterEqual => BinOp::GreaterOrEqual,
            TokenType::EqualEqual => BinOp::Equal,
            TokenType::BangEqual => BinOp::NotEqual,
            TokenType::And => BinOp::LogicAnd,
            TokenType::Or => BinOp::LogicOr,
            TokenType::Equal => BinOp::Assign,
            _ => unreachable!(),
        }
    }

    fn precedence(&self, token_ty: TokenType) -> Precedence {
        match token_ty {
            TokenType::LParen | TokenType::LBracket => Precedence::Call,
            TokenType::Plus | TokenType::Minus => Precedence::Term,
            TokenType::Star | TokenType::Slash => Precedence::Factor,
            TokenType::Greater 
            | TokenType::GreaterEqual 
            | TokenType::Less 
            | TokenType::LessEqual => Precedence::Comparison,
            TokenType::EqualEqual | TokenType::BangEqual => Precedence::Equality,
            TokenType::And => Precedence::LogicAnd,
            TokenType::Or => Precedence::LogicOr,
            TokenType::Equal => Precedence::Assignment,
            _ => Precedence::None,
        }
    }

    fn get_prefix_rule(&self, token_ty: TokenType) -> fn(&mut Self) -> Expr {
        match token_ty {
            TokenType::NumberLit => Self::number,
            TokenType::StringLit => Self::string,
            TokenType::LParen => Self::grouping,
            TokenType::Minus | TokenType::Not => Self::unary,
            TokenType::False | TokenType::True => Self::bool_literal,
            TokenType::Identifier => Self::variable,
            t => panic!("Expression can't begin with {:?}", t),
        }
    }


    #[rustfmt::skip]
    fn get_infix_rule(&self, token_ty: TokenType) -> fn(&mut Self, Expr) -> Expr {
        match token_ty {
            TokenType::LParen => Self::call,
            TokenType::LBracket => Self::subscript,
            TokenType::Plus
            | TokenType::Minus
            | TokenType::Slash
            | TokenType::Star
            | TokenType::EqualEqual
            | TokenType::BangEqual
            | TokenType::Less
            | TokenType::LessEqual
            | TokenType::Greater
            | TokenType::GreaterEqual 
            | TokenType::Equal
            | TokenType::And
            | TokenType::Or => Self::binary,
            _ => unreachable!(),
        }
    }

    fn expression(&mut self) -> Expr {
        self.parse_precedence(Precedence::Assignment as i32)
    }

    fn parse_precedence(&mut self, precedence: i32) -> Expr {
        self.advance();
        let prefix_rule = self.get_prefix_rule(self.prev.ty);

        let mut expr = prefix_rule(self);

        while precedence <= self.precedence(self.current.ty) as i32 {
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
            // [int; 10]
            TokenType::LBracket => {
                let ty = self.type_expr();
                self.consume(
                    TokenType::Semicolon,
                    "Expected a ';' after array type expression",
                );
                let length = self.expression();
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
    fn parse_params(&mut self) -> (Vec<Ty>, Vec<String>) {
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
            let (t, n) = self.parse_params();
            (types, names) = (Some(Box::new(t)), Some(n));
        }

        self.consume(TokenType::RParen, "Expected a ')' after parameter list.");
        self.consume(TokenType::RArrow, "Expected a '->' after ')'.");

        let ty = self.type_expr();

        let body = self.block_stmt();

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
                code: Box::new(body),
            }),
        }
    }

    fn block_stmt(&mut self) -> Stmt {
        self.consume(TokenType::LBrace, "Block statement has to begin with a '{'");
        let mut decls = Vec::new();

        while self.current.ty != TokenType::RBrace {
            decls.push(self.declaration());
        }

        self.consume(TokenType::RBrace, "Missing '}' after a block statement.");

        Stmt {
            kind: StmtKind::Block(Box::new(decls)),
        }
    }

    fn print_stmt(&mut self) -> Stmt {
        self.consume(TokenType::Print, "");
        let expr = self.expression();
        self.consume(
            TokenType::Semicolon,
            "Expected a ';' after a print statement",
        );
        Stmt {
            kind: StmtKind::Print(expr),
        }
    }

    fn return_stmt(&mut self) -> Stmt {
        self.consume(TokenType::Return, "");
        let expr = self.expression();
        self.consume(
            TokenType::Semicolon,
            "Expected a ';' after a return statement",
        );
        Stmt {
            kind: StmtKind::Return(expr),
        }
    }

    /// if expr block (else (ifstmt | block))?
    fn if_stmt(&mut self) -> Stmt {
        self.advance(); // move through 'if'
        let cond = self.expression();
        let then_branch = Box::new(self.block_stmt());
        let mut else_branch = None;
        if self.current.ty == TokenType::Else {
            self.advance();
            else_branch = match self.current.ty {
                TokenType::If => Some(Box::new(self.if_stmt())),
                TokenType::LBrace => Some(Box::new(self.block_stmt())),
                t => panic!("Illegal token {:?} after 'else' keyword", t),
            }
        }

        Stmt {
            kind: StmtKind::IfStmt(Box::new(IfStmt {
                cond,
                then_branch,
                else_branch,
            })),
        }
    }

    fn expr_stmt(&mut self) -> Stmt {
        let expr = self.expression();
        self.consume(TokenType::Semicolon, "Expected a ';' after an expression");
        Stmt {
            kind: StmtKind::Expr(expr)
        }
    }

    /// for ((expr_stmt | var_decl | ;) expr? ; expr?) block
    fn for_stmt(&mut self) -> Stmt {
        self.advance();  // go through the 'for'
        self.consume(TokenType::LParen, "Expected a '(' after 'for' keyword");
        let initializer = match self.current.ty {
            TokenType::Semicolon => { 
                self.advance();  // go through the ';' 
                None
            },
            TokenType::Var => Some(self.var_decl()),
            _ => Some(Decl{ kind: DeclKind::Stmt(self.expr_stmt())}),
        };

        let condition = match self.current.ty {
            TokenType::Semicolon => None,
            _ => Some(self.expression()),
        };

        self.advance();  // go through ';'

        let increment = match self.current.ty {
            TokenType::RParen => None,
            _ => Some(self.expression()),
        };

        self.consume(TokenType::RParen, "Expected a ')' after the increment expression of the for loop");

        let body = self.block_stmt();

        Stmt {
            kind: StmtKind::ForLoop(
                Box::new(ForLoop{
                    initializer,
                    condition,
                    increment,
                    body: Box::new(body)
                })
            )
        }
        
    }

    fn while_stmt(&mut self) -> Stmt {
        self.advance();  // go through 'while'
        let condition = self.expression();
        let body = self.block_stmt();
        Stmt {
            kind: StmtKind::WhileLoop(Box::new(WhileLoop {
                condition,
                body: Box::new(body),
            }))
        }    
    }

    fn declaration(&mut self) -> Decl {
        let decl = match self.current.ty {
            TokenType::Var => self.var_decl(),
            TokenType::Fun => self.fun_decl(),
            TokenType::LBrace => Decl {
                kind: DeclKind::Stmt(self.block_stmt()),
            },
            TokenType::Print => Decl {
                kind: DeclKind::Stmt(self.print_stmt()),
            },
            TokenType::Return => Decl {
                kind: DeclKind::Stmt(self.return_stmt()),
            },
            TokenType::If => Decl {
                kind: DeclKind::Stmt(self.if_stmt()),
            },
            TokenType::For => Decl {
                kind: DeclKind::Stmt(self.for_stmt()),
            },
            TokenType::While => Decl {
                kind: DeclKind::Stmt(self.while_stmt()),
            },
            _ => Decl {
                kind: DeclKind::Stmt(self.expr_stmt()),
            }
        };

        if self.panic_mode {
            self.synchronize();
        }

        decl
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
    use crate::ast::{
        Decl, DeclKind, ForLoop, FunDecl, IfStmt, Stmt, StmtKind, Ty, TyKind, VarDecl, WhileLoop,
    };

    use super::*;

    fn assert_expr(src: &'static str, expr: Expr) {
        let mut parser = Parser::new(src);
        let expr_ = parser.parse_expression();
        assert_eq!(
            expr,
            expr_,
        );
        assert!(!parser.had_error);
    }

    fn assert_decl(src: &'static str, decl: Decl) {
        let mut parser = Parser::new(src);
        let decl_ = &parser.parse()[0];
        assert_eq!(
            &decl,
            decl_,
        );
        assert!(!parser.had_error);
    }

    fn literal(val: i64) -> Expr {
        Expr {
            kind: ExprKind::IntegerLit(val),
        }
    }

    fn bool_literal(val: bool) -> Expr {
        Expr {
            kind: ExprKind::BoolLit(val)
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

    fn call_expr(name: Expr, args: Vec<Expr>) -> Expr {
        Expr {
            kind: ExprKind::Call(Box::new(name), args)
        }
    }

    fn subscript_expr(name: Expr, index: Expr) -> Expr {
        Expr {
            kind: ExprKind::Subscript(Box::new(name), Box::new(index))
        }
    }

    fn var_decl(name: &'static str, ty: Ty, val: Option<Expr>) -> Decl {
        Decl {
            kind: DeclKind::VarDecl(VarDecl { name: name.to_string(), ty, val }),
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

    fn return_stmt(expr: Expr) -> Stmt {
        Stmt {
            kind: StmtKind::Return(expr),
        }
    }

    fn print_stmt(expr: Expr) -> Stmt {
        Stmt {
            kind: StmtKind::Print(expr),
        }
    }

    fn block_stmt(body: Vec<Decl>) -> Stmt {
        Stmt {
            kind: StmtKind::Block(Box::new(body)),
        }
    }

    fn expr_stmt(expr: Expr) -> Stmt {
        Stmt {
            kind: StmtKind::Expr(expr),
        }
    }

    fn if_stmt(cond: Expr, then_branch: Stmt, else_branch: Stmt) -> Stmt {
        Stmt {
            kind: StmtKind::IfStmt(Box::new(IfStmt {
                cond,
                then_branch: Box::new(then_branch),
                else_branch: Some(Box::new(else_branch)),
            })),
        }
    }

    fn for_stmt(initializer: Option<Decl>, condition: Option<Expr>, increment: Option<Expr>, body: Stmt) -> Stmt {
        Stmt {
            kind: StmtKind::ForLoop(Box::new(ForLoop {
                initializer,
                condition,
                increment,
                body: Box::new(body),
            })),
        }
    }

    fn while_stmt(condition: Expr, body: Stmt) -> Stmt {
        Stmt {
            kind: StmtKind::WhileLoop(Box::new(WhileLoop{
                condition,
                body: Box::new(body),
            }))
        }
    }

    fn decl_stmt(stmt: Stmt) -> Decl {
        Decl {
            kind: DeclKind::Stmt(stmt),
        }
    }

    #[test]
    fn test_addition() {
        assert_expr("2 + 3", binary(BinOp::Add, literal(2), literal(3)))
    }

    #[test]
    fn test_subtraction() {
        assert_expr("2 - 3", binary(BinOp::Sub, literal(2), literal(3)))
    }

    #[test]
    fn test_multiplication() {
        assert_expr("2 * 3", binary(BinOp::Mul, literal(2), literal(3)))
    }

    #[test]
    fn test_division() {
        assert_expr("2 / 3", binary(BinOp::Div, literal(2), literal(3)))
    }

    #[test]
    fn test_equality() {
        assert_expr("2 == 4", binary(BinOp::Equal, literal(2), literal(4)))
    }

    #[test]
    fn test_not_equal() {
        assert_expr("2 != 4", binary(BinOp::NotEqual, literal(2), literal(4)))
    }

    #[test]
    fn test_less() {
        assert_expr("2 < 4", binary(BinOp::Less, literal(2), literal(4)))
    }

    #[test]
    fn test_greater() {
        assert_expr("2 > 4", binary(BinOp::Greater, literal(2), literal(4)))
    }

    #[test]
    fn test_less_or_equal() {
        assert_expr("2 <= 4", binary(BinOp::LessOrEqual, literal(2), literal(4)))
    }

    #[test]
    fn test_greater_or_equal() {
        assert_expr("2 >= 4", binary(BinOp::GreaterOrEqual, literal(2), literal(4)))
    }

    #[test]
    fn test_logic_and() {
        assert_expr("true and false", binary(BinOp::LogicAnd, bool_literal(true), bool_literal(false)))
    }

    #[test]
    fn test_logic_or() {
        assert_expr("true or false", binary(BinOp::LogicOr, bool_literal(true), bool_literal(false)))
    }

    #[test]
    fn test_unary_not() {
        assert_expr("not true", unary(UnOp::Not, bool_literal(true)))
    }

    #[test]
    fn test_unary_neg() {
        assert_expr("-2", unary(UnOp::Neg, literal(2)))
    }

    #[test]
    fn test_grouping() {
        assert_expr(
            "(2 + 3) * 4",
            binary(
                BinOp::Mul,
                binary(BinOp::Add, literal(2), literal(3)),
                literal(4),
            )
        )
    }

    #[test]
    fn test_assignment() {
        assert_expr("a = 2", binary(BinOp::Assign, var_expr("a"), literal(2)))
    }

    #[test]
    fn test_raising_precedence() {
        assert_expr(
            "a = true or true and 4 == 5 < 2 + 3 * -f(2)",
            binary(
                BinOp::Assign,
                var_expr("a"),
                binary(
                    BinOp::LogicOr, 
                    bool_literal(true), 
                    binary(
                        BinOp::LogicAnd,
                        bool_literal(true),
                        binary(
                            BinOp::Equal,
                            literal(4),
                            binary(
                                BinOp::Less,
                                literal(5),
                                binary(
                                    BinOp::Add,
                                    literal(2),
                                    binary(
                                        BinOp::Mul,
                                        literal(3), 
                                        unary(
                                            UnOp::Neg,
                                            call_expr(
                                                var_expr("f"),
                                                vec![literal(2)]
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
    }

    #[test]
    fn test_descending_precedence() {
        assert_expr(
            "-f(2) * 3 + 2 > 5 == 4 and true or true",
            binary(
                BinOp::LogicOr,
                binary(
                    BinOp::LogicAnd,
                    binary(
                        BinOp::Equal,
                        binary(
                            BinOp::Greater,
                            binary(
                                BinOp::Add,
                                binary(
                                    BinOp::Mul,
                                    unary(
                                        UnOp::Neg,
                                        call_expr(var_expr("f"), vec![literal(2)]),
                                    ),
                                    literal(3)
                                ),
                                literal(2),
                            ),
                            literal(5),
                        ),
                        literal(4),
                    ),
                    bool_literal(true)
                ),
                bool_literal(true)
            )
        )
    }

    #[test]
    fn test_subscript_of_call() {
        assert_expr(
            "f(2)[3]",
            subscript_expr(
                call_expr(var_expr("f"), vec![literal(2)]), 
                literal(3)
            )
        )
    }

    #[test]
    fn test_call_of_subscript() {
        assert_expr(
            "a[2](3)",
            call_expr(
                subscript_expr(var_expr("a"), literal(2)),
                vec![literal(3)],
            )
        )
    }

    #[test]
    fn test_var_expr() {
        assert_expr("a", var_expr("a"));
    }

    #[test]
    fn test_call_expr() {
        assert_expr(
            "a(b, 2 + 2)", 
            call_expr(var_expr("a"), vec![var_expr("b"), binary(BinOp::Add, literal(2), literal(2))])
        )
    }

    #[test]
    fn test_subscript_expr() {
        assert_expr(
            "a[3 * 10]",
            subscript_expr(var_expr("a"), binary(BinOp::Mul, literal(3), literal(10)))
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
        assert_decl(
            "var ident: int;",
            var_decl("ident", int_type(), None)
        )
    }

    #[test]
    fn test_var_decl_array_type() {
        assert_decl(
            "var name: [char; 10];",
            var_decl(
                "name",
                array_type(literal(10), char_type()),
                None
            )
        )
    }

    #[test]
    fn test_var_decl_fun_type() {
        assert_decl(
            "var lambda: fn(char, int) -> string;",
            var_decl(
                "lambda",
                function_type(string_type(), Some(Box::new(vec![char_type(), int_type()]))),
                None
            )
        )
    }

    #[test]
    fn test_block_stmt() {
        assert_decl(
            "{
                print \"hello world\";
                var a: int = 10;
            }",
            decl_stmt(block_stmt(vec![
                        decl_stmt(print_stmt(string_literal("hello world"))),
                        var_decl("a", int_type(), Some(literal(10))),
                    ]))
        )
    }

    #[test]
    fn test_fun_decl() {
        assert_decl(
            "fn foo(a: int, b: int) -> int { return a * b;}",
            Decl {
                kind: DeclKind::FunDecl(FunDecl {
                    name: "foo".to_string(),
                    ty: function_type(int_type(), Some(Box::new(vec![int_type(), int_type()]))),
                    param_names: Some(vec!["a".to_string(), "b".to_string()]),
                    code: Box::new(block_stmt(vec![decl_stmt(return_stmt(binary(
                        BinOp::Mul,
                        var_expr("a"),
                        var_expr("b")
                    )))]))
                })
            }
        )
    }

    #[test]
    fn test_if_else_decl() {
        assert_decl(
            "
            if is_true {
                print \"true\";            
            } else if is_false {
                print \"false\";
            } else if cookies {
                print \"cookies\";
            } else {
                print \"unknown\";
            }",
            decl_stmt(if_stmt(
                var_expr("is_true"),
                block_stmt(vec![decl_stmt(print_stmt(string_literal("true")))]),
                if_stmt(
                    var_expr("is_false"),
                    block_stmt(vec![decl_stmt(print_stmt(string_literal("false")))]),
                    if_stmt(
                        var_expr("cookies"),
                        block_stmt(vec![decl_stmt(print_stmt(string_literal("cookies")))]),
                        block_stmt(vec![decl_stmt(print_stmt(string_literal("unknown")))])
                    )
                )
            ))
        )
    }

    #[test]
    fn test_for_loop() {
        assert_decl(
            "for (var i: int = 0; i < 10; i = i + 1) {
                 print \"loop\";
            }",
            decl_stmt(for_stmt(
                Some(var_decl("i", int_type(), Some(literal(0)))),
                Some(binary(BinOp::Less, var_expr("i"), literal(10))),
                Some(binary(BinOp::Assign, var_expr("i"), binary(BinOp::Add, var_expr("i"), literal(1)))),
                block_stmt(vec![decl_stmt(print_stmt(string_literal("loop")))])
            ))
        )
    }

    #[test]
    fn test_while_loop() {
        assert_decl(
            "while a > 10 {
                a = a - 1;
            }",
            decl_stmt(
                while_stmt(
                    binary(BinOp::Greater, var_expr("a"), literal(10)), 
                    block_stmt(
                        vec![
                            decl_stmt(expr_stmt(binary(BinOp::Assign, var_expr("a"), binary(BinOp::Sub, var_expr("a"), literal(1)))))
                        ]
                    )
                )
            )
        )
    }
}
