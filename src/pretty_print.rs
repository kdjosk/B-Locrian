use crate::ast::*;

pub struct AstPrinter<'a> {
    ast: &'a Vec<Decl>,
}

impl<'a> AstPrinter<'a> {
    pub fn new(ast: &'a Vec<Decl>) -> AstPrinter {
        AstPrinter { ast }
    }

    pub fn print_tree(&self) {
        for decl in self.ast {
            self.walk_decl(decl, String::new());
            println!("");
        }
    }

    fn walk_decl(&self, decl: &Decl, prefix: String) {
        match &decl.kind {
            DeclKind::FunDecl(d) => self.walk_fun_decl(d, prefix),
            DeclKind::VarDecl(d) => self.walk_var_decl(d, prefix),
            DeclKind::Stmt(s) => self.walk_stmt(s, prefix),
        }
    }

    fn walk_stmt(&self, stmt: &Stmt, prefix: String) {
        match &stmt.kind {
            StmtKind::Expr(expr) => {
                println!("{}expression statement", prefix);
                print!("{}  ", prefix);
                self.walk_expr(expr);
                print!("\n");
            }
            StmtKind::IfStmt(ifstmt) => {
                println!("{}if statement", prefix);
                print!("{}  condition: ", prefix);
                self.walk_expr(&ifstmt.cond);
                print!("\n");
                println!("{}  then branch:", prefix);
                self.walk_stmt(&ifstmt.then_branch, prefix.clone() + "    ");
                match &ifstmt.else_branch {
                    Some(b) => {
                        println!("{}  else branch:", prefix);
                        self.walk_stmt(b, prefix + "    ");
                    }
                    None => (),
                }
            }
            StmtKind::ForLoop(forloop) => {
                println!("{}for loop", prefix);
                match &forloop.initializer {
                    Some(decl) => {
                        println!("{}  initializer:", prefix);
                        self.walk_decl(decl, prefix.clone() + "    ");
                    }
                    None => (),
                }
                match &forloop.condition {
                    Some(expr) => {
                        print!("{}  condition: ", prefix);
                        self.walk_expr(expr);
                        print!("\n");
                    }
                    None => (),
                }
                match &forloop.increment {
                    Some(expr) => {
                        print!("{}  increment: ", prefix);
                        self.walk_expr(expr);
                        print!("\n");
                    }
                    None => (),
                }
                println!("{}  body:", prefix);
                self.walk_stmt(&forloop.body, prefix + "    ");
            }
            StmtKind::WhileLoop(stmt) => {
                println!("{}while loop", prefix);
                print!("{}  condition: ", prefix);
                self.walk_expr(&stmt.condition);
                print!("\n");
                println!("{}  body:", prefix);
                self.walk_stmt(&stmt.body, prefix + "    ");
            }
            StmtKind::Print(expr) => {
                print!("{}print ", prefix);
                self.walk_expr(expr);
                print!("\n");
            }
            StmtKind::Return(expr) => {
                print!("{}return ", prefix);
                self.walk_expr(expr);
                print!("\n");
            }
            StmtKind::Block(block) => {
                println!("{}block statement", prefix);
                for decl in block.iter() {
                    self.walk_decl(decl, prefix.clone() + "  ");
                }
            }
        }
    }

    fn walk_var_decl(&self, var_decl: &VarDecl, prefix: String) {
        println!("{}variable declaration", prefix);
        println!("{}  name: {}", prefix, var_decl.name);
        print!("{}  type: ", prefix);
        self.walk_type(&var_decl.ty);
        print!("\n");
        print!("{}  value: ", prefix);
        match &var_decl.val {
            Some(expr) => self.walk_expr(expr),
            None => print!("uninitialized"),
        }
        print!("\n");
    }

    fn walk_fun_decl(&self, fun_decl: &FunDecl, prefix: String) {
        println!("{}function declaration", prefix);
        println!("{}  name: {}", prefix, fun_decl.name);
        print!("{}  type: ", prefix);
        self.walk_type(&fun_decl.ty);
        print!("\n");
        print!("{}  param_names: ", prefix);
        match &fun_decl.param_names {
            Some(pl) => print!("{:?}\n", pl),
            None => print!("\n"),
        }
        println!("{}  body:", prefix);
        self.walk_stmt(&fun_decl.code, prefix + "    ");
    }

    fn walk_expr(&self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Binary(op, lhs, rhs) => {
                print!("( ");
                self.walk_bin_op(op);
                print!(" ");
                self.walk_expr(lhs);
                print!(" ");
                self.walk_expr(rhs);
                print!(")");
            }
            ExprKind::Unary(op, ex) => {
                print!("({:?} ", op);
                self.walk_expr(ex);
                print!(")");
            }
            ExprKind::Var(name) => print!("'{}'", name),
            ExprKind::IntegerLit(val) => print!("{}", val),
            ExprKind::StringLit(val) => print!("\"{}\"", val),
            ExprKind::BoolLit(val) => print!("{}", val),
            ExprKind::Call(f, args) => {
                print!("call ");
                self.walk_expr(f);
                if !args.is_empty() {
                    print!(" with args ");
                    for (ix, arg) in args.iter().enumerate() {
                        self.walk_expr(arg);
                        if ix < args.len() - 1 {
                            print!(", ");
                        }
                    }
                }
            }
            ExprKind::Subscript(a, i) => {
                print!("subscript ");
                self.walk_expr(a);
                print!(" at ");
                self.walk_expr(i);
            }
        }
    }

    fn walk_bin_op(&self, op: &BinOp) {
        match op {
            BinOp::Add => print!("+"),
            BinOp::Sub => print!("-"),
            BinOp::Div => print!("/"),
            BinOp::Mul => print!("*"),
            BinOp::Greater => print!(">"),
            BinOp::GreaterOrEqual => print!(">="),
            BinOp::Less => print!("<"),
            BinOp::LessOrEqual => print!("<="),
            BinOp::Equal => print!("=="),
            BinOp::NotEqual => print!("!="),
            BinOp::Assign => print!("="),
            BinOp::LogicAnd => print!("and"),
            BinOp::LogicOr => print!("or"),
        }
    }

    fn walk_type(&self, ty: &Ty) {
        match &ty.kind {
            TyKind::Int64 => print!("i64"),
            TyKind::Bool => print!("bool"),
            TyKind::Array { len, ty } => {
                print!("[");
                self.walk_type(ty);
                print!("; ");
                self.walk_expr(len);
                print!("]");
            }
            TyKind::String => print!("string"),
            TyKind::Char => print!("char"),
            TyKind::Void => print!("void"),
            TyKind::Function { ret_type, args } => {
                print!("fn (");
                match args {
                    Some(al) => {
                        for (ix, t) in al.iter().enumerate() {
                            self.walk_type(t);
                            if ix < al.len() - 1 {
                                print!(", ");
                            }
                        }
                    }
                    None => (),
                }
                print!(") -> ");
                self.walk_type(ret_type);
            }
        }
    }
}
