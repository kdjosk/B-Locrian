struct Ty {}

enum BinOp {
    Add,
    Sub,
    Div,
    Mul,
}

enum UnOp {
    // unary '-'
    Neg
}

struct Arg {
    name: String,
    value: Expr,
}

enum ExprKind {
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Unary(UnOp, Box<Expr>),
    Var(String),
    IntegerLit(u32),
    StringLit(String),
    Call(String, Vec<Arg>),
    Subscript(Box<Expr>, Box<Expr>)
}

struct Expr {
    kind: ExprKind,

}

struct Block {
    body: Vec<Stmt>,
}

struct IfElse {
    cond: Expr,
    then_branch: Block,
    else_branch: Option<Block>
}

struct ForLoop {
    initializer: Expr,
    condition: Expr,
    increment: Expr,
}

struct Decl {
    name: String,
    ty: Ty,
    value: Expr,
}

enum StmtKind {
    Decl(Box<Decl>),
    Expr(Box<Expr>),
    IfElse(Box<IfElse>),
    ForLoop(Box<ForLoop>),
    Print(Box<Expr>),
    Return(Box<Expr>),
    Block(Box<Block>),
}

struct Stmt {
    kind: StmtKind
}


