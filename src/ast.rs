#[derive(Debug, Eq, PartialEq)]
pub struct Ty {}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Div,
    Mul,
}

#[derive(Debug, Eq, PartialEq)]
pub enum UnOp {
    // '-'
    Neg,
    //'!'
    Not,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Arg {
    pub name: String,
    pub value: Expr,
}

#[derive(Debug, Eq, PartialEq)]
pub enum ExprKind {
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Unary(UnOp, Box<Expr>),
    Var(String),
    IntegerLit(i64),
    StringLit(String),
    BoolLit(bool),
    Call(String, Vec<Arg>),
    Subscript(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Eq, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Block {
    pub body: Vec<Stmt>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct IfElse {
    pub cond: Expr,
    pub then_branch: Block,
    pub else_branch: Option<Block>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct ForLoop {
    pub initializer: Expr,
    pub condition: Expr,
    pub increment: Expr,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Decl {
    pub name: String,
    pub ty: Ty,
    pub value: Expr,
}

#[derive(Debug, Eq, PartialEq)]
pub enum StmtKind {
    Decl(Box<Decl>),
    Expr(Box<Expr>),
    IfElse(Box<IfElse>),
    ForLoop(Box<ForLoop>),
    Print(Box<Expr>),
    Return(Box<Expr>),
    Block(Box<Block>),
}

#[derive(Debug, Eq, PartialEq)]
pub struct Stmt {
    pub kind: StmtKind,
}
