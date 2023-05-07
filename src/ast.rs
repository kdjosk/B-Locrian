#[derive(Debug, Eq, PartialEq)]
pub struct Ty {
    pub kind: TyKind,
}

#[derive(Debug, Eq, PartialEq)]
pub enum TyKind {
    Int64,
    Bool,
    Array {
        len: Expr,
        ty: Box<Ty>,
    },
    String,
    Char,
    Void,
    Function {
        ret_type: Box<Ty>,
        args: Option<Box<Vec<Ty>>>,
    },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Div,
    Mul,
    Greater,
    GreaterOrEqual,
    Less,
    LessOrEqual,
    Equal,
    NotEqual,
    Assign,
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
pub struct IfStmt {
    pub cond: Expr,
    pub then_branch: Box<Stmt>,
    pub else_branch: Option<Box<Stmt>>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct ForLoop {
    pub initializer: Decl,
    pub condition: Expr,
    pub increment: Expr,
    pub body: Box<Stmt>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Decl {
    pub kind: DeclKind,
}

#[derive(Debug, Eq, PartialEq)]
pub struct FunDecl {
    pub name: String,
    pub ty: Ty,
    pub param_names: Option<Vec<String>>,
    pub code: Box<Stmt>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct VarDecl {
    pub name: String,
    pub ty: Ty,
    pub val: Option<Expr>,
}

#[derive(Debug, Eq, PartialEq)]
pub enum DeclKind {
    FunDecl(FunDecl),
    VarDecl(VarDecl),
    Stmt(Stmt),
}

#[derive(Debug, Eq, PartialEq)]
pub enum StmtKind {
    Expr(Expr),
    IfStmt(Box<IfStmt>),
    ForLoop(Box<ForLoop>),
    Print(Expr),
    Return(Expr),
    Block(Box<Vec<Decl>>),
}

#[derive(Debug, Eq, PartialEq)]
pub struct Stmt {
    pub kind: StmtKind,
}
