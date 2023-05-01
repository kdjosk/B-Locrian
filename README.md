# Language specification

## B-Locrian

### keywords

```
array
bool
char
else
false
for
fn
if
int
print 
return 
string 
true 
void
while 
and 
or
```

### types

```
x: int;
y: int;
b: bool = false;
c: char = 'q';
s: string = "hello world\n";
a: array [5] int = {1, 2, 3, 4, 5};
```

### functions

```
fn foo(x: int, y: fn(char, bool) -> void) -> void {
    return x * y;
}
```

### operators

```
[] f()  array subscript, function call
++ --   postfix increment, decrement
- !     unary negation, logical not
^       exponentiation
* / %   multiplication, division, modulus
+ -     addition subtraction
< <= 
> >=
== !=   comparison
and or   logical and, logical or
=       assignment
```


```
program: 
    stmt* EOF
    ;

stmt:
    declStmt
    | exprStmt
    | ifStmt
    | forStmt
    | printStmt
    | returnStmt
    | blockStmt
    ;

declStmt:
    varDecl
    | funDecl
    ;

funDecl:
    'fn' IDENT '(' args? ')' '->' typeExpr blockStmt  
    ;

typeExpr:
    TYPE
    | 'fn' '(' typeArgs? ')' '->' typeExpr
    ;

typeArgs:
    typeExpr (',' typeExpr)*
    ; 

exprStmt:
    expr ';'
    ;

ifStmt:
    'if' '(' expr ')' statement ('else' statemet)?
    ;

forStmt:
    'for' '(' expr? ';' expr? ';' expr? ')' stmt 
    ;

printStmt:
    'print' expr ';'
    ;

returnStmt:
    'return' expr ';'
    ;

varDecl:
    IDENT ':' TYPE ('=' expr)? ';'
    ;


expr:
    binaryExpr
    | unaryExpr
    | literalExpr
    | groupingExpr

// ambiguities and associativity handled by the Pratt parser
binaryExpr:
    expr BIN_OP expr
    ;

unaryExpr:
    UN_OP expr
    ;

literalExpr:
    NUMBER
    | STRING
    | FALSE
    | TRUE
    ;

```