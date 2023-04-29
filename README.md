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
c: char = 'q`;
s: string = "hello world\n";
a: array [5] int = {1, 2, 3, 4, 5};
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
    declaration* EOF
    ;

```