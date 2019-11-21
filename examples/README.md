# K-Liveness Hyperproperty Example Programs

This is a repository of programs that exhibit (or fail to exhibit) various
k-liveness hyperproperties.

The following resources are useful for understanding k-liveness and
hyperproperties:

* [Simple Relational Correctness Proofs for Static Analyses and Program
  Transformations](http://www.cs.ioc.ee/ewscs/2008/benton/benton-popl04.pdf).
  Nick Benton, 2004.

* [Hyperproperties](https://www.cs.cornell.edu/~clarkson/papers/clarkson_hyperproperties_journal.pdf).
  Michael Clarkson and Fred Schneider, 2010.


## Project Structure

This project is organized into subdirectories according to class of k-liveness
hyperproperty. The `package.md` file in each subdirectory contains more
information about the subdirectory's specific hyperproperty.


## File Format

Each program file (ending in `.imp`) contains a program expressed in a simple
imperative language, a formal description of some k-liveness hyperproperty, and
an indication of whether or not the program exhibits that hyperproperty. The
syntax of the program and property languages are described below.

The general format of each `imp` file is:

| A comment briefly describing the file contents.          |
| `satisfies: <hyperproperty>` or `fails: <hyperproperty>` |
| The program(s).                                          |

Extra whitespace is insignificant in both programs and property specifications.
Lines beginning with `--` (two dashes) are treated as comments.


## Property Syntax

TODO


## Program Syntax

Programs are expressed in a simple imperative language that supports
specified-but-uninterpreted function calls.

The language's EBNF grammar is:

```
prog
    : 'prog' identifier '(' param-list ')' ':' block 'end'
    ;

stmt
    :'skip'
    | identifier := aexp
    | fun identifier '(' [param-list] ')' ':' block 'end'
    | call identifier '(' [param-list] ')' 'pre:' cond 'post:' cond
    | identifier := identifier '(' param-list ')'
    | 'if' cond 'then' stmt 'end'
    | 'if' cond 'then' stmt 'else' stmt 'end'
    | 'while' cond 'do' stmt 'end'
    ;

param-list:
    : identifier [',' param-list]
    ;

block
    : [stmt ';']* 'return' aexp ';'
    ;

aexp
   : identifier
   | integer
   | '(' aexp ')'
   | aexp '+' aexp
   | aexp '-' aexp
   | aexp '*' aexp
   | aexp '%' aexp
   ;

cond
    : 'true'
    | 'false'
    | aexp == aexp
    | aexp '<' aexp
    | aexp '<=' aexp
    | aexp '>' aexp
    | aexp '>=' aexp
    | '!' cond
    | cond '&&' cond
    | cond '||' cond
    ;
```
