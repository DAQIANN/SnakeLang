module SNAKE-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Val ::= Int | Bool | "None"
    syntax Vals ::= List{Val, ","} [klabel(exprs)]

    syntax Ids ::= List{Id, ","}

    syntax Expr ::= Val | Id
                  | "(" Expr ")" [bracket]
                  | Id "(" Exprs ")" [strict(2)]
                  | Id "." "next" "(" ")"
                  | Expr "[" Expr "]" [strict]
                  > Expr "*" Expr [strict]
                  > Expr "+" Expr [strict]
                  > Expr "=" Expr [strict]
                  | Expr "<" Expr [strict]
    syntax Exprs ::= List{Expr, ","} [strict, klabel(exprs)]
                   | Vals

    syntax Stmt ::= "skip"
                  | Ids ":=" Exprs [strict(2)]
                  | "if" Expr "{" Stmts "}" "else" "{" Stmts "}" [strict(1)]
                  | "while" Expr "{" Stmts "}"
                  | "for" "(" Stmt ";" Expr ";" Stmt ")" "{" Stmts "}"
                  | "for" Id "in" Expr "{" Stmts "}"
                  | "def" Id "(" Ids ")" "{" Stmts "}"
                  | "return" Expr [strict]
                  | "yield" Expr [strict]
    syntax Stmts ::= Stmt
                   | Stmts Stmts [right]

    syntax Prog ::= Stmts
endmodule

module SNAKE
    imports DOMAINS
    imports SNAKE-SYNTAX

    syntax Val ::= List
    syntax KResult ::= Val
                     | Vals

    configuration
        <k> $PGM:Prog </k>
        <env> .Map </env>
        <defs> .Map </defs>
        <callstack> .List </callstack>

    rule <k> def F(Args) { Body } => . ... </k>
        <defs> Defs => Defs[F <- def F(Args) { Body }] </defs>

    rule skip => .

    rule (S1 Rest):Stmts => S1 ~> Rest

    rule .Ids := .Vals => .
    rule <k> X:Id := V:Val => . ... </k>
        <env> Env => Env[X <- V] </env>
    rule (X:Id, Y:Id, Xs) := (V:Val, W:Val, Vs) => (X := V) (Y, Xs) := (W, Vs)

    rule <k> X:Id => Env[X] ... </k>
        <env> Env </env>

    rule if true  { A } else { _ } => A
    rule if false { _ } else { B } => B

    rule for X in E { Body } =>
            (!It:Id := E)
            (!Loop:Id := true)
            while !Loop {
                (X := !It.next())
                if X = None {
                    !Loop := false
                } else {
                    Body
                }
            }
    rule for (Init ; Cond ; Step) { Body } => Init while Cond { Body Step }
    rule while Cond { Body } => if Cond { Body while Cond { Body } } else { skip }

    rule I1 * I2 => I1 *Int I2
    rule I1 + I2 => I1 +Int I2
    rule I1 < I2 => I1 <Int I2
    rule V1 = V2 => V1 ==K V2

    syntax KItem ::= call(Map, K)
                   | setupArgs(Ids, Vals)

    rule <k> F(Args) ~> K => setupArgs(FuncArgs, Args) ~> Body </k>
        <env> Env => .Map </env>
        <defs> ... F |-> def F(FuncArgs) { Body } ... </defs>
        <callstack> Calls => ListItem(call(Env, K)) Calls </callstack>

    rule setupArgs(.Ids, .Vals) => .
    rule setupArgs((X, Args), (V, Vals)) => X := V ~> setupArgs(Args, Vals)

    rule <k> return V:Val ~> _ => V ~> K </k>
        <env> _ => Env </env>
        <callstack> ListItem(call(Env, K)) Calls => Calls </callstack>

    syntax Val ::= generated(Map, K, List)
    syntax KItem ::= updateGenerator(Id)

    rule <k> yield V:Val ~> K => generated(Env, K, ListItem(V)) ~> NewK </k>
        <env> Env => NewEnv </env>
        <callstack> ListItem(call(NewEnv, NewK)) Calls => Calls </callstack>

    rule None ~> updateGenerator(_) => None
    rule <k> generated(NewEnv, K, Vs) ~> updateGenerator(X) => X.next() ... </k>
        <env> Env => Env[X <- generated(NewEnv, K, Vs)] </env>

    rule <k> X.next() => V ... </k>
        <env> ... X |-> generated(_, _, ListItem(V) Rest => Rest) ... </env>

    rule <k> X.next() ~> K => NewK </k>
        <env> (X |-> generated(NewEnv, NewK, .List)) Env => NewEnv </env>
        <callstack> Calls => ListItem(call(Env, updateGenerator(X) ~> K)) Calls </callstack>
endmodule

