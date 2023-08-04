%{

Require Import String.
Require CSC.Ltms.syntax CSC.Shared.Sema.

Definition expr := CSC.Ltms.syntax.expr.

%}

%token<nat> NUM

(*
    This represents all operators. Giving each
    operator its own token probably would have
    been cleaner, but I wanted to include
    strings in the example.
*)
%token ADD SUB MUL DIV LESS

%token LPAREN RPAREN EOF

%token<string> ID


%left LESS
%left ADD SUB
%left MUL DIV

%type<expr> expr

%start<expr> top_expr
%%

top_expr:
    | e=expr EOF
        { e }

expr:
    | i=NUM
      { CSC.Ltms.syntax.Xval(CSC.Ltms.syntax.Vnat i) }
    | x=ID
      { CSC.Ltms.syntax.Xvar x }
    | LPAREN e = expr RPAREN
      { e }
    | e1 = expr ADD e2 = expr
      { CSC.Ltms.syntax.Xbinop CSC.Shared.Sema.Badd e1 e2 }
    | e1 = expr SUB e2 = expr
      { CSC.Ltms.syntax.Xbinop CSC.Shared.Sema.Bsub e1 e2 }
    | e1 = expr MUL e2 = expr
      { CSC.Ltms.syntax.Xbinop CSC.Shared.Sema.Bmul e1 e2 }
    | e1 = expr DIV e2 = expr
      { CSC.Ltms.syntax.Xbinop CSC.Shared.Sema.Bdiv e1 e2 }
    | e1 = expr LESS e2 = expr
      { CSC.Ltms.syntax.Xbinop CSC.Shared.Sema.Bdiv e1 e2 }



