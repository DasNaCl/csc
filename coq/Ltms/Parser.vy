%{

Require Import String.
Require Import CSC.Ltms.syntax CSC.Shared.Sema.

Definition expr := CSC.Ltms.syntax.expr.

%}

%token<nat> NUM

(*
    This represents all operators. Giving each
    operator its own token probably would have
    been cleaner, but I wanted to include
    strings in the example.
*)
%token ADD SUB MUL DIV EQUAL

%token LPAREN RPAREN LBRACKET RBRACKET LANGLE RANGLE LARROW COMMA
%token GET SET LET NEW IN DELETE RETURN CALL IFZ THEN ELSE ABORT 
%token EOF

%token<string> ID

%nonassoc ID
%left LARROW LANGLE
%left ADD SUB
%left MUL DIV
%right RETURN IN
%left ELSE

%type<expr> expr

%start<expr> top_expr
%%

top_expr:
    | e=expr EOF
        { e }

expr:
    | i = NUM
      { CSC.Ltms.syntax.Xval(CSC.Ltms.syntax.Vnat i) }
    | x = ID
      { CSC.Ltms.syntax.Xvar x }
    | LPAREN e = expr RPAREN
      { e }
    | e1 = expr ADD e2 = expr
      { Xbinop Badd e1 e2 }
    | e1 = expr SUB e2 = expr
      { Xbinop Bsub e1 e2 }
    | e1 = expr MUL e2 = expr
      { Xbinop Bmul e1 e2 }
    | e1 = expr DIV e2 = expr
      { Xbinop Bdiv e1 e2 }
    | e1 = expr LANGLE e2 = expr
      { Xbinop Bdiv e1 e2 }
    | GET x = ID LBRACKET e = expr RBRACKET
      { Xget x e }
    | SET x = ID LBRACKET e1 = expr RBRACKET LARROW e2 = expr
      { Xset x e1 e2 }
    | LET x = ID EQUAL e1 = expr IN e2 = expr
      { Xlet x e1 e2 }
    | LET x = ID EQUAL NEW e1 = expr LBRACKET e2 = expr RBRACKET IN e3 = expr
      { Xnew x e1 e2 e3 }
    | DELETE x = ID
      { Xdel x }
    | LANGLE e1 = expr COMMA e2 = expr RANGLE 
      { Xpair e1 e2 }
    | LET LANGLE x1 = ID COMMA x2 = ID RANGLE EQUAL e1 = expr IN e2 = expr
      { Xunpair x1 x2 e1 e2 }
    | RETURN e = expr
      { Xreturn e }
    | CALL foo = ID e = expr
      { Xcall foo e }
    | IFZ e1 = expr THEN e2 = expr ELSE e3 = expr
      { Xifz e1 e2 e3 }
    | ABORT
      { Xabort }



