%{
open Ast
%}

%token <int> INT
%token TIMES PLUS MINUS
%token LPAREN RPAREN
%token IFZERO THEN ELSE 
%token EOF

%left PLUS
%left MINUS
%left TIMES

%start <Ast.expr> prog

%%

prog:
	| e = expr; EOF { e }
	;

expr: 
        | IFZERO; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr { IfZero(e1,e2,e3) }
        | e = bexpr { e }

bexpr:  
	| e1 = bexpr; TIMES; e2 = bexpr { Binop (Mult, e1, e2) } 
	| e1 = bexpr; PLUS; e2 = bexpr { Binop (Add, e1, e2) }
        | e1 = bexpr; MINUS; e2 = bexpr { Binop (Sub, e1, e2) }
	| e = aexpr { e }
aexpr:
	| i = INT { Int i }
	| LPAREN; e=expr; RPAREN { e } 
	;
	
