%{
open Types

let elaborate_schema foralls typ =
  let rec help typ =
    match typ with
    | TyCon _ -> typ
    | TyVar(name) -> if List.mem name primitive_typs then TyCon(name) else typ
    | TyArr(args, ret) -> TyArr(List.map help args, help ret)
    | TyTup(args) -> TyTup(List.map help args)
  in (foralls, help typ)
;;
%}

%token <int> NUM
%token <string> ID
%token LBRACK RBRACK DEF ADD1 SUB1 LPAREN RPAREN LET REC IN EQUAL COMMA PLUS MINUS TIMES IF COLON ELSECOLON TRUE FALSE ISBOOL ISNUM ISTUPLE LAMBDA EQEQ LESS GREATER PRINT PRINTSTACK EOF LESSEQ GREATEREQ AND OR NOT GETS BEGIN END SEMI ARROW

%left LPAREN
%left PLUS MINUS TIMES GREATER LESS EQEQ LESSEQ GREATEREQ AND OR


%type <(Lexing.position * Lexing.position) Types.program> program

%start program

%%

const :
  | NUM { ENumber($1, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | TRUE { EBool(true, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | FALSE { EBool(false, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

prim1 :
  | ADD1 { Add1 }
  | SUB1 { Sub1 }
  | NOT { Not }
  | PRINT { Print }
  | ISBOOL { IsBool }
  | ISNUM { IsNum }
  | ISTUPLE { IsTuple }
  | PRINTSTACK { PrintStack }

binds :
  | ID tyann EQUAL expr { [($1, $2, $4, (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1))] }
  | ID tyann EQUAL expr COMMA binds { ($1, $2, $4, (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1))::$6 }

tyann :
  | { None }
  | COLON schema { Some $2 }

schema :
  | LBRACK ids RBRACK typ { elaborate_schema (List.map fst $2) $4 }
  | typ { elaborate_schema [] $1 }

typ :
  | ID { TyVar $1 }
  | LPAREN typ typs ARROW typ RPAREN { TyArr($2::$3, $5) }
  | LPAREN typ typs RPAREN { TyTup ($2::$3) }

typs :
  | { [] }
  | COMMA typ typs { $2 :: $3 }

ids :
  | ID { [$1, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())] }
  | ID COMMA ids { ($1, (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1))::$3 }

exprs :
  | expr { [$1] }
  | expr COMMA exprs { $1::$3 }

tuple_exprs :
  | expr COMMA { [$1] }
  | expr COMMA exprs { $1::$3 }

colon_num:
  | COLON NUM COLON { $2 }

simple_expr :
  | prim1 LPAREN expr RPAREN { EPrim1($1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPAREN tuple_exprs RPAREN { ETuple($2, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPAREN expr RPAREN { $2 }
  | simple_expr LPAREN exprs RPAREN { EApp($1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | simple_expr LPAREN RPAREN { EApp($1, [], (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPAREN LAMBDA ids COLON expr RPAREN { ELambda($3, $5, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPAREN LAMBDA COLON expr RPAREN { ELambda([], $4, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | simple_expr LBRACK expr RBRACK { EGetItem($1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | simple_expr LBRACK expr RBRACK GETS expr { ESetItem($1, $3, $6, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | simple_expr LBRACK colon_num RBRACK { EGetItemExact($1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | simple_expr LBRACK colon_num RBRACK GETS expr { ESetItemExact($1, $3, $6, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | BEGIN block_exprs END { ESeq($2, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | const { $1 }
  | ID { EId($1, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

block_exprs :
  | expr { [$1] }
  | expr SEMI { [$1] }
  | expr SEMI block_exprs { $1::$3 }


binop:
  | PLUS { Plus }
  | MINUS { Minus }
  | TIMES { Times }
  | EQEQ { Eq }
  | LESS { Less }
  | GREATER { Greater }
  | LESSEQ { LessEq }
  | GREATEREQ { GreaterEq }
  | AND { And }
  | OR { Or }

binop_expr :
  | binop_expr binop binop_expr { EPrim2($2, $1, $3, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | simple_expr { $1 }

expr :
  | LET binds IN expr { ELet($2, $4, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LET REC binds IN expr { ELetRec($3, $5, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | IF expr COLON expr ELSECOLON expr { EIf($2, $4, $6, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | binop_expr { $1 }

program : expr EOF { $1 }

%%
