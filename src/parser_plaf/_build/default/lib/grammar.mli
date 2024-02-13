
(* The type of tokens. *)

type token = 
  | UNPAIR
  | UNITTYPE
  | UNIONSET
  | TREETYPE
  | TOPQ
  | TOP
  | TL
  | TIMES
  | THEN
  | SUPER
  | SUM
  | SND
  | SIZE
  | SETTYPE
  | SETREF
  | SET
  | SEND
  | SEMICOLON
  | SELF
  | RRANGLE
  | RPAREN
  | REMOVEQ
  | REMOVEHTBL
  | REFTYPE
  | RBRACE
  | RANGLE
  | QUEUETYPE
  | PUSH
  | PROD
  | PROC
  | POP
  | PLUS
  | PAIR
  | OF
  | NODE
  | NEWREF
  | NEW
  | MKSET
  | MKLIST
  | MINUS
  | MIN
  | METHOD
  | MAXL
  | LPAREN
  | LOOKUPHTBL
  | LLANGLE
  | LISTTYPE
  | LETREC
  | LET
  | LBRACE
  | LANGLE
  | ISZERO
  | ISSUBSET
  | ISNUMBER
  | ISMEMBER
  | ISEMPTY
  | INTTYPE
  | INTERFACE
  | INT of (int)
  | INSTANCEOF
  | INSERTSET
  | INSERTHTBL
  | IN
  | IMPLEMENTS
  | IF
  | ID of (string)
  | HTBLTYPE
  | HD
  | FST
  | FIELD
  | EXTENDS
  | EQUALSMUTABLE
  | EQUALS
  | EOF
  | END
  | EMPTYTREE
  | EMPTYSTACK
  | EMPTYSET
  | EMPTYQUEUE
  | EMPTYLIST
  | EMPTYHTBL
  | ELSE
  | DOT
  | DIVIDED
  | DEREF
  | DEBUG
  | CONS
  | COMMA
  | COLON
  | CLASS
  | CAST
  | CASET
  | BOOLTYPE
  | BEGIN
  | AVG
  | ARROW
  | ADDQ
  | ABS

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.prog)
