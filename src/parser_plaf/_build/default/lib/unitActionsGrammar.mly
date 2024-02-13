%start prog
%token ABS
%token ADDQ
%token ARROW
%token AVG
%token BEGIN
%token BOOLTYPE
%token CASET
%token CAST
%token CLASS
%token COLON
%token COMMA
%token CONS
%token DEBUG
%token DEREF
%token DIVIDED
%token DOT
%token ELSE
%token EMPTYHTBL
%token EMPTYLIST
%token EMPTYQUEUE
%token EMPTYSET
%token EMPTYSTACK
%token EMPTYTREE
%token END
%token EOF
%token EQUALS
%token EQUALSMUTABLE
%token EXTENDS
%token FIELD
%token FST
%token HD
%token HTBLTYPE
%token <string> ID
%token IF
%token IMPLEMENTS
%token IN
%token INSERTHTBL
%token INSERTSET
%token INSTANCEOF
%token <int> INT
%token INTERFACE
%token INTTYPE
%token ISEMPTY
%token ISMEMBER
%token ISNUMBER
%token ISSUBSET
%token ISZERO
%token LANGLE
%token LBRACE
%token LET
%token LETREC
%token LISTTYPE
%token LLANGLE
%token LOOKUPHTBL
%token LPAREN
%token MAXL
%token METHOD
%token MIN
%token MINUS
%token MKLIST
%token MKSET
%token NEW
%token NEWREF
%token NODE
%token OF
%token PAIR
%token PLUS
%token POP
%token PROC
%token PROD
%token PUSH
%token QUEUETYPE
%token RANGLE
%token RBRACE
%token REFTYPE
%token REMOVEHTBL
%token REMOVEQ
%token RPAREN
%token RRANGLE
%token SELF
%token SEMICOLON
%token SEND
%token SET
%token SETREF
%token SETTYPE
%token SIZE
%token SND
%token SUM
%token SUPER
%token THEN
%token TIMES
%token TL
%token TOP
%token TOPQ
%token TREETYPE
%token UNIONSET
%token UNITTYPE
%token UNPAIR
%nonassoc ELSE EQUALS EQUALSMUTABLE IN
%right ARROW
%left LLANGLE MINUS PLUS RRANGLE
%left DIVIDED TIMES
%left DOT
%nonassoc LISTTYPE REFTYPE TREETYPE
%type <unit> prog
%%

option_implements_declaration_:
  
    {} [@name none_implements_declaration]
| implements_declaration
    {} [@name some_implements_declaration]

option_texpr_:
  
    {} [@name none_texpr]
| texpr
    {} [@name some_texpr]

option_type_annotation_:
  
    {} [@name none_type_annotation]
| type_annotation
    {} [@name some_type_annotation]

loption_separated_nonempty_list_COMMA_ID__:
  
    {} [@name none_separated_nonempty_list_COMMA_ID_]
| separated_nonempty_list_COMMA_ID_
    {} [@name some_separated_nonempty_list_COMMA_ID_]

loption_separated_nonempty_list_COMMA_expr__:
  
    {} [@name none_separated_nonempty_list_COMMA_expr_]
| separated_nonempty_list_COMMA_expr_
    {} [@name some_separated_nonempty_list_COMMA_expr_]

loption_separated_nonempty_list_COMMA_formal_par__:
  
    {} [@name none_separated_nonempty_list_COMMA_formal_par_]
| separated_nonempty_list_COMMA_formal_par_
    {} [@name some_separated_nonempty_list_COMMA_formal_par_]

loption_separated_nonempty_list_SEMICOLON_expr__:
  
    {} [@name none_separated_nonempty_list_SEMICOLON_expr_]
| separated_nonempty_list_SEMICOLON_expr_
    {} [@name some_separated_nonempty_list_SEMICOLON_expr_]

loption_separated_nonempty_list_SEMICOLON_field__:
  
    {} [@name none_separated_nonempty_list_SEMICOLON_field_]
| separated_nonempty_list_SEMICOLON_field_
    {} [@name some_separated_nonempty_list_SEMICOLON_field_]

loption_separated_nonempty_list_SEMICOLON_fieldtype__:
  
    {} [@name none_separated_nonempty_list_SEMICOLON_fieldtype_]
| separated_nonempty_list_SEMICOLON_fieldtype_
    {} [@name some_separated_nonempty_list_SEMICOLON_fieldtype_]

list_abstract_method_decl_:
  
    {} [@name nil_abstract_method_decl]
| abstract_method_decl list_abstract_method_decl_
    {} [@name cons_abstract_method_decl]

list_iface_or_class_decl_:
  
    {} [@name nil_iface_or_class_decl]
| iface_or_class_decl list_iface_or_class_decl_
    {} [@name cons_iface_or_class_decl]

list_method_decl_:
  
    {} [@name nil_method_decl]
| method_decl list_method_decl_
    {} [@name cons_method_decl]

list_obj_fields_:
  
    {} [@name nil_obj_fields]
| obj_fields list_obj_fields_
    {} [@name cons_obj_fields]

nonempty_list_rdecs_:
  rdecs
    {} [@name one_rdecs]
| rdecs nonempty_list_rdecs_
    {} [@name more_rdecs]

separated_nonempty_list_COMMA_ID_:
  ID
    {} [@name one_COMMA_ID]
| ID COMMA separated_nonempty_list_COMMA_ID_
    {} [@name more_COMMA_ID]

separated_nonempty_list_COMMA_expr_:
  expr
    {} [@name one_COMMA_expr]
| expr COMMA separated_nonempty_list_COMMA_expr_
    {} [@name more_COMMA_expr]

separated_nonempty_list_COMMA_formal_par_:
  formal_par
    {} [@name one_COMMA_formal_par]
| formal_par COMMA separated_nonempty_list_COMMA_formal_par_
    {} [@name more_COMMA_formal_par]

separated_nonempty_list_SEMICOLON_expr_:
  expr
    {} [@name one_SEMICOLON_expr]
| expr SEMICOLON separated_nonempty_list_SEMICOLON_expr_
    {} [@name more_SEMICOLON_expr]

separated_nonempty_list_SEMICOLON_field_:
  field
    {} [@name one_SEMICOLON_field]
| field SEMICOLON separated_nonempty_list_SEMICOLON_field_
    {} [@name more_SEMICOLON_field]

separated_nonempty_list_SEMICOLON_fieldtype_:
  fieldtype
    {} [@name one_SEMICOLON_fieldtype]
| fieldtype SEMICOLON separated_nonempty_list_SEMICOLON_fieldtype_
    {} [@name more_SEMICOLON_fieldtype]

prog:
  list_iface_or_class_decl_ expr EOF
    {}

expr:
  INT
    {}
| ID
    {}
| DEBUG LPAREN expr RPAREN
    {}
| expr PLUS expr
    {}
| expr MINUS expr
    {}
| expr TIMES expr
    {}
| expr DIVIDED expr
    {}
| ABS LPAREN expr RPAREN
    {}
| MIN LPAREN expr COMMA expr RPAREN
    {}
| SUM LPAREN loption_separated_nonempty_list_COMMA_expr__ RPAREN
    {}
| PROD LPAREN loption_separated_nonempty_list_COMMA_expr__ RPAREN
    {}
| AVG LPAREN loption_separated_nonempty_list_COMMA_expr__ RPAREN
    {}
| MAXL LPAREN loption_separated_nonempty_list_COMMA_expr__ RPAREN
    {}
| PAIR LPAREN expr COMMA expr RPAREN
    {}
| FST LPAREN expr RPAREN
    {}
| SND LPAREN expr RPAREN
    {}
| LET ID EQUALS expr IN expr
    {}
| LETREC nonempty_list_rdecs_ IN expr
    {}
| PROC LPAREN ID option_type_annotation_ RPAREN LBRACE expr RBRACE
    {}
| LPAREN expr expr RPAREN
    {}
| ISZERO LPAREN expr RPAREN
    {}
| ISNUMBER LPAREN expr RPAREN
    {}
| expr EQUALS expr
    {}
| expr RRANGLE expr
    {}
| expr LLANGLE expr
    {}
| NEWREF LPAREN expr RPAREN
    {}
| DEREF LPAREN expr RPAREN
    {}
| SETREF LPAREN expr COMMA expr RPAREN
    {}
| IF expr THEN expr ELSE expr
    {}
| SET ID EQUALS expr
    {}
| BEGIN loption_separated_nonempty_list_SEMICOLON_expr__ END
    {}
| LPAREN expr RPAREN
    {}
| LPAREN MINUS expr RPAREN
    {}
| LPAREN RPAREN
    {}
| LPAREN expr COMMA expr RPAREN
    {}
| UNPAIR LPAREN ID COMMA ID RPAREN EQUALS expr IN expr
    {}
| LANGLE loption_separated_nonempty_list_COMMA_expr__ RANGLE
    {}
| LET LANGLE loption_separated_nonempty_list_COMMA_ID__ RANGLE EQUALS expr IN expr
    {}
| EMPTYTREE LPAREN option_texpr_ RPAREN
    {}
| NODE LPAREN expr COMMA expr COMMA expr RPAREN
    {}
| CASET expr OF LBRACE EMPTYTREE LPAREN RPAREN ARROW expr COMMA NODE LPAREN ID COMMA ID COMMA ID RPAREN ARROW expr RBRACE
    {}
| LBRACE loption_separated_nonempty_list_SEMICOLON_field__ RBRACE
    {}
| expr DOT ID
    {}
| expr DOT ID EQUALSMUTABLE expr
    {}
| NEW ID LPAREN loption_separated_nonempty_list_COMMA_expr__ RPAREN
    {}
| SELF
    {}
| SEND expr ID LPAREN loption_separated_nonempty_list_COMMA_expr__ RPAREN
    {}
| SUPER ID LPAREN loption_separated_nonempty_list_COMMA_expr__ RPAREN
    {}
| MKLIST LPAREN loption_separated_nonempty_list_COMMA_expr__ RPAREN
    {}
| EMPTYLIST LPAREN option_texpr_ RPAREN
    {}
| HD LPAREN expr RPAREN
    {}
| TL LPAREN expr RPAREN
    {}
| ISEMPTY LPAREN expr RPAREN
    {}
| CONS LPAREN expr COMMA expr RPAREN
    {}
| INSTANCEOF LPAREN expr COMMA ID RPAREN
    {}
| CAST LPAREN expr COMMA ID RPAREN
    {}
| MKSET LPAREN loption_separated_nonempty_list_COMMA_expr__ RPAREN
    {}
| EMPTYSET LPAREN option_texpr_ RPAREN
    {}
| INSERTSET LPAREN expr COMMA expr RPAREN
    {}
| UNIONSET LPAREN expr COMMA expr RPAREN
    {}
| ISSUBSET LPAREN expr COMMA expr RPAREN
    {}
| ISMEMBER LPAREN expr COMMA expr RPAREN
    {}
| SIZE LPAREN expr RPAREN
    {}
| EMPTYSTACK LPAREN option_texpr_ RPAREN
    {}
| PUSH LPAREN expr COMMA expr RPAREN
    {}
| POP LPAREN expr RPAREN
    {}
| TOP LPAREN expr RPAREN
    {}
| EMPTYQUEUE LPAREN option_texpr_ RPAREN
    {}
| ADDQ LPAREN expr COMMA expr RPAREN
    {}
| REMOVEQ LPAREN expr RPAREN
    {}
| TOPQ LPAREN expr RPAREN
    {}
| EMPTYHTBL LPAREN RPAREN
    {}
| EMPTYHTBL LPAREN texpr COMMA texpr RPAREN
    {}
| INSERTHTBL LPAREN expr COMMA expr COMMA expr RPAREN
    {}
| LOOKUPHTBL LPAREN expr COMMA expr RPAREN
    {}
| REMOVEHTBL LPAREN expr COMMA expr RPAREN
    {}

rdecs:
  ID LPAREN ID option_type_annotation_ RPAREN option_type_annotation_ EQUALS expr
    {}

type_annotation:
  COLON texpr
    {}

field:
  ID EQUALS expr
    {}
| ID EQUALSMUTABLE expr
    {}

fieldtype:
  ID COLON texpr
    {}

iface_or_class_decl:
  CLASS ID EXTENDS ID option_implements_declaration_ LBRACE list_obj_fields_ list_method_decl_ RBRACE
    {}
| INTERFACE ID LBRACE list_abstract_method_decl_ RBRACE
    {}

implements_declaration:
  IMPLEMENTS ID
    {}

obj_fields:
  FIELD ID
    {}
| FIELD texpr ID
    {}

method_decl:
  METHOD ID LPAREN loption_separated_nonempty_list_COMMA_formal_par__ RPAREN LBRACE expr RBRACE
    {}
| METHOD texpr ID LPAREN loption_separated_nonempty_list_COMMA_formal_par__ RPAREN LBRACE expr RBRACE
    {}

abstract_method_decl:
  METHOD texpr ID LPAREN loption_separated_nonempty_list_COMMA_formal_par__ RPAREN
    {}

formal_par:
  ID option_type_annotation_
    {}

texpr:
  ID
    {}
| INTTYPE
    {}
| BOOLTYPE
    {}
| UNITTYPE
    {}
| texpr ARROW texpr
    {}
| texpr TIMES texpr
    {}
| LPAREN texpr RPAREN
    {}
| REFTYPE texpr
    {}
| TREETYPE texpr
    {}
| LISTTYPE texpr
    {}
| SETTYPE LPAREN texpr RPAREN
    {}
| QUEUETYPE LPAREN texpr RPAREN
    {}
| HTBLTYPE LPAREN texpr COMMA texpr RPAREN
    {}
| LBRACE loption_separated_nonempty_list_SEMICOLON_fieldtype__ RBRACE
    {}

%%
