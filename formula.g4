grammar Formula;

formula: expression+ EOF;

expression
    : (TRUE | FALSE)                                                                       # booleanConstant
    | predicate (PAREN_OPEN args PAREN_CLOSE)?                                             # atom
    | PAREN_OPEN expression PAREN_CLOSE                                                    # parenthesizedExpression
    | NOT expression                                                                       # unary
    | condition = expression QUESTION truthy = expression COLON falsy = expression         # ternary
    | left = expression op = (AND | BAR | IF | IFF | THEN | XOR) right = expression        # binary
    | quantifier = (EXISTS |FORALL) variable = TVAR IN termSet scope = expression          # termQuantification
    | quantifier = (EXISTS |FORALL) variable = IVAR IN intExpressionSet scope = expression # intExpressionQuantification
    | quantifier = (EXISTS |FORALL) variable = PVAR IN predicateSet scope = expression     # predicateQuantification
    ;

predicate
    : CON  # predicateConstant
    | PVAR # predicateVariable
    ;

predicates
    : predicate (COMMA predicates)?
    ;

predicateSet
    : CURLY_OPEN predicates CURLY_CLOSE # predicateEnumeration
    ;

arg
    : term          # argTerm
    | intExpression # argIntExpression
    ;

args
    : arg (COMMA args)?
    ;

term
    : CON  # termConstant
    | TVAR # termVariable
    ;

terms
    : term (COMMA terms)?
    ;

termSet
    : CURLY_OPEN terms CURLY_CLOSE # termEnumeration
    ;

intExpressionSet
    : SQUARE_OPEN minimum = intExpression DOTS maximum = intExpression SQUARE_CLOSE # intExpressionRange
    | CURLY_OPEN intExpressions CURLY_CLOSE                                         # intExpressionEnumeration
    ;

intExpression
    : PAREN_OPEN intExpression PAREN_CLOSE                                          # parenthesizedIntExpression
    | BAR intExpression BAR                                                         # absIntExpression
    | SUB intExpression                                                             # negIntExpression
    | left = intExpression op = (MUL | DIV | MOD | ADD | SUB) right = intExpression # binaryIntExpression
    | variable = IVAR                                                               # varIntExpression
    | number = NUMBER                                                               # numIntExpression
    ;

intExpressions
    : intExpression (COMMA intExpressions)?
    ;

// Boolean constants:
TRUE        : 'true' | '⊤';
FALSE       : 'false' | '⊥';

// Quantifiers:
FORALL      : 'forall' | '∀';
EXISTS      : 'exists' | '∃';

// Parentheses and braces:
PAREN_OPEN   : '(';
PAREN_CLOSE  : ')';
CURLY_OPEN   : '{';
CURLY_CLOSE  : '}';
SQUARE_OPEN  : '[';
SQUARE_CLOSE : ']';

// Boolean connectives:
AND         : '&' | '∧';
THEN        : '->' | '→' | '⊃';
IF          : '<-' | '←' | '⊂';
IFF         : '<->' | '↔';
XOR         : '^' | '⊕';
NOT         : '~' | '¬';
QUESTION    : '?';
COLON       : ':';

// Arithmetic constants:
NUMBER      : DIGIT+;

// Arithmetic connectives:
MUL         : '*';
DIV         : '/';
MOD         : '%';
ADD         : '+';
SUB         : '-';

EQ          : '=';
NE          : '!=';
GT          : '>';
LT          : '<';
GE          : '>=';
LE          : '<=';

// Miscellaneous:
IN          : 'in' | '∈';
COMMA       : ',';
DOTS        : '...' | '…';

// NOTE: This character is used both in intExpressions
//       and as a binary boolean connective.
BAR         : '|';
fragment OR : BAR | '∨';

// Variable prefixes:
AT          : '@';
DOLLAR      : '$';
HASH        : '#';

// Drop whitespaces and comments:
WS       : [ \t\n\r]+ -> skip ;
COMMENTS : ('/*' .*? '*/' | '//' ~'\n'* '\n') -> skip;

// Constant args and elements:
CON : LOWER ALNUM*;

// Variable args and elements:
TVAR : DOLLAR ALNUM+;
PVAR : AT ALNUM+;
IVAR : HASH ALNUM+;

fragment DIGIT : '0' .. '9';
fragment UPPER : 'A' .. 'Z';
fragment LOWER : 'a' .. 'z';
fragment ALNUM : LOWER | UPPER | DIGIT;
