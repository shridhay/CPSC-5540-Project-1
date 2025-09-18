{
module Parser.Parser (parseProg) where

import Language
import Parser.Lexer
}

%name parse1
%tokentype { Token }
%error { parseError }
%monad { Maybe } { >>= } { return }

%token
    int         { TokenInt $$ }
    name        { TokenName $$ }
    '['         { TokenSymb "[" }
    ']'         { TokenSymb "]" }
    '+'         { TokenSymb "+" }
    '-'         { TokenSymb "-" }
    '*'         { TokenSymb "*" }
    '/'         { TokenSymb "/" }
    '%'         { TokenSymb "%" }
    '('         { TokenSymb "(" }
    ')'         { TokenSymb ")" }
    
    '='         { TokenSymb "=" }
    "!="        { TokenSymb "!=" }
    "<="        { TokenSymb "<=" }
    ">="        { TokenSymb ">=" }
    '<'         { TokenSymb "<" }
    '>'         { TokenSymb ">" }
    '!'         { TokenSymb "!" }
    "==>"       { TokenSymb "==>" }
    
    "||"        { TokenSymb "||" }
    "&&"        { TokenSymb "&&" }

    ":="        { TokenSymb ":=" }
    ','         { TokenSymb "," }
    ';'         { TokenSymb ";" }
    "if"        { TIf }
    "then"      { TThen }
    "else"      { TElse }
    "end"       { TEnd }
    "while"     { TWhile }
    "do"        { TDo }
    "inv"       { TInv }
    "pre"       { TPre }
    "post"      { TPost }
    "forall"    { TForall }
    "exists"    { TExists }
    "program"   { TProgram }
    "is"        { TIs }


%left '+' '-'
%left '*' '/' '%'

%nonassoc "exists"
%nonassoc "forall"
%right "==>"

%left "||"
%left "&&"
%left '!'

%%

prog :: { Program }
     : "program" name pres posts "is" block "end" { ($2, $3, $4, $6) }

arithExp :: { ArithExp }
         : int { Num $1 }
         | name { Var $1 }
         | '-' arithExp { Sub (Num 0) $2 }
         | name '[' arithExp ']' { Read $1 $3 }
         | arithExp '+' arithExp { Add $1 $3 }
         | arithExp '-' arithExp { Sub $1 $3 }
         | arithExp '*' arithExp { Mul $1 $3 }
         | arithExp '/' arithExp { Div $1 $3 }
         | arithExp '%' arithExp { Mod $1 $3 }
         | '(' arithExp ')'      { Parens $2 }

comp :: { Comparison }
     : arithExp '=' arithExp { Eq $1 $3 }
     | arithExp "!=" arithExp { Neq $1 $3 }
     | arithExp "<=" arithExp { Le $1 $3 }
     | arithExp ">=" arithExp { Ge $1 $3 }
     | arithExp '<' arithExp { Lt $1 $3 }
     | arithExp '>' arithExp { Gt $1 $3 }

boolExp :: { BoolExp }
        : comp { BCmp $1 }
        | '!' boolExp { BNot $2 }
        | boolExp "||" boolExp { BDisj $1 $3 }
        | boolExp "&&" boolExp { BConj $1 $3 }
        | '(' boolExp ')' { BParens $2 }

binders :: { [String] }
        : name { [$1] }
        | binders name { $2 : $1 }

assn :: { Assertion }
     : comp { ACmp $1 }
     | '!' assn { ANot $2 }
     | assn "||" assn { ADisj $1 $3 }
     | assn "&&" assn { AConj $1 $3 }
     | assn "==>" assn { AImpl $1 $3 }
     | "forall" binders ',' assn { AForall $2 $4 }
     | "exists" binders ',' assn { AExists $2 $4 }
     | '(' assn ')' { AParens $2 }

pre :: { Assertion }
    : "pre" assn { $2 }
pres_rev :: { [Assertion] }
         : { [] }
         | pre { [$1] }
         | pres_rev pre { $2 : $1 }
pres :: { [Assertion] }
     : pres_rev { reverse $1 }

post :: { Assertion }
     : "post" assn { $2 }
posts_rev :: { [Assertion] }
          : { [] }
          | post { [$1] }
          | posts_rev post { $2 : $1 }
posts :: { [Assertion] }
      : posts_rev { reverse $1 }

inv :: { Assertion }
    : "inv" assn { $2 }
invs_rev :: { [Assertion] }
     : { [] }
     | inv { [$1] }
     | invs_rev inv { $2 : $1 }
invs :: { [Assertion] }
     : invs_rev { reverse $1 }

stmt :: { Statement }
     : name ":=" arithExp ';' { Assign $1 $3 }
     | name ',' name ":=" arithExp ',' arithExp ';' { ParAssign $1 $3 $5 $7 }
     | name '[' arithExp ']' ":=" arithExp ';' { Write $1 $3 $6 }
     | "if" boolExp "then" block "else" block "end" { If $2 $4 $6 }
     | "if" boolExp "then" block "end" { If $2 $4 [] }
     | "while" boolExp invs "do" block "end" { While $2 $3 $5 }

block :: { Block }
      : block_rev { reverse $1 }

block_rev :: { Block }
          : { [] }
	  | stmt { [$1] }
          | block_rev stmt {$2:$1}

{
parseProg :: String -> Maybe Program
parseProg = parse1 . lexProg

parseError :: [Token] -> Maybe a
parseError _ = Nothing
}
