{
module Parser (calc, lexer) where

import Data.List.NonEmpty (NonEmpty (..), (<|))
import qualified Data.List.NonEmpty as NE

import Lexer (Token (..), lexer)
import Types (Identifier, Literal (..), Expr (..), FuncDef' (..), Stmt (..), TopLvlStmt (..), InnerObject (..), Object (..))
}

%name calc
%tokentype { Token }
%error { parseError }

%token
      '{'             { TokenLCurl }
      '}'             { TokenRCurl }
      '('             { TokenLPar }
      ')'             { TokenRPar }
      '->'            { TokenArrow }
      ':='            { TokenColonEq }
      ','             { TokenComma }
      ':'             { TokenColon }
      function        { TokenFunction }
      let             { TokenLet }
      if              { TokenIf }
      switch          { TokenSwitch }
      case            { TokenCase }
      default         { TokenDefault }
      for             { TokenFor }
      break           { TokenBreak }
      continue        { TokenContinue }
      leave           { TokenLeave }
      true            { TokenTrue }
      false           { TokenFalse }
      ident           { TokenIdentifier $$ }
      str             { TokenString $$ }
      hex             { TokenHex $$ }
      dec             { TokenDecimal $$ }
      inlcomment      { TokenInlineComment $$ }
      multicomment    { TokenMultilineComment $$ }
      object          { TokenObject }
      code            { TokenCode }

%%

Objects     : {- empty -}                 { [] }
            | Objects Object              { $2 : $1 }

Object      : inlcomment object str '{' Code InnerObject '}'          { Object $1 $3 $5 $6 }
            |            object str '{' Code InnerObject '}'          { Object "" $2 $4 $5 }

InnerObject : inlcomment object str '{' Code ident str ident str '}'  { InnerObject $1 $3 $5 }
            |            object str '{' Code ident str ident str '}'  { InnerObject "" $2 $4 }

Code        : code TopLvlBlock            { $2 }

Block       : '{' Statements '}'          { reverse $2 }

TopLvlBlock : '{' TopLvlStmts '}'         { reverse $2 }

Statements  : {- empty -}                 { [] }
            | Statements Statement        { $2 : $1 }

TopLvlStmts : {- empty -}                 { [] }
            | TopLvlStmts TopLvlStmt      { $2 : $1 }

TopLvlStmt  : Block                       { UnusedBlock }
            | FuncDef                     { FuncDefStmt $1 }
            | inlcomment                  { UnusedBlock }
            | multicomment                { UnusedBlock }

Statement   : Block                       { Block $1 }
            | VariableDeclaration         { let (idens, mbExpr) = $1 in
                                                case mbExpr of
                                                  Just expr -> LetInit idens expr
                                                  Nothing   -> Declaration idens
                                          }
            | Assignment                  { (uncurry Assignment) $1 }
            | If                          { (uncurry If) $1 }
            | Expression                  { ExpressionStmt $1 }
            | Switch                      { (uncurry3 Switch) $1 }
            | ForLoop                     { (uncurry4 For) $1 }
            | continue                    { Continue }
            | break                       { Break }
            | leave                       { Leave }
            | inlcomment                  { InlineComment $1 }
            | multicomment                { MultilineComment $1 }

FuncDef : function ident '(' ')' Block                                         { FuncDef' $2 [] [] $5 }
        | function ident '(' TypedIdentifiers ')' Block                        { FuncDef' $2 (reverse (NE.toList $4)) [] $6 }
        | function ident '(' ')' '->' TypedIdentifiers Block                   { FuncDef' $2 [] (reverse (NE.toList $6)) $7 }
        | function ident '(' TypedIdentifiers ')' '->' TypedIdentifiers Block  { FuncDef' $2 (reverse (NE.toList $4)) (reverse (NE.toList $7)) $8 }

VariableDeclaration : let TypedIdentifiers                  { (NE.reverse $2, Nothing) }
                    | let TypedIdentifiers ':=' Expression  { (NE.reverse $2, Just $4) }

Assignment  : Identifiers ':=' Expression { (NE.reverse $1, $3) }

Expression  : FunctionCall                { (uncurry Call) $1 }
            | ident                       { Var $1 }
            | Literal                     { Lit $1 }

If          : if Expression Block                         { ($2, $3) }
            | if multicomment Expression Block            { ($3, $4) }
            | if Expression inlcomment Block              { ($2, $4) }
            | if multicomment Expression inlcomment Block { ($3, $5) }

Switch      : switch Expression Cases          { ($2, reverse $3, []) }
            | switch Expression Cases Default  { ($2, reverse $3, $4) }
            | switch Expression Default        { ($2, [],         $3) }

Cases       : Case                        { [$1] }
            | Cases Case                  { $2 : $1 }

Case        : case Literal Block          { ($2, $3) }

Default     : default Block               { $2 }
            | default inlcomment Block    { $3 }

ForLoop     : for Block Expression Block Block    { ($2, $3, $4, $5) }

FunctionCall : ident '(' Arguments ')'    { ($1, reverse $3) }

ExpressionPrecComment : multicomment Expression { $2 }
                      |              Expression { $1 }

Arguments   : {- empty -}                         { [] }
            | ExpressionPrecComment               { [$1] }
            | Arguments ',' ExpressionPrecComment { $3 : $1 }

Identifiers : ident                       { $1 :| [] }
            | Identifiers ',' ident       { $3 <| $1 }

TypeName    : ident                       { $1 }

TypedIdentifiers : ident                                    { $1 :| [] }
                 | ident ':' TypeName                       { $1 :| [] }
                 | TypedIdentifiers ',' ident               { $3 <| $1 }
                 | TypedIdentifiers ',' ident ':' TypeName  { $3 <| $1 }

Literal     : NumberLiteral               { Number $1 }
            | NumberLiteral ':' TypeName  { Number $1 }
            | str                         { Str $1 }
            | str ':' TypeName            { Str $1 }
            | true                        { Number 1 }
            | true ':' TypeName           { Number 1 }
            | false                       { Number 0 }
            | false ':' TypeName          { Number 0 }

NumberLiteral : hex                       { (read $1) }
              | dec                       { (read $1) }

{
parseError :: [Token] -> a
parseError ts = error ("Can't parse tokens: " ++ show (take 10 ts))

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x, y, z) = f x y z

uncurry4 :: (a -> b -> c -> d -> e) -> (a, b, c, d) -> e
uncurry4 f (w, x, y, z) = f w x y z
}
