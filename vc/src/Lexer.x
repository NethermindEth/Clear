{
module Lexer (Token (..), lexer) where

import Data.List (dropWhileEnd)
}

%wrapper "posn"

tokens :-
  $white+                           ;
  "{"                               { \_ _ -> TokenLCurl }
  "}"                               { \_ _ -> TokenRCurl }
  "("                               { \_ _ -> TokenLPar }
  ")"                               { \_ _ -> TokenRPar }
  "->"                              { \_ _ -> TokenArrow }
  ":="                              { \_ _ -> TokenColonEq }
  ","                               { \_ _ -> TokenComma }
  ":"                               { \_ _ -> TokenColon }
  function                          { \_ _ -> TokenFunction }
  let                               { \_ _ -> TokenLet }
  if                                { \_ _ -> TokenIf }
  switch                            { \_ _ -> TokenSwitch }
  case                              { \_ _ -> TokenCase }
  default                           { \_ _ -> TokenDefault }
  for                               { \_ _ -> TokenFor }
  break                             { \_ _ -> TokenBreak }
  continue                          { \_ _ -> TokenContinue }
  leave                             { \_ _ -> TokenLeave }
  true                              { \_ _ -> TokenTrue }
  false                             { \_ _ -> TokenFalse }
  object                            { \_ _ -> TokenObject }
  code                              { \_ _ -> TokenCode }
  [a-zA-Z\_\$]+ [a-zA-Z\_\$0-9\.]*  { \_ s -> TokenIdentifier s}
  \" ([^\"\r\n\\] | '\\' .)* \"     { \_ s -> TokenString (trimQuotes s) }
  0x [0-9a-fA-F]+                   { \_ s -> TokenHex s }
  [0-9]+                            { \_ s -> TokenDecimal s }
  "///" .*$                         { \_ s -> TokenInlineComment s }
  "/**" [.]* "*/"                   ;

{
lexer :: String -> [Token]
lexer = alexScanTokens

trimQuotes :: String -> String
trimQuotes = dropWhileEnd (== '"') . dropWhile (== '"')

data Token
      = TokenLCurl
      | TokenRCurl
      | TokenLPar
      | TokenRPar
      | TokenArrow
      | TokenColonEq
      | TokenComma
      | TokenColon
      | TokenFunction
      | TokenLet
      | TokenIf
      | TokenSwitch
      | TokenCase
      | TokenDefault
      | TokenFor
      | TokenBreak
      | TokenContinue
      | TokenLeave
      | TokenTrue
      | TokenFalse
      | TokenObject
      | TokenCode
      | TokenIdentifier String
      | TokenString String
      | TokenHex String
      | TokenDecimal String
      | TokenInlineComment String
      | TokenMultilineComment String
  deriving Show
}
