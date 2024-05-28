import Clear.Ast
import Mathlib.Lean.Expr
import Lean.Parser

namespace Clear.YulNotation

open Ast Lean Parser

def yulKeywords := ["let", "if", "default", "switch", "case"]

def idFirstChar : Array Char := Id.run <| do
  let mut arr := #[]
  for i in [0:26] do
    arr := arr.push (Char.ofNat ('a'.toNat + i))
  for i in [0:26] do
    arr := arr.push (Char.ofNat ('A'.toNat + i))
  arr := (arr.push '_').push '$'
  return arr

def idSubsequentChar : Array Char := Id.run <| do
  let mut arr := idFirstChar
  for i in [0:10] do
    arr := arr.push (Char.ofNat ('0'.toNat + i))
  return arr.push '.'

def idFn : ParserFn := fun c s => Id.run do
  let input := c.input
  let start := s.pos
  if h : input.atEnd start then
    s.mkEOIError
  else
    let fst := input.get' start h
    if not (idFirstChar.contains fst) then
      return s.mkError "yul identifier"
    let s := takeWhileFn idSubsequentChar.contains c (s.next input start)
    let stop := s.pos
    let name := .str .anonymous (input.extract start stop)
    if yulKeywords.contains name.getString then
      return s.mkError "yul identifier"
    mkIdResult start none name c s

def idNoAntiquot : Parser := { fn := idFn }

section
open PrettyPrinter Parenthesizer Syntax.MonadTraverser Formatter

@[combinator_formatter idNoAntiquot]
def idNoAntiquot.formatter : Formatter := do
  Formatter.checkKind identKind
  let Syntax.ident info _ idn _ ← getCur
    | throwError m!"not an ident: {← getCur}"
  Formatter.pushToken info idn.toString
  goLeft

@[combinator_parenthesizer idNoAntiquot]
def idNoAntiquot.parenthesizer := Parenthesizer.visitToken
end

@[run_parser_attribute_hooks]
def ident : Parser := withAntiquot (mkAntiquot "ident" identKind) idNoAntiquot

declare_syntax_cat expr
declare_syntax_cat stmt

syntax identifier_list := ident,*
syntax typed_identifier_list := ident,*
syntax function_call := ident "(" expr,* ")"
syntax block := "{" stmt* "}"
syntax if' := "if" expr block
syntax function_definition :=
  "function" ident "(" typed_identifier_list ")"
    ("->" typed_identifier_list)?
    block
syntax params_list := "[" typed_identifier_list "]"
syntax variable_declaration := "let" ident (":=" expr)?
-- syntax let_str_literal := "let" ident ":=" str -- TODO(fix)
syntax variable_declarations := "let" typed_identifier_list (":=" expr)?
syntax for_loop := "for" block expr block block
syntax assignment := identifier_list ":=" expr

syntax stmtlist := stmt*

syntax block : stmt
syntax if' : stmt
syntax function_definition : stmt
syntax variable_declarations : stmt
syntax assignment : stmt
syntax expr : stmt
-- syntax let_str_literal : stmt -- TODO(fix)
syntax for_loop : stmt
syntax "break" : stmt
syntax "continue" : stmt
syntax "leave" : stmt

syntax ident : expr
syntax numLit : expr
syntax function_call: expr

syntax default := "default" "{" stmt* "}"
syntax case := "case" expr "{" stmt* "}"
syntax switch := "switch" expr case+ (default)?
syntax switch_default := "switch" expr default

syntax switch : stmt
syntax switch_default : stmt

scoped syntax:max "<<" expr ">>" : term
scoped syntax:max "<f" function_definition ">" : term
scoped syntax:max "<s" stmt ">" : term
scoped syntax:max "<ss" stmt ">" : term
scoped syntax:max "<params" params_list ">" : term

partial def translatePrimOp' (primOp : P) : TSyntax `term :=
  Syntax.mkStrLit primOp.toString 

partial def translateIdent (idn : TSyntax `ident) : TSyntax `term :=
  Syntax.mkStrLit idn.getId.getString

open P in
def parseFunction : String → PrimOp ⊕ Identifier
  | "add" => .inl Add
  | "sub" => .inl Sub
  | "mul" => .inl Mul
  | "div" => .inl Div
  | "sdiv" => .inl Sdiv
  | "mod" => .inl Mod
  | "smod" => .inl Smod
  | "addmod" => .inl Addmod
  | "mulmod" => .inl Mulmod
  | "exp" => .inl Exp
  | "signextend" => .inl Signextend
  | "lt" => .inl Lt
  | "gt" => .inl Gt
  | "slt" => .inl Slt
  | "sgt" => .inl Sgt
  | "eq" => .inl Eq
  | "iszero" => .inl Iszero
  | "and" => .inl And
  | "or" => .inl Or
  | "xor" => .inl Xor
  | "not" => .inl Not
  | "byte" => .inl Byte
  | "shl" => .inl Shl
  | "shr" => .inl Shr
  | "sar" => .inl Sar
  | "keccak256" => .inl Keccak256
  | "address" => .inl Address
  | "balance" => .inl Balance
  | "origin" => .inl Origin
  | "caller" => .inl Caller
  | "callvalue" => .inl Callvalue
  | "calldataload" => .inl Calldataload
  | "calldatacopy" => .inl Calldatacopy
  | "calldatasize" => .inl Calldatasize
  | "codesize" => .inl Codesize
  | "codecopy" => .inl Codecopy
  | "gasprice" => .inl Gasprice
  | "extcodesize" => .inl Extcodesize
  | "extcodecopy" => .inl Extcodecopy
  | "extcodehash" => .inl Extcodehash
  | "returndatasize" => .inl Returndatasize
  | "returndatacopy" => .inl Returndatacopy
  | "blockhash" => .inl Blockhash
  | "coinbase" => .inl Coinbase
  | "timestamp" => .inl Timestamp
  | "gaslimit" => .inl Gaslimit
  | "chainid" => .inl Chainid
  | "selfbalance" => .inl Selfbalance
  | "mload" => .inl Mload
  | "mstore" => .inl Mstore
  | "sload" => .inl Sload
  | "sstore" => .inl Sstore
  | "msize" => .inl Msize
  | "gas" => .inl Gas
  | "revert" => .inl Revert
  | "return" => .inl Return
  | "pop" => .inl Pop
  | "call" => .inl Call
  | "staticcall" => .inl Staticcall
  | "delegatecall" => .inl Delegatecall
  | "loadimmutable" => .inl Loadimmutable
  | "log1" => .inl Log1
  | "log2" => .inl Log2
  | "log3" => .inl Log3
  | "log4" => .inl Log4
  | "number" => .inl Number
  | userF => .inr userF 

partial def translateExpr (expr : TSyntax `expr) : MacroM (TSyntax `term) :=
  match expr with
  | `(expr| $idn:ident) => `(Expr.Var $(translateIdent idn))
  | `(expr| $num:num) => `(Expr.Lit $num)
  | `(expr| $name:ident($args:expr,*)) => do
    let args' ← (args : TSyntaxArray `expr).mapM translateExpr
    let f' := parseFunction (TSyntax.getId name).getString
    match f' with
      | .inl primOp =>
        let primOp' := Lean.mkIdent (Name.fromComponents [`P, primOp.toString.toName])
        `(Expr.PrimCall $primOp' [$args',*])
      | .inr _ =>
        `(Expr.Call $name [$args',*])
  | _ => Macro.throwError "unknown expr"

partial def translateExpr' (expr : TSyntax `expr) : MacroM (TSyntax `term) :=
  match expr with
  | `(expr| $num:num) => `($num)
  | exp => translateExpr exp

partial def translateParamsList
  (params : TSyntax `Clear.YulNotation.params_list)
: MacroM (TSyntax `term) :=
  match params with
  | `(params_list| [ $args:ident,* ]) => do
    let args' := (args : TSyntaxArray _).map translateIdent
    `([$args',*])
  | _ => Macro.throwError (toString params.raw)

mutual
partial def translateFdef
  (fdef : TSyntax `Clear.YulNotation.function_definition)
: MacroM (TSyntax `term) :=
  match fdef with
  | `(function_definition| function $_:ident($args:ident,*) {$body:stmt*}) => do
    let args' := (args : TSyntaxArray _).map translateIdent
    let body' ← body.mapM translateStmt
    `(Clear.Ast.FunctionDefinition.Def [$args',*] [] [$body',*])
  | `(function_definition| function $_:ident($args:ident,*) -> $rets,* {$body:stmt*}) => do
    let args' := (args : TSyntaxArray _).map translateIdent
    let rets' := (rets : TSyntaxArray _).map translateIdent
    let body' ← body.mapM translateStmt
    `(Clear.Ast.FunctionDefinition.Def [$args',*] [$rets',*] [$body',*])
  | _ => Macro.throwError (toString fdef.raw)

partial def translateStmt (stmt : TSyntax `stmt) : MacroM (TSyntax `term) :=
  match stmt with

  -- Block
  | `(stmt| {$stmts:stmt*}) => do
    let stmts' ← stmts.mapM translateStmt
    `(Stmt.Block ([$stmts',*]))

  -- If
  | `(stmt| if $cond:expr {$body:stmt*}) => do
    let cond' ← translateExpr cond
    let body' ← body.mapM translateStmt
    `(Stmt.If $cond' [$body',*])

  -- Function Definition
  | `(stmt| $fdef:function_definition) => do
    let fdef' ← translateFdef fdef
    `(Stmt.FunctionDefinition $fdef')

  -- Switch
  | `(stmt| switch $expr:expr $[case $lits { $cs:stmt* }]* $[default { $dflts:stmt* }]?) => do
    let expr ← translateExpr expr
    let lits ← lits.mapM translateExpr'
    let cases ← cs.mapM (λ cc ↦ cc.mapM translateStmt)
    let f (litCase : TSyntax `term × Array (TSyntax `term)) : MacroM (TSyntax `term) := do
      let (lit, cs) := litCase; `(($lit, [$cs,*]))
    let switchCases ← lits.zip cases |>.mapM f
    let dflt ← match dflts with
                 | .none => `([.Break])
                 | .some dflts => `([$(←dflts.mapM translateStmt),*])
    `(Stmt.Switch $expr [$switchCases,*] $dflt)

  -- Switch
  | `(stmt| switch $expr:expr default {$dflts:stmt*}) => do
    let expr ← translateExpr expr
    let dflt ← dflts.mapM translateStmt
    `(Stmt.Switch $expr [] ([$dflt,*]))
  
  -- LetCall
  | `(stmt| let $ids:ident,* := $f:ident ( $es:expr,* )) => do
    let ids' := (ids : TSyntaxArray _).map translateIdent
    let f' := parseFunction (TSyntax.getId f).getString
    let es' ← (es : TSyntaxArray _).mapM translateExpr
    match f' with
      | .inl primOp =>
        let primOp' := Lean.mkIdent (Name.fromComponents [`P, primOp.toString.toName])
        `(Stmt.LetPrimCall [$ids',*] $primOp' [$es',*])
      | .inr _ =>
        `(Stmt.LetCall [$ids',*] $f [$es',*])

  -- LetEq
  | `(stmt| let $idn:ident := $init:expr) => do
    let idn' := translateIdent idn
    let expr' ← translateExpr init
    `(Stmt.LetEq $idn' $expr')

  -- TODO(fix)
  -- | `(stmt| let $idn:ident := $s:str) => do
  --   let idn' := translateIdent idn
  --   `(Stmt.LetEq $idn' _)

  -- Let
  | `(stmt| let $ids:ident,*) => do
    let ids' := (ids : TSyntaxArray _).map translateIdent
    `(Stmt.Let [$ids',*])

  -- AssignCall
  | `(stmt| $ids:ident,* := $f:ident ( $es:expr,* )) => do
    let ids' := (ids : TSyntaxArray _).map translateIdent
    let f' := parseFunction (TSyntax.getId f).getString
    let es' ← (es : TSyntaxArray _).mapM translateExpr
    match f' with
      | .inl primOp =>
        let primOp' := Lean.mkIdent (Name.fromComponents [`P, primOp.toString.toName])
        `(Stmt.AssignPrimCall [$ids',*] $primOp' [$es',*])
      | .inr _ =>
        `(Stmt.AssignCall [$ids',*] $f [$es',*])

  -- Assign
  | `(stmt| $idn:ident := $init:expr) => do
    let idn' := translateIdent idn
    let expr' ← translateExpr init
    `(Stmt.Assign $idn' $expr')

  -- ExprStmt
  | `(stmt| $f:ident ( $es:expr,* )) => do
    let f' := parseFunction (TSyntax.getId f).getString
    let es' ← (es : TSyntaxArray _).mapM translateExpr
    match f' with
      | .inl primOp =>
        let primOp' := Lean.mkIdent (Name.fromComponents [`P, primOp.toString.toName])
        `(Stmt.ExprStmtPrimCall $primOp' [$es',*])
      | .inr _ =>
        `(Stmt.ExprStmtCall $f [$es',*])

  -- For
  | `(stmt| for {} $cond:expr {$post:stmt*} {$body:stmt*}) => do
    let cond' ← translateExpr cond
    let post' ← post.mapM translateStmt
    let body' ← body.mapM translateStmt
    `(Stmt.For $cond' [$post',*] [$body',*])

  -- Break
  | `(stmt| break) => `(Stmt.Break)

  -- Continue
  | `(stmt| continue) => `(Stmt.Continue)

  -- Leave
  | `(stmt| leave) => `(Stmt.Leave)

  -- Anything else
  | _ => Macro.throwError (toString stmt.raw)
end

partial def translateStmtList (stmt : TSyntax `stmt) : MacroM (TSyntax `term) :=
  match stmt with
  | `(stmt| {$stmts:stmt*}) => do
    let stmts' ← stmts.mapM translateStmt
    `([$stmts',*])
  | _ => Macro.throwError (toString stmt.raw)

scoped macro_rules
| `(term|<< $expr:expr >>) => translateExpr expr
| `(term|<f $fdef:function_definition >) => translateFdef fdef
| `(term|<s $stmt:stmt >) => translateStmt stmt
| `(term|<ss $stmt:stmt >) => translateStmtList stmt
| `(term|<params $params:params_list >) => translateParamsList params

def f : FunctionDefinition := <f
  function sort2(a, b) -> x, y {
    if lt(a, b) {
      x := a
      y := b
      leave
    }
    x := b
    y := a
  }
>

example : <params [a,b,c] > = ["a", "b", "c"] := rfl
example : << bar >> = Expr.Var "bar" := rfl
example : << 42 >> = Expr.Lit 42 := rfl
example : <s break > = Stmt.Break := rfl
example : <s let a, b := f(42) > = Stmt.LetCall ["a", "b"] f [Expr.Lit 42] := rfl
example : <s let a > = Stmt.Let ["a"] := rfl
example : <s let a := 5 > = Stmt.LetEq "a" (.Lit 5) := rfl
example : <s a, b := f(42) > = Stmt.AssignCall ["a", "b"] f [Expr.Lit 42] := rfl
example : <s a := 42 > = Stmt.Assign "a" (.Lit 42) := rfl
example : <s c := add(a, b) > = Stmt.AssignPrimCall ["c"] P.Add [Expr.Var "a", Expr.Var "b"] := rfl
example : <s let c := sub(a, b) > = Stmt.LetPrimCall ["c"] P.Sub [Expr.Var "a", Expr.Var "b"] := rfl
example : <s let a := 5 > = Stmt.LetEq "a" (.Lit 5) := rfl
example : <s {} >
  = Stmt.Block [] := rfl
example : <s
{
  break
  let a := 5
  break
}
> = Stmt.Block [<s break>, <s let a := 5>, <s break>] := rfl
example : <s
  if a {
    let b := 5
    break
  }
> = Stmt.If <<a>> [<s let b := 5>, <s break >] := rfl

example : <ss {
  let a
  let b
  let c
} > = [<s let a>, <s let b>, <s let c>] := rfl

example : <s for {} 0 {} {} > = Stmt.For (.Lit 0) [] [] := by rfl

example : <s
  for {} lt(i, exponent) { i := add(i, 1) }
  {
    result := mul(result, base)
  }
> = Stmt.For <<lt(i, exponent)>> [<s i := add(i, 1)>]
      [<s result := mul(result, base)>] := rfl

def sort2 : FunctionDefinition := <f
  function sort2(a, b) -> x, y {
    if lt(a, b) {
      x := a
      y := b
      leave
    }
    x := b
    y := a
  }
>
def no_rets : FunctionDefinition := <f
  function no_rets(a, b) {
  }
>
example : <s
  switch a
  case 42 { continue }
  default { break }
> = Stmt.Switch (Expr.Var "a") [(42, [.Continue])] [.Break] := rfl

example : <s let a, b, c > = Stmt.Let ["a", "b", "c"] := rfl
example : <s revert(0, 0) > = Stmt.ExprStmtPrimCall P.Revert [(Expr.Lit 0), (Expr.Lit 0)] := rfl
example : <s if 1 { leave } > = Stmt.If (.Lit 1) [Stmt.Leave] := rfl
example : <s {
    if 1 { leave }
    leave
  }
> = Stmt.Block [Stmt.If (.Lit 1) [.Leave], .Leave] := rfl

end Clear.YulNotation
