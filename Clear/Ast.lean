/- Yul specification:
https://docs.soliditylang.org/en/v0.8.9/yul.html
-/

import Batteries.Tactic.Basic
import Mathlib.Data.Fin.Basic
import Clear.UInt256

namespace Clear.Ast

open Clear UInt256

abbrev Literal := UInt256
def Identifier := String

instance : Inhabited Identifier := ⟨""⟩
instance : DecidableEq Identifier := String.decEq

inductive P where
  | Add
  | Sub
  | Mul
  | Div
  | Sdiv
  | Mod
  | Smod
  | Addmod
  | Mulmod
  | Exp
  | Signextend
  | Lt
  | Gt
  | Slt
  | Sgt
  | Eq
  | Iszero
  | And
  | Or
  | Xor
  | Not
  -- Rename to `Byteat`?
  | Byte
  | Shl
  | Shr
  | Sar
  | Keccak256
  | Address
  | Balance
  | Origin
  | Caller
  | Callvalue
  | Calldataload
  | Calldatacopy
  | Calldatasize
  | Codesize
  | Codecopy
  | Gasprice
  | Extcodesize
  | Extcodecopy
  | Extcodehash
  | Returndatasize
  | Returndatacopy
  | Blockhash
  | Coinbase
  | Timestamp
  | Gaslimit
  | Chainid
  | Selfbalance
  | Mload
  | Mstore
  | Sload
  | Sstore
  | Msize
  | Gas
  | Revert
  | Return
  | Pop
  | Call
  | Staticcall
  | Delegatecall
  | Loadimmutable
  | Log1
  | Log2
  | Log3
  | Log4
  | Number
deriving Repr

abbrev PrimOp := P

def P.toString (primOp : P) : String :=
  (ToString.toString <| repr primOp).splitOn "." |>.getLast!

-- https://docs.soliditylang.org/en/latest/yul.html#informal-description-of-yul

mutual
  inductive FunctionDefinition where
    | Def : List Identifier → List Identifier → List Stmt → FunctionDefinition

  inductive Expr where
    | PrimCall : PrimOp → List Expr → Expr
    | Call : FunctionDefinition → List Expr → Expr
    | Var : Identifier → Expr
    | Lit : Literal → Expr

  -- | The loop constructor 'Stmt.For' has no initialiser because of 
  -- https://docs.soliditylang.org/en/latest/internals/optimizer.html#forloopinitrewriter
  inductive Stmt where
    | Block : List Stmt → Stmt
    | Let : List Identifier → Stmt
    | LetEq : Identifier → Expr → Stmt
    | LetCall : List Identifier → FunctionDefinition → List Expr → Stmt
    | LetPrimCall : List Identifier → PrimOp → List Expr → Stmt
    | Assign : Identifier → Expr → Stmt
    | AssignCall : List Identifier → FunctionDefinition → List Expr → Stmt
    | AssignPrimCall : List Identifier → PrimOp → List Expr → Stmt
    | ExprStmtCall : FunctionDefinition → List Expr -> Stmt
    | ExprStmtPrimCall : PrimOp → List Expr -> Stmt
    | Switch : Expr → List (Literal × List Stmt) → List Stmt → Stmt
    | For : Expr → List Stmt → List Stmt → Stmt
    | If : Expr → List Stmt → Stmt
    | Continue : Stmt
    | Break : Stmt
    | Leave : Stmt
end

namespace FunctionDefinition

def params : FunctionDefinition → List Identifier
  | Def params _ _ => params

def rets : FunctionDefinition → List Identifier
  | Def _ rets _ => rets

def body : FunctionDefinition → List Stmt
  | Def _ _ body => body

end FunctionDefinition


end Clear.Ast
