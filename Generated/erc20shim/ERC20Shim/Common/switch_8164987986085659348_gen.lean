import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.array_dataslot_string_storage
import Generated.erc20shim.ERC20Shim.Common.for_1821242857744567453


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def switch_8164987986085659348 := <s
  switch _2 case 0 {
    let _3 := not(255)
    let _4 := and(slotValue, _3)
    mstore(pos, _4)
    let _5 := iszero(length)
    let _6 := iszero(_5)
    let _7 := shl(5, _6)
    ret := add(pos, _7)
}
case 1 {
    let dataPos := array_dataslot_string_storage(value)
    let i := 0
    for { } lt(i, length) {
        let _8 := 32
        i := add(i, _8)
    } {
        let _9 := sload(dataPos)
        let _10 := add(pos, i)
        mstore(_10, _9)
        let _11 := _1
        dataPos := add(dataPos, _1)
    }
    ret := add(pos, i)
}
default
{ }
>

set_option maxRecDepth 5000
set_option maxHeartbeats 400000

def switch_8164987986085659348_concrete_of_code : {
    C : State → State → Prop
    // ∀ {s₀ s₉ fuel}
    , exec fuel switch_8164987986085659348 s₀ = s₉
    → Spec C s₀ s₉
  } := by
  constructor
  intros s₀ s₉ fuel

  unfold Spec switch_8164987986085659348
  rcases s₀ with ⟨evm₀, store₀⟩ | _ | c <;> dsimp only
  rotate_left 1
  · generalize Switch _ _ _ = f; aesop
  · generalize Switch _ _ _ = f; aesop
  swap
  generalize hok : Ok evm₀ store₀ = s₀
  intros h _
  revert h

  rw [Switch']

  -- AST-specific tactics

  unfold execSwitchCases
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- simp [Var']
  (try (unfold execSwitchCases))
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMNot']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMAnd']
  try simp
  
  rw [cons, ExprStmtPrimCall']; try simp only
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- EXPR 
  rw [EVMMstore']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMIszero']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMIszero']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMShl']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMAdd']
  try simp
  
  (try (unfold execSwitchCases))
  rw [cons]; simp only [LetCall', AssignCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- EXPR 
  try simp
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (array_dataslot_string_storage_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract for_1821242857744567453_abs_of_code for_1821242857744567453 with ss hs
  try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro ss (And.intro hs ?_)
  swap; clear hs
  try revert h'
  revert h
  subst xs
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMAdd']
  try simp
  
  
  generalize hdefault : exec _ _ _ = sdef
  (try (unfold execSwitchCases))
  subst hdefault
  
  
  -- tacticsOfStmt offsetting
  try rw [nil]
  try simp [Bool.toUInt256, UInt256.size]
  intros h
  exact h


end

end ERC20Shim.Common
