import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def if_3989404597755436942 := <s
  if _7 
{
    let expr_1 := var_from
    let expr_2 := _6
    let expr_3 := var_value
    let _8 := 64
    let _9 := mload(_8)
    let _10 := shl(226, 957625571)
    mstore(_9, _10)
    let _11 := 4
    let _12 := add(_9, _11)
    let _13 := abi_encode_address_uint256_uint256(_12, var_from, _6, var_value)
    let _14 := sub(_13, _9)
    revert(_9, _14)
}
>

set_option maxRecDepth 5000
set_option maxHeartbeats 400000

def if_3989404597755436942_concrete_of_code : {
    C : State → State → Prop
    // ∀ {s₀ s₉ fuel}
    , exec fuel if_3989404597755436942 s₀ = s₉
    → Spec C s₀ s₉
  } := by
  constructor
  intros s₀ s₉ fuel

  unfold Spec if_3989404597755436942
  rcases s₀ with ⟨evm₀, store₀⟩ | _ | c <;> dsimp only
  rotate_left 1
  · generalize If _ _ = f; aesop
  · generalize If _ _ = f; aesop
  swap
  generalize hok : Ok evm₀ store₀ = s₀
  intros h _
  revert h

  rw [If']

  -- AST-specific tactics

  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- simp [Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMMload']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMShl']
  try simp
  
  rw [cons, ExprStmtPrimCall']; try simp only
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- EXPR 
  rw [EVMMstore']
  try simp
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMAdd']
  try simp
  
  rw [cons]; simp only [LetCall', AssignCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- EXPR 
  try simp
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (abi_encode_address_uint256_uint256_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMSub']
  try simp
  
  rw [cons, ExprStmtPrimCall']; try simp only
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- EXPR 
  rw [EVMRevert']
  try simp
  
  
  
  -- tacticsOfStmt offsetting
  try rw [nil]
  try simp [Bool.toUInt256, UInt256.size]
  intros h
  exact h


end

end ERC20Shim.Common
