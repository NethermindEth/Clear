import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_3856757177752523473
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.fun__approve


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def if_8475192588736690919 := <s
  if _2 
{
    let _3 := lt(var_currentAllowance, var_value)
    if _3 
    {
        let expr := var_spender
        let expr_1 := var_currentAllowance
        let expr_2 := var_value
        let _4 := 64
        let _5 := mload(_4)
        let _6 := shl(225, 2110234841)
        mstore(_5, _6)
        let _7 := 4
        let _8 := add(_5, _7)
        let _9 := abi_encode_address_uint256_uint256(_8, var_spender, var_currentAllowance, var_value)
        let _10 := sub(_9, _5)
        revert(_5, _10)
    }
    let expr_3 := var_owner
    let expr_4 := var_spender
    let _11 := 0
    let _12 := sub(var_currentAllowance, var_value)
    fun__approve(var_owner, var_spender, _12, _11)
}
>

set_option maxRecDepth 5000
set_option maxHeartbeats 400000

def if_8475192588736690919_concrete_of_code : {
    C : State → State → Prop
    // ∀ {s₀ s₉ fuel}
    , exec fuel if_8475192588736690919 s₀ = s₉
    → Spec C s₀ s₉
  } := by
  constructor
  intros s₀ s₉ fuel

  unfold Spec if_8475192588736690919
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
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMLt']
  try simp
  
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_3856757177752523473_abs_of_code if_3856757177752523473 with ss hs
  try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro ss (And.intro hs ?_)
  swap; clear hs
  try revert h'
  revert h
  subst xs
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMSub']
  try simp
  
  rw [cons, ExprStmtCall']; try simp only
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- simp [Var']
  -- simp [Var']
  -- simp [Var']
  -- simp [Var']
  try simp
  
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (fun__approve_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  
  
  -- tacticsOfStmt offsetting
  try rw [nil]
  try simp [Bool.toUInt256, UInt256.size]
  intros h
  exact h


end

end ERC20Shim.Common