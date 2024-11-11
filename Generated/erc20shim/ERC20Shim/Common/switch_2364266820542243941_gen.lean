import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.Common.if_3989404597755436942
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.erc20shim.ERC20Shim.checked_add_uint256


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def switch_2364266820542243941 := <s
  switch _3 case 0 {
    let _4 := 0
    let _5 := mapping_index_access_mapping_address_uint256_of_address(_4, var_from)
    let _6 := sload(_5)
    let var_fromBalance := _6
    let _7 := lt(_6, var_value)
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
    let expr_4 := sub(_6, var_value)
    let _15 := _4
    let _16 := mapping_index_access_mapping_address_uint256_of_address(_4, var_from)
    update_storage_value_offsett_uint256_to_uint256(_16, expr_4)
}
default
{
    let _17 := 2
    let _18 := sload(_17)
    let _19 := _18
    let _20 := checked_add_uint256(_18, var_value)
    let _21 := _17
    update_storage_value_offsett_uint256_to_uint256(_17, _20)
}
>

set_option maxRecDepth 5000
set_option maxHeartbeats 400000

def switch_2364266820542243941_concrete_of_code : {
    C : State → State → Prop
    // ∀ {s₀ s₉ fuel}
    , exec fuel switch_2364266820542243941 s₀ = s₉
    → Spec C s₀ s₉
  } := by
  constructor
  intros s₀ s₉ fuel

  unfold Spec switch_2364266820542243941
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
  simp only [Fin.isValue]
  try rw [List.foldr_cons]
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  -- simp [Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetCall', AssignCall']
  try simp only [Fin.isValue]; try rw [List.foldr_cons]; 
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  -- EXPR 
  try simp
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (mapping_index_access_mapping_address_uint256_of_address_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  try simp only [Fin.isValue]; try rw [List.foldr_cons]; 
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMSload']
  try simp
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  try simp only [Fin.isValue]; try rw [List.foldr_cons]; 
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMLt']
  try simp
  
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_3989404597755436942_abs_of_code if_3989404597755436942 with ss hs
  try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro ss (And.intro hs ?_)
  swap; clear hs
  try revert h'
  revert h
  subst xs
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  try simp only [Fin.isValue]; try rw [List.foldr_cons]; 
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMSub']
  try simp
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetCall', AssignCall']
  try simp only [Fin.isValue]; try rw [List.foldr_cons]; 
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  -- EXPR 
  try simp
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (mapping_index_access_mapping_address_uint256_of_address_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  rw [cons, ExprStmtCall']; try simp only
  try simp only [Fin.isValue]; try rw [List.foldr_cons]; 
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  -- simp [Var']
  -- simp [Var']
  try simp
  
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (update_storage_value_offsett_uint256_to_uint256_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  
  generalize hdefault : exec _ _ _ = sdef
  unfold execSwitchCases
  subst hdefault
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  try simp only [Fin.isValue]; try rw [List.foldr_cons]; try rw [List.foldr_nil]
  simp only [Fin.isValue, execPrimCall, multifill', reverse', List.reverse_cons, List.reverse_nil,
    List.nil_append, evalArgs, Var', evalTail_nil]
  try rw [List.foldr_nil]
  rw [EVMSload']
  try simp
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetCall', AssignCall']
  try simp only [Fin.isValue]; try rw [List.foldr_cons]; 
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  -- EXPR 
  try simp
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (checked_add_uint256_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons, ExprStmtCall']; try simp only
  try simp only [Fin.isValue]; try rw [List.foldr_cons]; 
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  -- simp [Var']
  -- simp [Var']
  try simp
  
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (update_storage_value_offsett_uint256_to_uint256_abs_of_code hs) ?_)
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
