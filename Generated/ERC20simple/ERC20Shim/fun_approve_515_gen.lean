import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_7933877964017211044
import Generated.ERC20simple.ERC20Shim.abi_encode_tuple_address
import Generated.ERC20simple.ERC20Shim.Common.if_7567335688764008016
import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_mapping_address_uint256_of_address
import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.ERC20simple.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.ERC20simple.ERC20Shim.Common.if_1708065363866081018
import Generated.ERC20simple.ERC20Shim.abi_encode_uint256


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def fun_approve_515 : FunctionDefinition := <f
    function fun_approve_515(var_owner, var_spender, var_value, var_emitEvent) -> 
    
{
    let _1 := var_owner
    let expr := var_owner
    let _2 := sub(shl(160, 1), 1)
    let _3 := and(var_owner, _2)
    let expr_1 := iszero(_3)
    if expr_1 
    {
        let expr_2 := 0
        let _4 := 64
        let _5 := mload(_4)
        let _6 := shl(224, 3858947845)
        mstore(_5, _6)
        let _7 := 4
        let _8 := add(_5, _7)
        let _9 := abi_encode_tuple_address(_8, expr_2)
        let _10 := sub(_9, _5)
        revert(_5, _10)
    }
    let _11 := var_spender
    let expr_3 := var_spender
    let _12 := _2
    let _13 := and(var_spender, _2)
    let expr_4 := iszero(_13)
    if expr_4 
    {
        let expr_5 := 0
        let _14 := 64
        let _15 := mload(_14)
        let _16 := shl(225, 1242826417)
        mstore(_15, _16)
        let _17 := 4
        let _18 := add(_15, _17)
        let _19 := abi_encode_tuple_address(_18, expr_5)
        let _20 := sub(_19, _15)
        revert(_15, _20)
    }
    let _21 := var_value
    let expr_6 := var_value
    let _101_slot := 1
    let expr_497_slot := _101_slot
    let _22 := var_owner
    let expr_7 := var_owner
    let _23 := mapping_index_access_mapping_address_mapping_address_uint256_of_address(_101_slot, var_owner)
    let _104_slot := _23
    let expr_500_slot := _23
    let _24 := var_spender
    let expr_8 := var_spender
    let _25 := mapping_index_access_mapping_address_uint256_of_address(_23, var_spender)
    update_storage_value_offsett_uint256_to_uint256(_25, var_value)
    let _26 := var_emitEvent
    let expr_9 := var_emitEvent
    if var_emitEvent 
    {
        let _27 := var_owner
        let expr_10 := var_owner
        let _28 := var_spender
        let expr_11 := var_spender
        let _29 := var_value
        let expr_12 := var_value
        let _30 := 63486140976153616755203102783360879283472101686154884697241723088393386309925
        let _31 := _3
        let _32 := _13
        let _33 := 64
        let _34 := mload(_33)
        let _35 := abi_encode_uint256(_34, var_value)
        let _36 := sub(_35, _34)
        log3(_34, _36, _30, _3, _13)
    }
}
    
>

set_option maxRecDepth 4000
set_option maxHeartbeats 300000

def fun_approve_515_concrete_of_code
: {
    C :
      _ → _ → _ → _ → 
      State → State → Prop
    // ∀ {s₀ s₉ : State} { var_owner var_spender var_value var_emitEvent fuel},
         execCall fuel fun_approve_515 [] (s₀, [var_owner, var_spender, var_value, var_emitEvent]) = s₉ →
         Spec (C  var_owner var_spender var_value var_emitEvent) s₀ s₉
  } := by
  constructor
  intros s₀ s₉  var_owner var_spender var_value var_emitEvent fuel
  unfold fun_approve_515

  unfold Spec
  rcases s₀ with ⟨evm, store⟩ | _ | c <;> dsimp only
  rotate_left 1
  · generalize Def _ _ _ = f; aesop
  · generalize Def _ _ _ = f; aesop
  swap
  generalize hok : Ok evm store = s₀
  intros h _
  revert h

  unfold execCall
  unfold call
  unfold params body rets
  conv => simp_match
  conv => pattern List.map _ _; simp
  conv => pattern mkOk _; rw [← hok]; simp
  conv => pattern setStore _; rw [← hok]; simp

  generalize hs₁ : initcall _ _ _ = s₁
  let_unfold s₁
  generalize hbody : exec _ _ _ = s₂
  revert hbody
  generalize hs₉ : multifill' _ _ = s₉'

  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMSub']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMAnd']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMIszero']
  try simp
  
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_7933877964017211044_abs_of_code if_7933877964017211044 with ss hs
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
  rw [EVMAnd']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMIszero']
  try simp
  
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_7567335688764008016_abs_of_code if_7567335688764008016 with ss hs
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
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetCall', AssignCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- EXPR 
  try simp
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (mapping_index_access_mapping_address_mapping_address_uint256_of_address_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetCall', AssignCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
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
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
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
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_1708065363866081018_abs_of_code if_1708065363866081018 with ss hs
  try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro ss (And.intro hs ?_)
  swap; clear hs
  try revert h'
  revert h
  subst xs
  
  -- finish offsetting
  subst hs₉
  intros hbody
  subst hbody
  subst hs₁
  rw [← hok]
  repeat {rw [lookup_insert' (by aesop)]}
  repeat {rw [lookup_insert_of_ne (by decide)]}
  try rw [lookup_initcall_1]
  try rw [lookup_initcall_2 ?_]
  try rw [lookup_initcall_3 ?_]
  try rw [lookup_initcall_4 ?_]
  try rw [lookup_initcall_5 ?_]
  all_goals try decide
  let_unfold s₂
  simp [multifill']
  try {rw [reviveJump_insert (by aesop)]}
  repeat {rw [lookup_insert' (by aesop)]}
  try simp
  rw [hok]
  intros h
  exact h


end

end Generated.ERC20simple.ERC20Shim
