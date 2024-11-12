import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.switch_7286792350880435020
import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.ERC20simple.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.ERC20simple.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.ERC20simple.ERC20Shim.checked_add_uint256
import Generated.ERC20simple.ERC20Shim.Common.switch_108332838879531311
import Generated.ERC20simple.ERC20Shim.abi_encode_uint256


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def fun_update : FunctionDefinition := <f
    function fun_update(var_from, var_to, var_value) -> 
    
{
    let _1 := var_from
    let expr := var_from
    let _2 := sub(shl(160, 1), 1)
    let _3 := and(var_from, _2)
    let expr_1 := iszero(_3)
    switch expr_1 case 0 {
        let _57_slot := 0
        let expr_317_slot := _57_slot
        let _4 := var_from
        let expr_2 := var_from
        let _5 := mapping_index_access_mapping_address_uint256_of_address(_57_slot, var_from)
        let _6 := sload(_5)
        let _7 := _6
        let expr_3 := _6
        let var_fromBalance := _6
        let _8 := _6
        let expr_4 := _6
        let _9 := var_value
        let expr_5 := var_value
        let expr_6 := lt(_6, var_value)
        if expr_6 
        {
            let _10 := var_from
            let expr_7 := var_from
            let _11 := _6
            let expr_8 := _6
            let _12 := var_value
            let expr_9 := var_value
            let _13 := 64
            let _14 := mload(_13)
            let _15 := shl(226, 957625571)
            mstore(_14, _15)
            let _16 := 4
            let _17 := add(_14, _16)
            let _18 := abi_encode_address_uint256_uint256(_17, var_from, _6, var_value)
            let _19 := sub(_18, _14)
            revert(_14, _19)
        }
        let _20 := _6
        let expr_10 := _6
        let _21 := var_value
        let expr_11 := var_value
        let expr_12 := sub(_6, var_value)
        let _70_slot := _57_slot
        let expr_332_slot := _57_slot
        let _22 := var_from
        let expr_13 := var_from
        let _23 := mapping_index_access_mapping_address_uint256_of_address(_57_slot, var_from)
        update_storage_value_offsett_uint256_to_uint256(_23, expr_12)
    }
    default
    {
        let _24 := var_value
        let expr_14 := var_value
        let _25 := 2
        let _26 := sload(_25)
        let _27 := _26
        let expr_15 := checked_add_uint256(_26, var_value)
        let _28 := _25
        update_storage_value_offsett_uint256_to_uint256(_25, expr_15)
    }
    let _29 := var_to
    let expr_16 := var_to
    let _30 := _2
    let _31 := and(var_to, _2)
    let expr_17 := iszero(_31)
    switch expr_17 case 0 {
        let _32 := var_value
        let expr_18 := var_value
        let _77_slot := 0
        let expr_355_slot := _77_slot
        let _33 := var_to
        let expr_19 := var_to
        let _34 := mapping_index_access_mapping_address_uint256_of_address(_77_slot, var_to)
        let _35 := sload(_34)
        let _36 := _35
        let expr_20 := add(_35, var_value)
        update_storage_value_offsett_uint256_to_uint256(_34, expr_20)
    }
    default
    {
        let _37 := var_value
        let expr_21 := var_value
        let _38 := 2
        let _39 := sload(_38)
        let _40 := _39
        let expr_22 := sub(_39, var_value)
        let _41 := _38
        update_storage_value_offsett_uint256_to_uint256(_38, expr_22)
    }
    let _42 := var_from
    let expr_23 := var_from
    let _43 := var_to
    let expr_24 := var_to
    let _44 := var_value
    let expr_25 := var_value
    let _45 := 100389287136786176327247604509743168900146139575972864366142685224231313322991
    let _46 := _3
    let _47 := _31
    let _48 := 64
    let _49 := mload(_48)
    let _50 := abi_encode_uint256(_49, var_value)
    let _51 := sub(_50, _49)
    log3(_49, _51, _45, _3, _31)
}
    
>

set_option maxRecDepth 4000
set_option maxHeartbeats 300000

def fun_update_concrete_of_code
: {
    C :
      _ → _ → _ → 
      State → State → Prop
    // ∀ {s₀ s₉ : State} { var_from var_to var_value fuel},
         execCall fuel fun_update [] (s₀, [var_from, var_to, var_value]) = s₉ →
         Spec (C  var_from var_to var_value) s₀ s₉
  } := by
  constructor
  intros s₀ s₉  var_from var_to var_value fuel
  unfold fun_update

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
  abstract switch_7286792350880435020_abs_of_code switch_7286792350880435020 with ss hs
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
  abstract switch_108332838879531311_abs_of_code switch_108332838879531311 with ss hs
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
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMMload']
  try simp
  
  rw [cons]; simp only [LetCall', AssignCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- EXPR 
  try simp
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (abi_encode_uint256_abs_of_code hs) ?_)
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
  rw [EVMLog3']
  try simp
  
  try clr_varstore_target
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
