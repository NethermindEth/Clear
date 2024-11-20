import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.switch_2364266820542243941
import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.erc20shim.ERC20Shim.checked_add_uint256
import Generated.erc20shim.ERC20Shim.Common.switch_1041419350816529734
import Generated.erc20shim.ERC20Shim.abi_encode_uint256


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def fun_update : FunctionDefinition := <f
    function fun_update(var_from, var_to, var_value) -> 
    
{
    let expr := var_from
    let _1 := sub(shl(160, 1), 1)
    let _2 := and(var_from, _1)
    let _3 := iszero(_2)
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
    let expr_5 := var_to
    let _22 := _1
    let _23 := and(var_to, _1)
    let _24 := iszero(_23)
    switch _24 case 0 {
        let expr_6 := var_value
        let _25 := 0
        let _26 := mapping_index_access_mapping_address_uint256_of_address(_25, var_to)
        let _27 := sload(_26)
        let _28 := _27
        let _29 := add(_27, var_value)
        update_storage_value_offsett_uint256_to_uint256(_26, _29)
    }
    default
    {
        let _30 := 2
        let _31 := sload(_30)
        let _32 := _31
        let _33 := sub(_31, var_value)
        let _34 := _30
        update_storage_value_offsett_uint256_to_uint256(_30, _33)
    }
    let expr_7 := var_from
    let expr_8 := var_to
    let expr_9 := var_value
    let _35 := 100389287136786176327247604509743168900146139575972864366142685224231313322991
    let _36 := _2
    let _37 := _23
    let _38 := 64
    let _39 := mload(_38)
    let _40 := abi_encode_uint256(_39, var_value)
    let _41 := sub(_40, _39)
    log3(_39, _41, _35, _2, _23)
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
  abstract switch_2364266820542243941_abs_of_code switch_2364266820542243941 with ss hs
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
  abstract switch_1041419350816529734_abs_of_code switch_1041419350816529734 with ss hs
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

end Generated.erc20shim.ERC20Shim
