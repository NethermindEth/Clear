import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.fun_allowance
import Generated.ERC20simple.ERC20Shim.Common.if_6834419392173916452
import Generated.ERC20simple.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.ERC20simple.ERC20Shim.fun_approve_515


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def fun_spendAllowance : FunctionDefinition := <f
    function fun_spendAllowance(var_owner, var_spender, var_value) -> 
    
{
    let _1 := var_owner
    let expr := var_owner
    let _2 := var_spender
    let expr_1 := var_spender
    let expr_2 := fun_allowance(var_owner, var_spender)
    let var_currentAllowance := expr_2
    let _3 := expr_2
    let expr_3 := expr_2
    let expr_4 := not(0)
    let expr_5 := lt(expr_2, expr_4)
    if expr_5 
    {
        let _4 := expr_2
        let expr_6 := expr_2
        let _5 := var_value
        let expr_7 := var_value
        let expr_8 := lt(expr_2, var_value)
        if expr_8 
        {
            let _6 := var_spender
            let expr_9 := var_spender
            let _7 := expr_2
            let expr_10 := expr_2
            let _8 := var_value
            let expr_11 := var_value
            let _9 := 64
            let _10 := mload(_9)
            let _11 := shl(225, 2110234841)
            mstore(_10, _11)
            let _12 := 4
            let _13 := add(_10, _12)
            let _14 := abi_encode_address_uint256_uint256(_13, var_spender, expr_2, var_value)
            let _15 := sub(_14, _10)
            revert(_10, _15)
        }
        let _16 := var_owner
        let expr_12 := var_owner
        let _17 := var_spender
        let expr_13 := var_spender
        let _18 := expr_2
        let expr_14 := expr_2
        let _19 := var_value
        let expr_15 := var_value
        let expr_16 := sub(expr_2, var_value)
        let expr_17 := 0
        fun_approve_515(var_owner, var_spender, expr_16, expr_17)
    }
}
    
>

set_option maxRecDepth 4000
set_option maxHeartbeats 300000

def fun_spendAllowance_concrete_of_code
: {
    C :
      _ → _ → _ → 
      State → State → Prop
    // ∀ {s₀ s₉ : State} { var_owner var_spender var_value fuel},
         execCall fuel fun_spendAllowance [] (s₀, [var_owner, var_spender, var_value]) = s₉ →
         Spec (C  var_owner var_spender var_value) s₀ s₉
  } := by
  constructor
  intros s₀ s₉  var_owner var_spender var_value fuel
  unfold fun_spendAllowance

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
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetCall', AssignCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- EXPR 
  try simp
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (fun_allowance_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMNot']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMLt']
  try simp
  
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_6834419392173916452_abs_of_code if_6834419392173916452 with ss hs
  try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro ss (And.intro hs ?_)
  swap; clear hs
  try revert h'
  revert h
  subst xs
  
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
