import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun_allowance
import Generated.erc20shim.ERC20Shim.Common.if_5327145078839977110
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.fun__approve


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def fun_spendAllowance : FunctionDefinition := <f
    function fun_spendAllowance(var_owner, var_spender, var_value) -> 
    
{
    let var_currentAllowance := fun_allowance(var_owner, var_spender)
    let _1 := not(0)
    let _2 := eq(var_currentAllowance, _1)
    let _3 := iszero(_2)
    if _3 
    {
        let _4 := lt(var_currentAllowance, var_value)
        if _4 
        {
            let expr := var_spender
            let expr_1 := var_currentAllowance
            let expr_2 := var_value
            let _5 := 64
            let _6 := mload(_5)
            let _7 := shl(225, 2110234841)
            mstore(_6, _7)
            let _8 := 4
            let _9 := add(_6, _8)
            let _10 := abi_encode_address_uint256_uint256(_9, var_spender, var_currentAllowance, var_value)
            let _11 := sub(_10, _6)
            revert(_6, _11)
        }
        let expr_3 := var_owner
        let expr_4 := var_spender
        let _12 := 0
        let _13 := sub(var_currentAllowance, var_value)
        fun__approve(var_owner, var_spender, _13, _12)
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

  rw [cons]; simp only [LetCall', AssignCall']
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  -- EXPR 
  try simp
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (fun_allowance_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMNot']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMEq']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMIszero']
  try simp
  
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_5327145078839977110_abs_of_code if_5327145078839977110 with ss hs
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

end Generated.erc20shim.ERC20Shim
