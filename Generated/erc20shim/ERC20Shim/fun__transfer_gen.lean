import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_9141570808380448040
import Generated.erc20shim.ERC20Shim.abi_encode_tuple_address
import Generated.erc20shim.ERC20Shim.Common.if_2395397427938978657
import Generated.erc20shim.ERC20Shim.fun_update


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def fun__transfer : FunctionDefinition := <f
    function fun__transfer(var_from, var_to, var_value) -> 
    
{
    let expr := var_from
    let _1 := sub(shl(160, 1), 1)
    let _2 := and(var_from, _1)
    let _3 := iszero(_2)
    if _3 
    {
        let expr_1 := 0
        let _4 := 64
        let _5 := mload(_4)
        let _6 := shl(225, 1264811663)
        mstore(_5, _6)
        let _7 := 4
        let _8 := add(_5, _7)
        let _9 := abi_encode_tuple_address(_8, expr_1)
        let _10 := sub(_9, _5)
        revert(_5, _10)
    }
    let expr_2 := var_to
    let _11 := _1
    let _12 := and(var_to, _1)
    let _13 := iszero(_12)
    if _13 
    {
        let expr_3 := 0
        let _14 := 64
        let _15 := mload(_14)
        let _16 := shl(224, 3963891461)
        mstore(_15, _16)
        let _17 := 4
        let _18 := add(_15, _17)
        let _19 := abi_encode_tuple_address(_18, expr_3)
        let _20 := sub(_19, _15)
        revert(_15, _20)
    }
    fun_update(var_from, var_to, var_value)
}
    
>

set_option maxRecDepth 4000
set_option maxHeartbeats 300000

def fun__transfer_concrete_of_code
: {
    C :
      _ → _ → _ → 
      State → State → Prop
    // ∀ {s₀ s₉ : State} { var_from var_to var_value fuel},
         execCall fuel fun__transfer [] (s₀, [var_from, var_to, var_value]) = s₉ →
         Spec (C  var_from var_to var_value) s₀ s₉
  } := by
  constructor
  intros s₀ s₉  var_from var_to var_value fuel
  unfold fun__transfer

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
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMSub']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMAnd']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMIszero']
  try simp
  
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_9141570808380448040_abs_of_code if_9141570808380448040 with ss hs
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
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMAnd']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMIszero']
  try simp
  
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_2395397427938978657_abs_of_code if_2395397427938978657 with ss hs
  try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro ss (And.intro hs ?_)
  swap; clear hs
  try revert h'
  revert h
  subst xs
  
  rw [cons, ExprStmtCall']; try simp only
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  -- simp [Var']
  -- simp [Var']
  -- simp [Var']
  try simp
  
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (fun_update_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
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
