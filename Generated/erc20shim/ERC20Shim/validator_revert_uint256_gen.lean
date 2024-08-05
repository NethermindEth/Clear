import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_1438067688173587229


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common 

def validator_revert_uint256 : FunctionDefinition := <f
    function validator_revert_uint256(value) -> 
    
{
    let _1 := 0
    if _1 
    {
        let _2 := _1
        let _3 := _1
        revert(_1, _1)
    }
}
    
>

set_option maxRecDepth 4000
set_option maxHeartbeats 300000

def validator_revert_uint256_concrete_of_code
: {
    C :
      _ → 
      State → State → Prop
    // ∀ {s₀ s₉ : State} { value fuel},
         execCall fuel validator_revert_uint256 [] (s₀, [value]) = s₉ →
         Spec (C  value) s₀ s₉
  } := by
  constructor
  intros s₀ s₉  value fuel
  unfold validator_revert_uint256

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
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_1438067688173587229_abs_of_code if_1438067688173587229 with ss hs
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
