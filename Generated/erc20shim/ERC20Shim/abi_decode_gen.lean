import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_7164014626810332831
import Generated.erc20shim.ERC20Shim.revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def abi_decode : FunctionDefinition := <f
    function abi_decode(headStart, dataEnd) -> 
    
{
    let _1 := 0
    let _2 := sub(dataEnd, headStart)
    let _3 := slt(_2, _1)
    if _3 
    {revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()}
}
    
>

set_option maxRecDepth 4000
set_option maxHeartbeats 300000

def abi_decode_concrete_of_code
: {
    C :
      _ → _ → 
      State → State → Prop
    // ∀ {s₀ s₉ : State} { headStart dataEnd fuel},
         execCall fuel abi_decode [] (s₀, [headStart, dataEnd]) = s₉ →
         Spec (C  headStart dataEnd) s₀ s₉
  } := by
  constructor
  intros s₀ s₉  headStart dataEnd fuel
  unfold abi_decode

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
  rw [EVMSlt']
  try simp
  
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_7164014626810332831_abs_of_code if_7164014626810332831 with ss hs
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