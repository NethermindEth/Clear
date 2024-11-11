import Clear.ReasoningPrinciple

import Generated.ERC20.GetCode.Common.if_8423444027764651193


namespace Generated.ERC20.GetCode

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities GetCode.Common 

def fun_transfer : FunctionDefinition := <f
    function fun_transfer(var_ammount, var_acc1, var_acc2) -> var_acc1out, var_acc2out
    
{
    var_acc1out := 0
    var_acc2out := 0
    let usr := lt(var_ammount, var_acc1)
    if eq(0, usr) 
    {
        var_acc1out := sub(var_acc1, var_ammount)
        var_acc2out := add(var_acc2, var_ammount)
    }
}
    
>

set_option maxRecDepth 4000
set_option maxHeartbeats 300000

def fun_transfer_concrete_of_code
: {
    C :
      _ → _ → _ → _ → _ → 
      State → State → Prop
    // ∀ {s₀ s₉ : State} {var_acc1out var_acc2out var_ammount var_acc1 var_acc2 fuel},
         execCall fuel fun_transfer [var_acc1out, var_acc2out] (s₀, [var_ammount, var_acc1, var_acc2]) = s₉ →
         Spec (C var_acc1out var_acc2out var_ammount var_acc1 var_acc2) s₀ s₉
  } := by
  constructor
  intros s₀ s₉ var_acc1out var_acc2out var_ammount var_acc1 var_acc2 fuel
  unfold fun_transfer

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
  rw [EVMLt']
  try simp
  
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_8423444027764651193_abs_of_code if_8423444027764651193 with ss hs
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

end Generated.ERC20.GetCode
