import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_5295847412656974480
import Generated.ERC20simple.ERC20Shim.checked_sub_uint256
import Generated.ERC20simple.ERC20Shim.checked_add_uint256


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def fun_transferFromSimple : FunctionDefinition := <f
    function fun_transferFromSimple(var_from, var_to, var_value) -> var, var_1, var_2
    
{
    let _1 := var_from
    let expr := var_from
    let _2 := var_value
    let expr_1 := var_value
    let expr_2 := lt(var_from, var_value)
    if expr_2 
    {
        let expr_3 := 0
        let expr_201_component := expr_3
        let _3 := var_from
        let expr_4 := var_from
        let expr_201_component_1 := var_from
        let _4 := var_to
        let expr_5 := var_to
        let expr_component := var_to
        var := expr_3
        var_1 := var_from
        var_2 := var_to
        leave
    }
    let expr_6 := 1
    let expr_component_1 := expr_6
    let _5 := var_from
    let expr_7 := var_from
    let _6 := var_value
    let expr_8 := var_value
    let expr_9 := checked_sub_uint256(var_from, var_value)
    let expr_component_2 := expr_9
    let _7 := var_to
    let expr_10 := var_to
    let _8 := var_value
    let expr_11 := var_value
    let expr_12 := checked_add_uint256(var_to, var_value)
    let expr_component_3 := expr_12
    var := expr_6
    var_1 := expr_9
    var_2 := expr_12
}
    
>

set_option maxRecDepth 4000
set_option maxHeartbeats 300000

def fun_transferFromSimple_concrete_of_code
: {
    C :
      _ → _ → _ → _ → _ → _ → 
      State → State → Prop
    // ∀ {s₀ s₉ : State} {var var_1 var_2 var_from var_to var_value fuel},
         execCall fuel fun_transferFromSimple [var, var_1, var_2] (s₀, [var_from, var_to, var_value]) = s₉ →
         Spec (C var var_1 var_2 var_from var_to var_value) s₀ s₉
  } := by
  constructor
  intros s₀ s₉ var var_1 var_2 var_from var_to var_value fuel
  unfold fun_transferFromSimple

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
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMLt']
  try simp
  
  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_5295847412656974480_abs_of_code if_5295847412656974480 with ss hs
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
  refine' Exists.intro s (And.intro (checked_sub_uint256_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
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
  refine' Exists.intro s (And.intro (checked_add_uint256_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
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
