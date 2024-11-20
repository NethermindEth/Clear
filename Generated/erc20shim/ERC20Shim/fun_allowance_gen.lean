import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def fun_allowance : FunctionDefinition := <f
    function fun_allowance(var_owner, var_spender) -> var
    
{
    let _1 := 1
    let _2 := mapping_index_access_mapping_address_mapping_address_uint256_of_address(_1, var_owner)
    let _3 := mapping_index_access_mapping_address_uint256_of_address(_2, var_spender)
    var := sload(_3)
}
    
>

set_option maxRecDepth 4000
set_option maxHeartbeats 300000

def fun_allowance_concrete_of_code
: {
    C :
      _ → _ → _ → 
      State → State → Prop
    // ∀ {s₀ s₉ : State} {var var_owner var_spender fuel},
         execCall fuel fun_allowance [var] (s₀, [var_owner, var_spender]) = s₉ →
         Spec (C var var_owner var_spender) s₀ s₉
  } := by
  constructor
  intros s₀ s₉ var var_owner var_spender fuel
  unfold fun_allowance

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
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMSload']
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

end Generated.erc20shim.ERC20Shim
