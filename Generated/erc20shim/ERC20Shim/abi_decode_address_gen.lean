import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.validator_revert_address


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def abi_decode_address : FunctionDefinition := <f
    function abi_decode_address(offset, end_clear_sanitised_hrafn) -> value
    
{
    value := calldataload(offset)
    validator_revert_address(value)
}
    
>

set_option maxRecDepth 4000
set_option maxHeartbeats 300000

def abi_decode_address_concrete_of_code
: {
    C :
      _ → _ → _ → 
      State → State → Prop
    // ∀ {s₀ s₉ : State} {value offset end_clear_sanitised_hrafn fuel},
         execCall fuel abi_decode_address [value] (s₀, [offset, end_clear_sanitised_hrafn]) = s₉ →
         Spec (C value offset end_clear_sanitised_hrafn) s₀ s₉
  } := by
  constructor
  intros s₀ s₉ value offset end_clear_sanitised_hrafn fuel
  unfold abi_decode_address

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

  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMCalldataload']
  try simp
  
  rw [cons, ExprStmtCall']; try simp only
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  -- simp [Var']
  try simp
  
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (validator_revert_address_abs_of_code hs) ?_)
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
