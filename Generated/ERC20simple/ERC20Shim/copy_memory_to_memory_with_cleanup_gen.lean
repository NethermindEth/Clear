import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.for_6088573059593786335


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common 

def copy_memory_to_memory_with_cleanup : FunctionDefinition := <f
    function copy_memory_to_memory_with_cleanup(src, dst, length) -> 
    
{
    let i := 0
    for { } lt(i, length) {
        let _1 := 32
        i := add(i, _1)
    } {
        let _2 := add(src, i)
        let _3 := mload(_2)
        let _4 := add(dst, i)
        mstore(_4, _3)
    }
    let _5 := 0
    let _6 := add(dst, length)
    mstore(_6, _5)
}
    
>

set_option maxRecDepth 4000
set_option maxHeartbeats 300000

def copy_memory_to_memory_with_cleanup_concrete_of_code
: {
    C :
      _ → _ → _ → 
      State → State → Prop
    // ∀ {s₀ s₉ : State} { src dst length fuel},
         execCall fuel copy_memory_to_memory_with_cleanup [] (s₀, [src, dst, length]) = s₉ →
         Spec (C  src dst length) s₀ s₉
  } := by
  constructor
  intros s₀ s₉  src dst length fuel
  unfold copy_memory_to_memory_with_cleanup

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
  abstract for_6088573059593786335_abs_of_code for_6088573059593786335 with ss hs
  try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro ss (And.intro hs ?_)
  swap; clear hs
  try revert h'
  revert h
  subst xs
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMAdd']
  try simp
  
  rw [cons, ExprStmtPrimCall']; try simp only
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- EXPR 
  rw [EVMMstore']
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

end Generated.ERC20simple.ERC20Shim
