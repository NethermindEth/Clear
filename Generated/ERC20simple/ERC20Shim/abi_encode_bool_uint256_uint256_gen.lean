import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_bool_to_bool
import Generated.ERC20simple.ERC20Shim.abi_encode_uint256_to_uint256


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def abi_encode_bool_uint256_uint256 : FunctionDefinition := <f
    function abi_encode_bool_uint256_uint256(headStart, value0, value1, value2) -> tail
    
{
    let _1 := 96
    tail := add(headStart, _1)
    abi_encode_bool_to_bool(value0, headStart)
    let _2 := 32
    let _3 := add(headStart, _2)
    abi_encode_uint256_to_uint256(value1, _3)
    let _4 := 64
    let _5 := add(headStart, _4)
    abi_encode_uint256_to_uint256(value2, _5)
}
    
>

set_option maxRecDepth 4000
set_option maxHeartbeats 300000

def abi_encode_bool_uint256_uint256_concrete_of_code
: {
    C :
      _ → _ → _ → _ → _ → 
      State → State → Prop
    // ∀ {s₀ s₉ : State} {tail headStart value0 value1 value2 fuel},
         execCall fuel abi_encode_bool_uint256_uint256 [tail] (s₀, [headStart, value0, value1, value2]) = s₉ →
         Spec (C tail headStart value0 value1 value2) s₀ s₉
  } := by
  constructor
  intros s₀ s₉ tail headStart value0 value1 value2 fuel
  unfold abi_encode_bool_uint256_uint256

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
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMAdd']
  try simp
  
  rw [cons, ExprStmtCall']; try simp only
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- simp [Var']
  -- simp [Var']
  try simp
  
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (abi_encode_bool_to_bool_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMAdd']
  try simp
  
  rw [cons, ExprStmtCall']; try simp only
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- simp [Var']
  -- simp [Var']
  try simp
  
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (abi_encode_uint256_to_uint256_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMAdd']
  try simp
  
  rw [cons, ExprStmtCall']; try simp only
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- simp [Var']
  -- simp [Var']
  try simp
  
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (abi_encode_uint256_to_uint256_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
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
