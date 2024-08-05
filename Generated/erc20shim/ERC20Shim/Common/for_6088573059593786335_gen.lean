import Clear.ReasoningPrinciple



namespace ERC20Shim.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def for_6088573059593786335_cond := <<
    lt(i, length)
>>

def for_6088573059593786335_post : List Stmt := <ss
    {
    let _1 := 32
    i := add(i, _1)
}
>

def for_6088573059593786335_body : List Stmt := <ss
{
    let _2 := add(src, i)
    let _3 := mload(_2)
    let _4 := add(dst, i)
    mstore(_4, _3)
}
>

def for_6088573059593786335 := <s
for { } lt(i, length) {
    let _1 := 32
    i := add(i, _1)
} {
    let _2 := add(src, i)
    let _3 := mload(_2)
    let _4 := add(dst, i)
    mstore(_4, _3)
}
>

set_option maxRecDepth 4000

-- =============================================================================
--  POST
-- =============================================================================

def for_6088573059593786335_post_concrete_of_code
: {
    C : State → State → Prop
    // ∀ {s₀ s₉ fuel}
    , exec fuel (Block for_6088573059593786335_post) s₀ = s₉
    → Spec C s₀ s₉
  } := by
  constructor
  intros s₀ s₉ fuel

  unfold Spec for_6088573059593786335_post
  rcases s₀ with ⟨evm₀, store₀⟩ | _ | c <;> dsimp only
  rotate_left 1
  · aesop
  · aesop
  swap
  generalize hok : Ok evm₀ store₀ = s₀
  intros h _
  revert h

  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMAdd']
  try simp
  
  
  -- tacticsOfStmt offsetting
  try rw [nil]
  try simp [Bool.toUInt256, UInt256.size]
  intros h
  exact h


-- =============================================================================
--  BODY
-- =============================================================================

def for_6088573059593786335_body_concrete_of_code
: {
    C : State → State → Prop
    // ∀ {s₀ s₉ fuel}
    , exec fuel (Block for_6088573059593786335_body) s₀ = s₉
    → Spec C s₀ s₉
  }
:= by
  constructor
  intros s₀ s₉ fuel

  unfold Spec for_6088573059593786335_body
  rcases s₀ with ⟨evm₀, store₀⟩ | _ | c <;> dsimp only
  rotate_left 1
  · aesop
  · aesop
  swap
  generalize hok : Ok evm₀ store₀ = s₀
  intros h _
  revert h

  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMAdd']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMMload']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  rw [EVMAdd']
  try simp
  
  rw [cons, ExprStmtPrimCall']; try simp only
  simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]
  -- EXPR 
  rw [EVMMstore']
  try simp
  
  
  -- tacticsOfStmt offsetting
  try rw [nil]
  try simp [Bool.toUInt256, UInt256.size]
  intros h
  exact h


end

end ERC20Shim.Common
