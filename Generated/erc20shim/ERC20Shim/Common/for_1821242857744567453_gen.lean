import Clear.ReasoningPrinciple



namespace ERC20Shim.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def for_1821242857744567453_cond := <<
    lt(i, length)
>>

def for_1821242857744567453_post : List Stmt := <ss
    {
    let _8 := 32
    i := add(i, _8)
}
>

def for_1821242857744567453_body : List Stmt := <ss
{
    let _9 := sload(dataPos)
    let _10 := add(pos, i)
    mstore(_10, _9)
    let _11 := _1
    dataPos := add(dataPos, _1)
}
>

def for_1821242857744567453 := <s
for { } lt(i, length) {
    let _8 := 32
    i := add(i, _8)
} {
    let _9 := sload(dataPos)
    let _10 := add(pos, i)
    mstore(_10, _9)
    let _11 := _1
    dataPos := add(dataPos, _1)
}
>

set_option maxRecDepth 4000

-- =============================================================================
--  POST
-- =============================================================================

def for_1821242857744567453_post_concrete_of_code
: {
    C : State → State → Prop
    // ∀ {s₀ s₉ fuel}
    , exec fuel (Block for_1821242857744567453_post) s₀ = s₉
    → Spec C s₀ s₉
  } := by
  constructor
  intros s₀ s₉ fuel

  unfold Spec for_1821242857744567453_post
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
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
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

def for_1821242857744567453_body_concrete_of_code
: {
    C : State → State → Prop
    // ∀ {s₀ s₉ fuel}
    , exec fuel (Block for_1821242857744567453_body) s₀ = s₉
    → Spec C s₀ s₉
  }
:= by
  constructor
  intros s₀ s₉ fuel

  unfold Spec for_1821242857744567453_body
  rcases s₀ with ⟨evm₀, store₀⟩ | _ | c <;> dsimp only
  rotate_left 1
  · aesop
  · aesop
  swap
  generalize hok : Ok evm₀ store₀ = s₀
  intros h _
  revert h

  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMSload']
  try simp
  
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMAdd']
  try simp
  
  rw [cons, ExprStmtPrimCall']; try simp only
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- EXPR 
  rw [EVMMstore']
  try simp
  
  rw [cons]; simp only [LetEq', Assign', Lit', Var']
  rw [cons]; simp only [LetPrimCall', AssignPrimCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  rw [EVMAdd']
  try simp
  
  
  -- tacticsOfStmt offsetting
  try rw [nil]
  try simp [Bool.toUInt256, UInt256.size]
  intros h
  exact h


end

end ERC20Shim.Common
