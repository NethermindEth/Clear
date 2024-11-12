import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.if_6183625948864629624
import Generated.peano.Peano.addk


namespace Peano.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common Generated.peano Peano

def for_4806375509446804985_cond := <<
    1
>>

def for_4806375509446804985_post : List Stmt := <ss
    {k := sub(k, 1)}
>

def for_4806375509446804985_body : List Stmt := <ss
{
    if eq(k, 0) 
    {break}
    y := addk(y, x)
}
>

def for_4806375509446804985 := <s
for { } 1 {k := sub(k, 1)} {
    if eq(k, 0) 
    {break}
    y := addk(y, x)
}
>

set_option maxRecDepth 4000

-- =============================================================================
--  POST
-- =============================================================================

def for_4806375509446804985_post_concrete_of_code
: {
    C : State → State → Prop
    // ∀ {s₀ s₉ fuel}
    , exec fuel (Block for_4806375509446804985_post) s₀ = s₉
    → Spec C s₀ s₉
  } := by
  constructor
  intros s₀ s₉ fuel

  unfold Spec for_4806375509446804985_post
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
  rw [EVMSub']
  try simp
  
  
  -- tacticsOfStmt offsetting
  try rw [nil]
  try simp [Bool.toUInt256, UInt256.size]
  intros h
  exact h


-- =============================================================================
--  BODY
-- =============================================================================

def for_4806375509446804985_body_concrete_of_code
: {
    C : State → State → Prop
    // ∀ {s₀ s₉ fuel}
    , exec fuel (Block for_4806375509446804985_body) s₀ = s₉
    → Spec C s₀ s₉
  }
:= by
  constructor
  intros s₀ s₉ fuel

  unfold Spec for_4806375509446804985_body
  rcases s₀ with ⟨evm₀, store₀⟩ | _ | c <;> dsimp only
  rotate_left 1
  · aesop
  · aesop
  swap
  generalize hok : Ok evm₀ store₀ = s₀
  intros h _
  revert h

  -- abstraction offsetting
  rw [cons]
  generalize hxs : Block _ = xs
  abstract if_6183625948864629624_abs_of_code if_6183625948864629624 with ss hs
  try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro ss (And.intro hs ?_)
  swap; clear hs
  try revert h'
  revert h
  subst xs
  
  rw [cons]; simp only [LetCall', AssignCall']
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- EXPR 
  try simp
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (addk_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  
  -- tacticsOfStmt offsetting
  try rw [nil]
  try simp [Bool.toUInt256, UInt256.size]
  intros h
  exact h


end

end Peano.Common
