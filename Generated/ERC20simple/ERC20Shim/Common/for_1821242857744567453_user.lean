import Clear.ReasoningPrinciple


import Generated.ERC20simple.ERC20Shim.Common.for_1821242857744567453_gen


namespace ERC20Shim.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def ACond_for_1821242857744567453 (s₀ : State) : Literal := sorry 
def APost_for_1821242857744567453 (s₀ s₉ : State) : Prop := sorry
def ABody_for_1821242857744567453 (s₀ s₉ : State) : Prop := sorry
def AFor_for_1821242857744567453 (s₀ s₉ : State) : Prop := sorry

lemma for_1821242857744567453_cond_abs_of_code {s₀ fuel} : eval fuel for_1821242857744567453_cond (s₀) = (s₀, ACond_for_1821242857744567453 (s₀)) := by
  unfold eval ACond_for_1821242857744567453
  sorry

lemma for_1821242857744567453_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_1821242857744567453_post_concrete_of_code s₀ s₉ →
  Spec APost_for_1821242857744567453 s₀ s₉ := by
  sorry

lemma for_1821242857744567453_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_1821242857744567453_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_1821242857744567453 s₀ s₉ := by
  sorry

lemma AZero_for_1821242857744567453 : ∀ s₀, isOk s₀ → ACond_for_1821242857744567453 (👌 s₀) = 0 → AFor_for_1821242857744567453 s₀ s₀ := sorry
lemma AOk_for_1821242857744567453 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_1821242857744567453 s₀ = 0 → ABody_for_1821242857744567453 s₀ s₂ → APost_for_1821242857744567453 s₂ s₄ → Spec AFor_for_1821242857744567453 s₄ s₅ → AFor_for_1821242857744567453 s₀ s₅
:= sorry
lemma AContinue_for_1821242857744567453 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_1821242857744567453 s₀ = 0 → ABody_for_1821242857744567453 s₀ s₂ → Spec APost_for_1821242857744567453 (🧟s₂) s₄ → Spec AFor_for_1821242857744567453 s₄ s₅ → AFor_for_1821242857744567453 s₀ s₅ := sorry
lemma ABreak_for_1821242857744567453 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_1821242857744567453 s₀ = 0 → ABody_for_1821242857744567453 s₀ s₂ → AFor_for_1821242857744567453 s₀ (🧟s₂) := sorry
lemma ALeave_for_1821242857744567453 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_1821242857744567453 s₀ = 0 → ABody_for_1821242857744567453 s₀ s₂ → AFor_for_1821242857744567453 s₀ s₂ := sorry

end

end ERC20Shim.Common
