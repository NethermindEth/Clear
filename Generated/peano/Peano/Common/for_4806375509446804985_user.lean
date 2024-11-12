import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.if_6183625948864629624
import Generated.peano.Peano.addk

import Generated.peano.Peano.Common.for_4806375509446804985_gen


namespace Peano.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common Generated.peano Peano

def ACond_for_4806375509446804985 (s₀ : State) : Literal := sorry 
def APost_for_4806375509446804985 (s₀ s₉ : State) : Prop := sorry
def ABody_for_4806375509446804985 (s₀ s₉ : State) : Prop := sorry
def AFor_for_4806375509446804985 (s₀ s₉ : State) : Prop := sorry

lemma for_4806375509446804985_cond_abs_of_code {s₀ fuel} : eval fuel for_4806375509446804985_cond (s₀) = (s₀, ACond_for_4806375509446804985 (s₀)) := by
  unfold eval ACond_for_4806375509446804985
  sorry

lemma for_4806375509446804985_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_4806375509446804985_post_concrete_of_code s₀ s₉ →
  Spec APost_for_4806375509446804985 s₀ s₉ := by
  sorry

lemma for_4806375509446804985_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_4806375509446804985_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_4806375509446804985 s₀ s₉ := by
  sorry

lemma AZero_for_4806375509446804985 : ∀ s₀, isOk s₀ → ACond_for_4806375509446804985 (👌 s₀) = 0 → AFor_for_4806375509446804985 s₀ s₀ := sorry
lemma AOk_for_4806375509446804985 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_4806375509446804985 s₀ = 0 → ABody_for_4806375509446804985 s₀ s₂ → APost_for_4806375509446804985 s₂ s₄ → Spec AFor_for_4806375509446804985 s₄ s₅ → AFor_for_4806375509446804985 s₀ s₅
:= sorry
lemma AContinue_for_4806375509446804985 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_4806375509446804985 s₀ = 0 → ABody_for_4806375509446804985 s₀ s₂ → Spec APost_for_4806375509446804985 (🧟s₂) s₄ → Spec AFor_for_4806375509446804985 s₄ s₅ → AFor_for_4806375509446804985 s₀ s₅ := sorry
lemma ABreak_for_4806375509446804985 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_4806375509446804985 s₀ = 0 → ABody_for_4806375509446804985 s₀ s₂ → AFor_for_4806375509446804985 s₀ (🧟s₂) := sorry
lemma ALeave_for_4806375509446804985 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_4806375509446804985 s₀ = 0 → ABody_for_4806375509446804985 s₀ s₂ → AFor_for_4806375509446804985 s₀ s₂ := sorry

end

end Peano.Common
