import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.if_6183625948864629624

import Generated.peano.Peano.Common.for_84821961910748561_gen


namespace Peano.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common

def ACond_for_84821961910748561 (s₀ : State) : Literal := 1
def APost_for_84821961910748561 (s₀ s₉ : State) : Prop := s₉ = s₀⟦"k"↦(s₀["k"]!) - 1⟧
def ABody_for_84821961910748561 (s₀ s₉ : State) : Prop := s₉ = if s₀["k"]! = 0 then 💔 s₀ else s₀⟦"x"↦(s₀["x"]!) + 1⟧
def AFor_for_84821961910748561 (s₀ s₉ : State) : Prop := (s₀["x"]!) + (s₀["k"]!) = (s₉["x"]!) ∧ isPure s₀ s₉ ∧ s₉.isOk

lemma for_84821961910748561_cond_abs_of_code {s₀ fuel} : eval fuel for_84821961910748561_cond (s₀) = (s₀, ACond_for_84821961910748561 (s₀)) := by
  unfold eval ACond_for_84821961910748561
  aesop_spec

lemma for_84821961910748561_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_84821961910748561_post_concrete_of_code s₀ s₉ →
  Spec APost_for_84821961910748561 s₀ s₉ := by
  unfold APost_for_84821961910748561 for_84821961910748561_post_concrete_of_code
  aesop_spec

lemma for_84821961910748561_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_84821961910748561_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_84821961910748561 s₀ s₉ := by
  unfold for_84821961910748561_body_concrete_of_code ABody_for_84821961910748561 A_if_6183625948864629624
  apply spec_eq; simp
  aesop_spec

lemma AZero_for_84821961910748561 : ∀ s₀, isOk s₀ → ACond_for_84821961910748561 (👌 s₀) = 0 → AFor_for_84821961910748561 s₀ s₀ := by
  unfold ACond_for_84821961910748561
  aesop_spec

lemma AOk_for_84821961910748561 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_84821961910748561 s₀ = 0 → ABody_for_84821961910748561 s₀ s₂ → APost_for_84821961910748561 s₂ s₄ → Spec AFor_for_84821961910748561 s₄ s₅ → AFor_for_84821961910748561 s₀ s₅ := by
  unfold ABody_for_84821961910748561 APost_for_84821961910748561 AFor_for_84821961910748561
  intros s₀ s₂ s₄ s₅ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  rcases s₄ with _ | _ | _ <;> [skip; aesop_spec; skip]
  · clr_spec at h₇
    split_ands <;> [skip; aesop_spec; tauto]
    by_cases eq : s₀["k"]! = 0 <;> simp [eq] at h₅ <;> [simp [h₅] at h₂; skip]
    rw [h₆] at h₇; rw [h₇.1.symm, h₅]; clr_varstore
    ring
  · have h : isOk (s₂⟦"k"↦(s₂["k"]!) - 1⟧) := by aesop
    simp [h₆.symm] at h

lemma AContinue_for_84821961910748561 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_84821961910748561 s₀ = 0 → ABody_for_84821961910748561 s₀ s₂ → Spec APost_for_84821961910748561 (🧟s₂) s₄ → Spec AFor_for_84821961910748561 s₄ s₅ → AFor_for_84821961910748561 s₀ s₅ := by
  unfold ABody_for_84821961910748561
  aesop_spec

lemma ABreak_for_84821961910748561 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_84821961910748561 s₀ = 0 → ABody_for_84821961910748561 s₀ s₂ → AFor_for_84821961910748561 s₀ (🧟s₂) := by
  unfold ABody_for_84821961910748561 AFor_for_84821961910748561
  aesop_spec

lemma ALeave_for_84821961910748561 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_84821961910748561 s₀ = 0 → ABody_for_84821961910748561 s₀ s₂ → AFor_for_84821961910748561 s₀ s₂ := by
  unfold ABody_for_84821961910748561
  aesop_spec

end

end Peano.Common
