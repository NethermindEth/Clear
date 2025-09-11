import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.if_6183625948864629624
import Generated.peano.Peano.addk

import Generated.peano.Peano.Common.for_4806375509446804985_gen


namespace Peano.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common Generated.peano Peano

def ACond_for_4806375509446804985 (s₀ : State) : Literal := 1
def APost_for_4806375509446804985 (s₀ s₉ : State) : Prop := s₉ = s₀⟦"k"↦(s₀["k"]!) - 1⟧
def ABody_for_4806375509446804985 (s₀ s₉ : State) : Prop := s₉ = if s₀["k"]! = 0 then 💔 s₀ else s₀⟦"y"↦(s₀["y"]!) + (s₀["x"]!)⟧
def AFor_for_4806375509446804985 (s₀ s₉ : State) : Prop := (s₉["y"]!) = (s₀["y"]!) + (s₀["x"]!) * (s₀["k"]!) ∧ isPure s₀ s₉ ∧ s₉.isOk

lemma for_4806375509446804985_cond_abs_of_code {s₀ fuel} : eval fuel for_4806375509446804985_cond (s₀) = (s₀, ACond_for_4806375509446804985 (s₀)) := by
  unfold eval ACond_for_4806375509446804985
  aesop_spec

lemma for_4806375509446804985_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_4806375509446804985_post_concrete_of_code s₀ s₉ →
  Spec APost_for_4806375509446804985 s₀ s₉ := by
  unfold for_4806375509446804985_post_concrete_of_code APost_for_4806375509446804985 Spec
  aesop_spec

lemma for_4806375509446804985_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_4806375509446804985_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_4806375509446804985 s₀ s₉ := by
  unfold for_4806375509446804985_body_concrete_of_code ABody_for_4806375509446804985 A_if_6183625948864629624 Spec
  aesop_spec

lemma AZero_for_4806375509446804985 : ∀ s₀, isOk s₀ → ACond_for_4806375509446804985 (👌 s₀) = 0 → AFor_for_4806375509446804985 s₀ s₀ := by
  unfold ACond_for_4806375509446804985
  aesop_spec

lemma AOk_for_4806375509446804985 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_4806375509446804985 s₀ = 0 → ABody_for_4806375509446804985 s₀ s₂ → APost_for_4806375509446804985 s₂ s₄ → Spec AFor_for_4806375509446804985 s₄ s₅ → AFor_for_4806375509446804985 s₀ s₅
:= by
  unfold AFor_for_4806375509446804985 APost_for_4806375509446804985 ABody_for_4806375509446804985
  intros s₀ s₂ s₄ s₅ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  rcases s₄ with ⟨evm, vs⟩ | _ | v <;> [skip; aesop_spec; skip]
  · clr_spec at h₇
    split_ands <;> [rw [h₆] at h₇; aesop_spec; tauto]
    · split_ifs at h₅
      · aesop_spec
      · simp only [h₇, h₅] at *
        clr_varstore
        ring
  · have : isOk (s₂⟦"k"↦s₂["k"]! - 1⟧) := by aesop
    simp [h₆.symm] at this

lemma AContinue_for_4806375509446804985 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_4806375509446804985 s₀ = 0 → ABody_for_4806375509446804985 s₀ s₂ → Spec APost_for_4806375509446804985 (🧟s₂) s₄ → Spec AFor_for_4806375509446804985 s₄ s₅ → AFor_for_4806375509446804985 s₀ s₅ := by
  unfold ABody_for_4806375509446804985
  aesop_spec

lemma ABreak_for_4806375509446804985 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_4806375509446804985 s₀ = 0 → ABody_for_4806375509446804985 s₀ s₂ → AFor_for_4806375509446804985 s₀ (🧟s₂) := by
  unfold ABody_for_4806375509446804985 AFor_for_4806375509446804985
  aesop_spec

lemma ALeave_for_4806375509446804985 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_4806375509446804985 s₀ = 0 → ABody_for_4806375509446804985 s₀ s₂ → AFor_for_4806375509446804985 s₀ s₂ := by
  unfold ABody_for_4806375509446804985
  aesop_spec

end

end Peano.Common
