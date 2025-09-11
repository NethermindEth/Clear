import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.if_6183625948864629624
import Generated.peano.Peano.mulk

import Generated.peano.Peano.Common.for_727972558926940900_gen


namespace Peano.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common Generated.peano Peano

def ACond_for_727972558926940900 (s₀ : State) : Literal := 1
def APost_for_727972558926940900 (s₀ s₉ : State) : Prop := s₉ = s₀⟦"k"↦(s₀["k"]!) - 1⟧
def ABody_for_727972558926940900 (s₀ s₉ : State) : Prop := s₉ = if s₀["k"]! = 0 then 💔 s₀ else s₀⟦"y"↦(s₀["y"]!) * (s₀["x"]!)⟧
def AFor_for_727972558926940900 (s₀ s₉ : State) : Prop := (s₉["y"]!) =  (s₀["y"]!) * (s₀["x"]!) ^ (s₀["k"]!) ∧ isPure s₀ s₉ ∧ s₉.isOk

lemma for_727972558926940900_cond_abs_of_code {s₀ fuel} : eval fuel for_727972558926940900_cond (s₀) = (s₀, ACond_for_727972558926940900 (s₀)) :=
  by unfold eval ACond_for_727972558926940900; aesop_spec

def for_727972558926940900_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_727972558926940900_post_concrete_of_code s₀ s₉ →
  Spec APost_for_727972558926940900 s₀ s₉ := by
  unfold for_727972558926940900_post_concrete_of_code APost_for_727972558926940900
  aesop_spec

def for_727972558926940900_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_727972558926940900_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_727972558926940900 s₀ s₉ := by
  unfold for_727972558926940900_body_concrete_of_code ABody_for_727972558926940900 A_if_6183625948864629624 A_mulk
  apply spec_eq; simp; aesop_spec

lemma AZero_for_727972558926940900 : ∀ s₀, isOk s₀ →
  ACond_for_727972558926940900 (👌 s₀) = 0 →
  AFor_for_727972558926940900 s₀ s₀ := by unfold ACond_for_727972558926940900; aesop_spec

lemma UInt256_zero_unfold : (0 : UInt256) = ⟨0, by decide⟩ := by rfl
lemma UInt256_one_unfold : (1 : UInt256) = ⟨1, by decide⟩ := by rfl

lemma coe_sub {a b : UInt256} (h : a ≤ b) : (((b - a) : UInt256) : ℕ) = b.val - a.val :=
  Fin.coe_sub_iff_le.mpr h

lemma fin_eq_lem {a : UInt256} (h : a ≠ 0) : (a - 1).val = a.val - 1 := by
  have : 1 ≤ a := by rcases a with ⟨_ | a, ha⟩ <;> [simp at h; (simp [Fin.le_iff_val_le_val])]
  rw [coe_sub] <;> simp_all

lemma AOk_for_727972558926940900 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_727972558926940900 s₀ = 0 → ABody_for_727972558926940900 s₀ s₂ → APost_for_727972558926940900 s₂ s₄ → Spec AFor_for_727972558926940900 s₄ s₅ → AFor_for_727972558926940900 s₀ s₅ := by
  unfold APost_for_727972558926940900 ABody_for_727972558926940900 AFor_for_727972558926940900
  intros s₀ s₂ s₄ s₅ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  rcases s₄ with _ | _ | _ <;> [skip; aesop_spec; skip]
  · clr_spec at h₇
    split_ands <;> [skip; aesop_spec; tauto]
    by_cases eq : s₀["k"]! = 0 <;> simp [eq] at h₅ <;> [simp [h₅] at h₂; skip]
    rw [h₆] at h₇; rw [h₇.1, h₅]; clr_varstore
    have : ↑(s₀["k"]! - 1) + 1 < UInt256.size := by simp_arith [fin_eq_lem eq]; zify; omega
    rw [mul_assoc, UInt256.UInt256_pow_succ this]; ring
  · have h : isOk (s₂⟦"k"↦(s₂["k"]!) - 1⟧) := by aesop
    simp [h₆.symm] at h

lemma AContinue_for_727972558926940900 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_727972558926940900 s₀ = 0 → ABody_for_727972558926940900 s₀ s₂ → Spec APost_for_727972558926940900 (🧟s₂) s₄ → Spec AFor_for_727972558926940900 s₄ s₅ → AFor_for_727972558926940900 s₀ s₅ := by
  unfold ABody_for_727972558926940900
  aesop_spec

lemma ABreak_for_727972558926940900 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_727972558926940900 s₀ = 0 → ABody_for_727972558926940900 s₀ s₂ → AFor_for_727972558926940900 s₀ (🧟s₂) := by
  unfold ABody_for_727972558926940900 AFor_for_727972558926940900
  have {a : UInt256} : a ^ (0 : Literal) = 1 := rfl
  aesop_spec

lemma ALeave_for_727972558926940900 :  ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_727972558926940900 s₀ = 0 → ABody_for_727972558926940900 s₀ s₂ → AFor_for_727972558926940900 s₀ s₂ := by
  unfold ABody_for_727972558926940900
  aesop_spec

end

end Peano.Common
