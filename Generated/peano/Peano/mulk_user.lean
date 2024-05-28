import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.for_4806375509446804985
import Generated.peano.Peano.addk

import Generated.peano.Peano.mulk_gen


namespace Generated.peano.Peano

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common Generated.peano Peano

def A_mulk (y : Identifier) (x k : Literal) (s₀ s₉ : State) : Prop := s₉ = s₀⟦y ↦ (x * k)⟧

lemma mulk_abs_of_concrete {s₀ s₉ : State} {y x k} :
  Spec (mulk_concrete_of_code.1 y x k) s₀ s₉ →
  Spec (A_mulk y x k) s₀ s₉ := by
  unfold mulk_concrete_of_code A_mulk AFor_for_4806375509446804985
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  rintro h ⟨h₁, ⟨ss, h₂⟩⟩
  clr_funargs at ss
  clr_spec at ss
  aesop_spec
  congr
  aesop_spec

end

end Generated.peano.Peano
