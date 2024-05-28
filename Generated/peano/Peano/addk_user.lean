import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.for_84821961910748561

import Generated.peano.Peano.addk_gen


namespace Generated.peano.Peano

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common 

def A_addk (y : Identifier) (x k : Literal) (s₀ s₉ : State) : Prop := s₉ = s₀⟦y ↦ (x + k)⟧

lemma addk_abs_of_concrete {s₀ s₉ : State} {y x k}
: Spec (addk_concrete_of_code.1 y x k) s₀ s₉ →
  Spec (A_addk y x k) s₀ s₉ := by
  unfold addk_concrete_of_code A_addk AFor_for_84821961910748561
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  rintro h ⟨h₁, ⟨ss, h₂⟩⟩
  clr_funargs at ss
  clr_spec at ss
  aesop_spec
  congr
  symm; assumption
  aesop_spec

end

end Generated.peano.Peano
