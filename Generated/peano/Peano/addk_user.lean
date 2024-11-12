import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.for_84821961910748561

import Generated.peano.Peano.addk_gen


namespace Generated.peano.Peano

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common 

def A_addk (y : Identifier) (x k : Literal) (s₀ s₉ : State) : Prop := sorry

lemma addk_abs_of_concrete {s₀ s₉ : State} {y x k} :
  Spec (addk_concrete_of_code.1 y x k) s₀ s₉ →
  Spec (A_addk y x k) s₀ s₉ := by
  unfold addk_concrete_of_code A_addk
  sorry

end

end Generated.peano.Peano
