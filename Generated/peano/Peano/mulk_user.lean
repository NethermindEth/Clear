import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.for_4806375509446804985
import Generated.peano.Peano.addk

import Generated.peano.Peano.mulk_gen


namespace Generated.peano.Peano

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common Generated.peano Peano

def A_mulk (y : Identifier) (x k : Literal) (s₀ s₉ : State) : Prop := sorry

lemma mulk_abs_of_concrete {s₀ s₉ : State} {y x k} :
  Spec (mulk_concrete_of_code.1 y x k) s₀ s₉ →
  Spec (A_mulk y x k) s₀ s₉ := by
  unfold mulk_concrete_of_code A_mulk
  sorry

end

end Generated.peano.Peano
