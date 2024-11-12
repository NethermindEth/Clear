import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.for_727972558926940900
import Generated.peano.Peano.mulk

import Generated.peano.Peano.expk_gen


namespace Generated.peano.Peano

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common Generated.peano Peano

def A_expk (y : Identifier) (x k : Literal) (s₀ s₉ : State) : Prop := sorry

lemma expk_abs_of_concrete {s₀ s₉ : State} {y x k} :
  Spec (expk_concrete_of_code.1 y x k) s₀ s₉ →
  Spec (A_expk y x k) s₀ s₉ := by
  unfold expk_concrete_of_code A_expk
  sorry

end

end Generated.peano.Peano
