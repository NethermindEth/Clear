import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.for_4806375509446804985
import Generated.peano.Peano.addk

import Generated.peano.Peano.mulk_gen

import Generated.peano.Peano.mulk_user


namespace Generated.peano.Peano

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common Generated.peano Peano

lemma mulk_abs_of_code {s₀ s₉ : State} {y x k} {fuel : Nat} :
  execCall fuel mulk [y] (s₀, [x, k]) = s₉ →
  Spec (A_mulk y x k) s₀ s₉
:= λ h ↦ mulk_abs_of_concrete (mulk_concrete_of_code.2 h)

end

end Generated.peano.Peano
