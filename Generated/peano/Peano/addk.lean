import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.for_84821961910748561

import Generated.peano.Peano.addk_gen

import Generated.peano.Peano.addk_user


namespace Generated.peano.Peano

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common 

lemma addk_abs_of_code {s₀ s₉ : State} {y x k} {fuel : Nat} :
  execCall fuel addk [y] (s₀, [x, k]) = s₉ →
  Spec (A_addk y x k) s₀ s₉
:= λ h ↦ addk_abs_of_concrete (addk_concrete_of_code.2 h)

end

end Generated.peano.Peano
