import Clear.ReasoningPrinciple

import Generated.peano.Peano.Common.for_727972558926940900
import Generated.peano.Peano.mulk

import Generated.peano.Peano.expk_gen

import Generated.peano.Peano.expk_user


namespace Generated.peano.Peano

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Peano.Common Generated.peano Peano

lemma expk_abs_of_code {s₀ s₉ : State} {y x k} {fuel : Nat} :
  execCall fuel expk [y] (s₀, [x, k]) = s₉ →
  Spec (A_expk y x k) s₀ s₉
:= λ h ↦ expk_abs_of_concrete (expk_concrete_of_code.2 h)

end

end Generated.peano.Peano
