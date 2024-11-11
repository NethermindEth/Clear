import Clear.ReasoningPrinciple


import Generated.ERC20.GetCode.Common.if_8423444027764651193_gen

import Generated.ERC20.GetCode.Common.if_8423444027764651193_user


namespace GetCode.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma if_8423444027764651193_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_8423444027764651193 s₀ = s₉ →
        Spec A_if_8423444027764651193 s₀ s₉ :=
  λ _ h ↦ if_8423444027764651193_abs_of_concrete (if_8423444027764651193_concrete_of_code.2 h)

end

end GetCode.Common
