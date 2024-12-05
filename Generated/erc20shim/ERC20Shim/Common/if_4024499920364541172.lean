import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.Common.if_4024499920364541172_gen

import Generated.erc20shim.ERC20Shim.Common.if_4024499920364541172_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma if_4024499920364541172_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_4024499920364541172 s₀ = s₉ →
        Spec A_if_4024499920364541172 s₀ s₉ :=
  λ _ h ↦ if_4024499920364541172_abs_of_concrete (if_4024499920364541172_concrete_of_code.2 h)

end

end ERC20Shim.Common
