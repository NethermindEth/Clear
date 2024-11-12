import Clear.ReasoningPrinciple


import Generated.ERC20simple.ERC20Shim.Common.if_5295847412656974480_gen

import Generated.ERC20simple.ERC20Shim.Common.if_5295847412656974480_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma if_5295847412656974480_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_5295847412656974480 s₀ = s₉ →
        Spec A_if_5295847412656974480 s₀ s₉ :=
  λ _ h ↦ if_5295847412656974480_abs_of_concrete (if_5295847412656974480_concrete_of_code.2 h)

end

end ERC20Shim.Common
