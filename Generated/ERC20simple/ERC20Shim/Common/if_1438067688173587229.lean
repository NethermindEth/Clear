import Clear.ReasoningPrinciple


import Generated.ERC20simple.ERC20Shim.Common.if_1438067688173587229_gen

import Generated.ERC20simple.ERC20Shim.Common.if_1438067688173587229_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma if_1438067688173587229_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_1438067688173587229 s₀ = s₉ →
        Spec A_if_1438067688173587229 s₀ s₉ :=
  λ _ h ↦ if_1438067688173587229_abs_of_concrete (if_1438067688173587229_concrete_of_code.2 h)

end

end ERC20Shim.Common
