import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.Common.if_8073281237182003506_gen

import Generated.erc20shim.ERC20Shim.Common.if_8073281237182003506_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma if_8073281237182003506_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_8073281237182003506 s₀ = s₉ →
        Spec A_if_8073281237182003506 s₀ s₉ :=
  λ _ h ↦ if_8073281237182003506_abs_of_concrete (if_8073281237182003506_concrete_of_code.2 h)

end

end ERC20Shim.Common
