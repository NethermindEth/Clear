import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.panic_error_0x41

import Generated.ERC20simple.ERC20Shim.Common.if_9222169807163418225_gen

import Generated.ERC20simple.ERC20Shim.Common.if_9222169807163418225_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma if_9222169807163418225_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_9222169807163418225 s₀ = s₉ →
        Spec A_if_9222169807163418225 s₀ s₉ :=
  λ _ h ↦ if_9222169807163418225_abs_of_concrete (if_9222169807163418225_concrete_of_code.2 h)

end

end ERC20Shim.Common
