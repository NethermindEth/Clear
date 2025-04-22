import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.panic_error_0x22

import Generated.erc20shim.ERC20Shim.Common.if_384845947645085899_gen

import Generated.erc20shim.ERC20Shim.Common.if_384845947645085899_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

lemma if_384845947645085899_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_384845947645085899 s₀ = s₉ →
        Spec A_if_384845947645085899 s₀ s₉ :=
  λ _ h ↦ if_384845947645085899_abs_of_concrete (if_384845947645085899_concrete_of_code.2 h)

end

end ERC20Shim.Common
