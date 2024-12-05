import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_uint256

import Generated.erc20shim.ERC20Shim.Common.if_5042234445269809685_gen

import Generated.erc20shim.ERC20Shim.Common.if_5042234445269809685_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

lemma if_5042234445269809685_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_5042234445269809685 s₀ = s₉ →
        Spec A_if_5042234445269809685 s₀ s₉ :=
  λ _ h ↦ if_5042234445269809685_abs_of_concrete (if_5042234445269809685_concrete_of_code.2 h)

end

end ERC20Shim.Common
