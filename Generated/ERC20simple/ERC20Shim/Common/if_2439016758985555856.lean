import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_address_uint256_uint256

import Generated.ERC20simple.ERC20Shim.Common.if_2439016758985555856_gen

import Generated.ERC20simple.ERC20Shim.Common.if_2439016758985555856_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma if_2439016758985555856_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_2439016758985555856 s₀ = s₉ →
        Spec A_if_2439016758985555856 s₀ s₉ :=
  λ _ h ↦ if_2439016758985555856_abs_of_concrete (if_2439016758985555856_concrete_of_code.2 h)

end

end ERC20Shim.Common
