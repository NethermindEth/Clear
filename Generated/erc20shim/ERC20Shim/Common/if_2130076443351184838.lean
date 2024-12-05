import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256

import Generated.erc20shim.ERC20Shim.Common.if_2130076443351184838_gen

import Generated.erc20shim.ERC20Shim.Common.if_2130076443351184838_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

lemma if_2130076443351184838_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_2130076443351184838 s₀ = s₉ →
        Spec A_if_2130076443351184838 s₀ s₉ :=
  λ _ h ↦ if_2130076443351184838_abs_of_concrete (if_2130076443351184838_concrete_of_code.2 h)

end

end ERC20Shim.Common
