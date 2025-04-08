import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256

import Generated.erc20shim.ERC20Shim.Common.if_3856757177752523473_gen

import Generated.erc20shim.ERC20Shim.Common.if_3856757177752523473_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

lemma if_3856757177752523473_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_3856757177752523473 s₀ = s₉ →
        Spec A_if_3856757177752523473 s₀ s₉ :=
  λ _ h ↦ if_3856757177752523473_abs_of_concrete (if_3856757177752523473_concrete_of_code.2 h)

end

end ERC20Shim.Common
