import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_2130076443351184838
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.fun__approve

import Generated.erc20shim.ERC20Shim.Common.if_5327145078839977110_gen

import Generated.erc20shim.ERC20Shim.Common.if_5327145078839977110_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

lemma if_5327145078839977110_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_5327145078839977110 s₀ = s₉ →
        Spec A_if_5327145078839977110 s₀ s₉ :=
  λ _ h ↦ if_5327145078839977110_abs_of_concrete (if_5327145078839977110_concrete_of_code.2 h)

end

end ERC20Shim.Common
