import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_2130076443351184838
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.fun__approve

import Generated.erc20shim.ERC20Shim.Common.if_5327145078839977110_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def A_if_5327145078839977110 (s₀ s₉ : State) : Prop := sorry

lemma if_5327145078839977110_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5327145078839977110_concrete_of_code s₀ s₉ →
  Spec A_if_5327145078839977110 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
