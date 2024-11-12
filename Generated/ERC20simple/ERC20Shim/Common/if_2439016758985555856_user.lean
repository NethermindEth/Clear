import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_address_uint256_uint256

import Generated.ERC20simple.ERC20Shim.Common.if_2439016758985555856_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_if_2439016758985555856 (s₀ s₉ : State) : Prop := sorry

lemma if_2439016758985555856_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2439016758985555856_concrete_of_code s₀ s₉ →
  Spec A_if_2439016758985555856 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
