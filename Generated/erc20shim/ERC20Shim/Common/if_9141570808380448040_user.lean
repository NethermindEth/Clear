import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_tuple_address

import Generated.erc20shim.ERC20Shim.Common.if_9141570808380448040_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_if_9141570808380448040 (s₀ s₉ : State) : Prop := sorry

lemma if_9141570808380448040_abs_of_concrete {s₀ s₉ : State} :
  Spec if_9141570808380448040_concrete_of_code s₀ s₉ →
  Spec A_if_9141570808380448040 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
