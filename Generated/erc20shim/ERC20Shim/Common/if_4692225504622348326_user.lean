import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_tuple_address

import Generated.erc20shim.ERC20Shim.Common.if_4692225504622348326_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_if_4692225504622348326 (s₀ s₉ : State) : Prop := sorry

lemma if_4692225504622348326_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4692225504622348326_concrete_of_code s₀ s₉ →
  Spec A_if_4692225504622348326 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
