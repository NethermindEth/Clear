import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_address

import Generated.erc20shim.ERC20Shim.abi_encode_tuple_address_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_abi_encode_tuple_address (tail : Identifier) (headStart value0 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_tuple_address_abs_of_concrete {s₀ s₉ : State} {tail headStart value0} :
  Spec (abi_encode_tuple_address_concrete_of_code.1 tail headStart value0) s₀ s₉ →
  Spec (A_abi_encode_tuple_address tail headStart value0) s₀ s₉ := by
  unfold abi_encode_tuple_address_concrete_of_code A_abi_encode_tuple_address
  sorry

end

end Generated.erc20shim.ERC20Shim
