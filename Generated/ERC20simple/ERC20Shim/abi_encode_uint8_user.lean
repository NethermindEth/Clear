import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_uint8_to_uint8

import Generated.ERC20simple.ERC20Shim.abi_encode_uint8_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_abi_encode_uint8 (tail : Identifier) (headStart value0 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_uint8_abs_of_concrete {s₀ s₉ : State} {tail headStart value0} :
  Spec (abi_encode_uint8_concrete_of_code.1 tail headStart value0) s₀ s₉ →
  Spec (A_abi_encode_uint8 tail headStart value0) s₀ s₉ := by
  unfold abi_encode_uint8_concrete_of_code A_abi_encode_uint8
  sorry

end

end Generated.ERC20simple.ERC20Shim
