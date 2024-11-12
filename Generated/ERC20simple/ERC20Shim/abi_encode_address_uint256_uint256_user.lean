import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_address
import Generated.ERC20simple.ERC20Shim.abi_encode_uint256_to_uint256

import Generated.ERC20simple.ERC20Shim.abi_encode_address_uint256_uint256_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_abi_encode_address_uint256_uint256 (tail : Identifier) (headStart value0 value1 value2 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_address_uint256_uint256_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2} :
  Spec (abi_encode_address_uint256_uint256_concrete_of_code.1 tail headStart value0 value1 value2) s₀ s₉ →
  Spec (A_abi_encode_address_uint256_uint256 tail headStart value0 value1 value2) s₀ s₉ := by
  unfold abi_encode_address_uint256_uint256_concrete_of_code A_abi_encode_address_uint256_uint256
  sorry

end

end Generated.ERC20simple.ERC20Shim
