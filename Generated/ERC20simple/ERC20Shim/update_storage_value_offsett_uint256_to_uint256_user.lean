import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.update_byte_slice_shift

import Generated.ERC20simple.ERC20Shim.update_storage_value_offsett_uint256_to_uint256_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_update_storage_value_offsett_uint256_to_uint256  (slot value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma update_storage_value_offsett_uint256_to_uint256_abs_of_concrete {s₀ s₉ : State} { slot value} :
  Spec (update_storage_value_offsett_uint256_to_uint256_concrete_of_code.1  slot value) s₀ s₉ →
  Spec (A_update_storage_value_offsett_uint256_to_uint256  slot value) s₀ s₉ := by
  unfold update_storage_value_offsett_uint256_to_uint256_concrete_of_code A_update_storage_value_offsett_uint256_to_uint256
  sorry

end

end Generated.ERC20simple.ERC20Shim
