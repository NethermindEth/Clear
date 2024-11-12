import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.update_byte_slice_shift

import Generated.ERC20simple.ERC20Shim.update_storage_value_offsett_uint256_to_uint256_gen

import Generated.ERC20simple.ERC20Shim.update_storage_value_offsett_uint256_to_uint256_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma update_storage_value_offsett_uint256_to_uint256_abs_of_code {s₀ s₉ : State} { slot value} {fuel : Nat} :
  execCall fuel update_storage_value_offsett_uint256_to_uint256 [] (s₀, [slot, value]) = s₉ →
  Spec (A_update_storage_value_offsett_uint256_to_uint256  slot value) s₀ s₉
:= λ h ↦ update_storage_value_offsett_uint256_to_uint256_abs_of_concrete (update_storage_value_offsett_uint256_to_uint256_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
