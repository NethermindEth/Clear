import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.switch_8694440494872382586
import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.ERC20simple.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.ERC20simple.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.ERC20simple.ERC20Shim.checked_add_uint256
import Generated.ERC20simple.ERC20Shim.Common.switch_6048342142894339161
import Generated.ERC20simple.ERC20Shim.abi_encode_uint256

import Generated.ERC20simple.ERC20Shim.fun_update_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def A_fun_update  (var_from var_to var_value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_update_abs_of_concrete {s₀ s₉ : State} { var_from var_to var_value} :
  Spec (fun_update_concrete_of_code.1  var_from var_to var_value) s₀ s₉ →
  Spec (A_fun_update  var_from var_to var_value) s₀ s₉ := by
  unfold fun_update_concrete_of_code A_fun_update
  sorry

end

end Generated.ERC20simple.ERC20Shim
