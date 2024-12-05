import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_3812165059632449189
import Generated.erc20shim.ERC20Shim.abi_encode_tuple_address
import Generated.erc20shim.ERC20Shim.Common.if_4692225504622348326
import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.erc20shim.ERC20Shim.Common.if_5042234445269809685
import Generated.erc20shim.ERC20Shim.abi_encode_uint256

import Generated.erc20shim.ERC20Shim.fun__approve_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def A_fun__approve  (var_owner var_spender var_value var_emitEvent : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun__approve_abs_of_concrete {s₀ s₉ : State} { var_owner var_spender var_value var_emitEvent} :
  Spec (fun__approve_concrete_of_code.1  var_owner var_spender var_value var_emitEvent) s₀ s₉ →
  Spec (A_fun__approve  var_owner var_spender var_value var_emitEvent) s₀ s₉ := by
  unfold fun__approve_concrete_of_code A_fun__approve
  sorry

end

end Generated.erc20shim.ERC20Shim
