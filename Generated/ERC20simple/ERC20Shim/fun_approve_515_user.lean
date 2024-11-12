import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_7933877964017211044
import Generated.ERC20simple.ERC20Shim.abi_encode_tuple_address
import Generated.ERC20simple.ERC20Shim.Common.if_7567335688764008016
import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_mapping_address_uint256_of_address
import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.ERC20simple.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.ERC20simple.ERC20Shim.Common.if_1708065363866081018
import Generated.ERC20simple.ERC20Shim.abi_encode_uint256

import Generated.ERC20simple.ERC20Shim.fun_approve_515_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def A_fun_approve_515  (var_owner var_spender var_value var_emitEvent : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_approve_515_abs_of_concrete {s₀ s₉ : State} { var_owner var_spender var_value var_emitEvent} :
  Spec (fun_approve_515_concrete_of_code.1  var_owner var_spender var_value var_emitEvent) s₀ s₉ →
  Spec (A_fun_approve_515  var_owner var_spender var_value var_emitEvent) s₀ s₉ := by
  unfold fun_approve_515_concrete_of_code A_fun_approve_515
  sorry

end

end Generated.ERC20simple.ERC20Shim
