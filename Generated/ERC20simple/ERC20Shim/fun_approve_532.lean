import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_7933877964017211044
import Generated.ERC20simple.ERC20Shim.abi_encode_tuple_address
import Generated.ERC20simple.ERC20Shim.Common.if_7567335688764008016
import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_mapping_address_uint256_of_address
import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.ERC20simple.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.ERC20simple.ERC20Shim.Common.if_1708065363866081018
import Generated.ERC20simple.ERC20Shim.abi_encode_uint256

import Generated.ERC20simple.ERC20Shim.fun_approve_532_gen

import Generated.ERC20simple.ERC20Shim.fun_approve_532_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

lemma fun_approve_532_abs_of_code {s₀ s₉ : State} { var_owner var_spender var_value var_emitEvent} {fuel : Nat} :
  execCall fuel fun_approve_532 [] (s₀, [var_owner, var_spender, var_value, var_emitEvent]) = s₉ →
  Spec (A_fun_approve_532  var_owner var_spender var_value var_emitEvent) s₀ s₉
:= λ h ↦ fun_approve_532_abs_of_concrete (fun_approve_532_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
