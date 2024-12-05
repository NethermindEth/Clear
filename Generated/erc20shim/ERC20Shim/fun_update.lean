import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.switch_2364266820542243941
import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.erc20shim.ERC20Shim.checked_add_uint256
import Generated.erc20shim.ERC20Shim.Common.switch_1041419350816529734
import Generated.erc20shim.ERC20Shim.abi_encode_uint256

import Generated.erc20shim.ERC20Shim.fun_update_gen

import Generated.erc20shim.ERC20Shim.fun_update_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

lemma fun_update_abs_of_code {s₀ s₉ : State} { var_from var_to var_value} {fuel : Nat} :
  execCall fuel fun_update [] (s₀, [var_from, var_to, var_value]) = s₉ →
  Spec (A_fun_update  var_from var_to var_value) s₀ s₉
:= λ h ↦ fun_update_abs_of_concrete (fun_update_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
