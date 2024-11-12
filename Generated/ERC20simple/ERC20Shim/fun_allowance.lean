import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_mapping_address_uint256_of_address
import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address

import Generated.ERC20simple.ERC20Shim.fun_allowance_gen

import Generated.ERC20simple.ERC20Shim.fun_allowance_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma fun_allowance_abs_of_code {s₀ s₉ : State} {var var_owner var_spender} {fuel : Nat} :
  execCall fuel fun_allowance [var] (s₀, [var_owner, var_spender]) = s₉ →
  Spec (A_fun_allowance var var_owner var_spender) s₀ s₉
:= λ h ↦ fun_allowance_abs_of_concrete (fun_allowance_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
