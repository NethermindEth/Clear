import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address

import Generated.erc20shim.ERC20Shim.fun_balanceOf_gen

import Generated.erc20shim.ERC20Shim.fun_balanceOf_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

lemma fun_balanceOf_abs_of_code {s₀ s₉ : State} {var var_account} {fuel : Nat} :
  execCall fuel fun_balanceOf [var] (s₀, [var_account]) = s₉ →
  Spec (A_fun_balanceOf var var_account) s₀ s₉
:= λ h ↦ fun_balanceOf_abs_of_concrete (fun_balanceOf_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
