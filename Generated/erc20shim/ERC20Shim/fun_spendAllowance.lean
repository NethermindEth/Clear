import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun_allowance
import Generated.erc20shim.ERC20Shim.Common.if_8475192588736690919
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.fun__approve

import Generated.erc20shim.ERC20Shim.fun_spendAllowance_gen

import Generated.erc20shim.ERC20Shim.fun_spendAllowance_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

lemma fun_spendAllowance_abs_of_code {s₀ s₉ : State} { var_owner var_spender var_value} {fuel : Nat} :
  execCall fuel fun_spendAllowance [] (s₀, [var_owner, var_spender, var_value]) = s₉ →
  Spec (A_fun_spendAllowance  var_owner var_spender var_value) s₀ s₉
:= λ h ↦ fun_spendAllowance_abs_of_concrete (fun_spendAllowance_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
