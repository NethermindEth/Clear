import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_9141570808380448040
import Generated.erc20shim.ERC20Shim.abi_encode_tuple_address
import Generated.erc20shim.ERC20Shim.Common.if_2395397427938978657
import Generated.erc20shim.ERC20Shim.fun_update

import Generated.erc20shim.ERC20Shim.fun__transfer_gen

import Generated.erc20shim.ERC20Shim.fun__transfer_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

lemma fun__transfer_abs_of_code {s₀ s₉ : State} { var_from var_to var_value} {fuel : Nat} :
  execCall fuel fun__transfer [] (s₀, [var_from, var_to, var_value]) = s₉ →
  Spec (A_fun__transfer  var_from var_to var_value) s₀ s₉
:= λ h ↦ fun__transfer_abs_of_concrete (fun__transfer_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
