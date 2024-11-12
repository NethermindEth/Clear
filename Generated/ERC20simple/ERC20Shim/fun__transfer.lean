import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_8836250053273208363
import Generated.ERC20simple.ERC20Shim.abi_encode_tuple_address
import Generated.ERC20simple.ERC20Shim.Common.if_3919842492790420297
import Generated.ERC20simple.ERC20Shim.fun_update

import Generated.ERC20simple.ERC20Shim.fun__transfer_gen

import Generated.ERC20simple.ERC20Shim.fun__transfer_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

lemma fun__transfer_abs_of_code {s₀ s₉ : State} { var_from var_to var_value} {fuel : Nat} :
  execCall fuel fun__transfer [] (s₀, [var_from, var_to, var_value]) = s₉ →
  Spec (A_fun__transfer  var_from var_to var_value) s₀ s₉
:= λ h ↦ fun__transfer_abs_of_concrete (fun__transfer_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
