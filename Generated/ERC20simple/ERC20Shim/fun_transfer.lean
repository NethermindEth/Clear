import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.fun_msgSender
import Generated.ERC20simple.ERC20Shim.fun__transfer

import Generated.ERC20simple.ERC20Shim.fun_transfer_gen

import Generated.ERC20simple.ERC20Shim.fun_transfer_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma fun_transfer_abs_of_code {s₀ s₉ : State} {var var_to var_value} {fuel : Nat} :
  execCall fuel fun_transfer [var] (s₀, [var_to, var_value]) = s₉ →
  Spec (A_fun_transfer var var_to var_value) s₀ s₉
:= λ h ↦ fun_transfer_abs_of_concrete (fun_transfer_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
