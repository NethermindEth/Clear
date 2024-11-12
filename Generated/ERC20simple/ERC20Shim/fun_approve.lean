import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.fun_msgSender
import Generated.ERC20simple.ERC20Shim.fun__approve

import Generated.ERC20simple.ERC20Shim.fun_approve_gen

import Generated.ERC20simple.ERC20Shim.fun_approve_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma fun_approve_abs_of_code {s₀ s₉ : State} {var var_spender var_value} {fuel : Nat} :
  execCall fuel fun_approve [var] (s₀, [var_spender, var_value]) = s₉ →
  Spec (A_fun_approve var var_spender var_value) s₀ s₉
:= λ h ↦ fun_approve_abs_of_concrete (fun_approve_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
