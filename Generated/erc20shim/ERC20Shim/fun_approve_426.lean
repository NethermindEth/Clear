import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun__approve

import Generated.erc20shim.ERC20Shim.fun_approve_426_gen

import Generated.erc20shim.ERC20Shim.fun_approve_426_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

lemma fun_approve_426_abs_of_code {s₀ s₉ : State} { var_owner var_spender var_value} {fuel : Nat} :
  execCall fuel fun_approve_426 [] (s₀, [var_owner, var_spender, var_value]) = s₉ →
  Spec (A_fun_approve_426  var_owner var_spender var_value) s₀ s₉
:= λ h ↦ fun_approve_426_abs_of_concrete (fun_approve_426_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
