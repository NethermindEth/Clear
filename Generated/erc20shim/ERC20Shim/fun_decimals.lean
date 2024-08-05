import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.fun_decimals_gen

import Generated.erc20shim.ERC20Shim.fun_decimals_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma fun_decimals_abs_of_code {s₀ s₉ : State} {var } {fuel : Nat} :
  execCall fuel fun_decimals [var] (s₀, []) = s₉ →
  Spec (A_fun_decimals var ) s₀ s₉
:= λ h ↦ fun_decimals_abs_of_concrete (fun_decimals_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
