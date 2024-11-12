import Clear.ReasoningPrinciple


import Generated.ERC20simple.ERC20Shim.fun_decimals_gen

import Generated.ERC20simple.ERC20Shim.fun_decimals_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma fun_decimals_abs_of_code {s₀ s₉ : State} {var } {fuel : Nat} :
  execCall fuel fun_decimals [var] (s₀, []) = s₉ →
  Spec (A_fun_decimals var ) s₀ s₉
:= λ h ↦ fun_decimals_abs_of_concrete (fun_decimals_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
