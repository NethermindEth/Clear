import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.fun_totalSupply_gen

import Generated.erc20shim.ERC20Shim.fun_totalSupply_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma fun_totalSupply_abs_of_code {s₀ s₉ : State} {var } {fuel : Nat} :
  execCall fuel fun_totalSupply [var] (s₀, []) = s₉ →
  Spec (A_fun_totalSupply var ) s₀ s₉
:= λ h ↦ fun_totalSupply_abs_of_concrete (fun_totalSupply_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
