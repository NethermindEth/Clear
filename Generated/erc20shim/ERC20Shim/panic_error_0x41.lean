import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.panic_error_0x41_gen

import Generated.erc20shim.ERC20Shim.panic_error_0x41_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma panic_error_0x41_abs_of_code {s₀ s₉ : State}  {fuel : Nat} :
  execCall fuel panic_error_0x41 [] (s₀, []) = s₉ →
  Spec (A_panic_error_0x41  ) s₀ s₉
:= λ h ↦ panic_error_0x41_abs_of_concrete (panic_error_0x41_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
