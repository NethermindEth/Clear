import Clear.ReasoningPrinciple


import Generated.ERC20simple.ERC20Shim.panic_error_0x22_gen

import Generated.ERC20simple.ERC20Shim.panic_error_0x22_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma panic_error_0x22_abs_of_code {s₀ s₉ : State}  {fuel : Nat} :
  execCall fuel panic_error_0x22 [] (s₀, []) = s₉ →
  Spec (A_panic_error_0x22  ) s₀ s₉
:= λ h ↦ panic_error_0x22_abs_of_concrete (panic_error_0x22_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
