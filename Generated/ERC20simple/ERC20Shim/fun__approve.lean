import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.fun_approve_532

import Generated.ERC20simple.ERC20Shim.fun__approve_gen

import Generated.ERC20simple.ERC20Shim.fun__approve_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma fun__approve_abs_of_code {s₀ s₉ : State} { var_owner var_spender var_value} {fuel : Nat} :
  execCall fuel fun__approve [] (s₀, [var_owner, var_spender, var_value]) = s₉ →
  Spec (A_fun__approve  var_owner var_spender var_value) s₀ s₉
:= λ h ↦ fun__approve_abs_of_concrete (fun__approve_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
