import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.fun_approve_532

import Generated.ERC20simple.ERC20Shim.fun__approve_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_fun__approve  (var_owner var_spender var_value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun__approve_abs_of_concrete {s₀ s₉ : State} { var_owner var_spender var_value} :
  Spec (fun__approve_concrete_of_code.1  var_owner var_spender var_value) s₀ s₉ →
  Spec (A_fun__approve  var_owner var_spender var_value) s₀ s₉ := by
  unfold fun__approve_concrete_of_code A_fun__approve
  sorry

end

end Generated.ERC20simple.ERC20Shim
