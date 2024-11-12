import Clear.ReasoningPrinciple


import Generated.ERC20simple.ERC20Shim.fun_decimals_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_fun_decimals (var : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma fun_decimals_abs_of_concrete {s₀ s₉ : State} {var } :
  Spec (fun_decimals_concrete_of_code.1 var ) s₀ s₉ →
  Spec (A_fun_decimals var ) s₀ s₉ := by
  unfold fun_decimals_concrete_of_code A_fun_decimals
  sorry

end

end Generated.ERC20simple.ERC20Shim
