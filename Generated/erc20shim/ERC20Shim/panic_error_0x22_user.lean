import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.panic_error_0x22_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_panic_error_0x22   (s₀ s₉ : State) : Prop := sorry

lemma panic_error_0x22_abs_of_concrete {s₀ s₉ : State}  } :
  Spec (panic_error_0x22_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_panic_error_0x22  ) s₀ s₉ := by
  unfold panic_error_0x22_concrete_of_code A_panic_error_0x22
  sorry

end

end Generated.erc20shim.ERC20Shim
