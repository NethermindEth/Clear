import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.panic_error_0x11_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_panic_error_0x11   (s₀ s₉ : State) : Prop := sorry

lemma panic_error_0x11_abs_of_concrete {s₀ s₉ : State}  } :
  Spec (panic_error_0x11_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_panic_error_0x11  ) s₀ s₉ := by
  unfold panic_error_0x11_concrete_of_code A_panic_error_0x11
  sorry

end

end Generated.erc20shim.ERC20Shim
