import Clear.ReasoningPrinciple


import Generated.ERC20simple.ERC20Shim.panic_error_0x41_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_panic_error_0x41   (s₀ s₉ : State) : Prop := sorry

lemma panic_error_0x41_abs_of_concrete {s₀ s₉ : State}  :
  Spec (panic_error_0x41_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_panic_error_0x41  ) s₀ s₉ := by
  unfold panic_error_0x41_concrete_of_code A_panic_error_0x41
  sorry

end

end Generated.ERC20simple.ERC20Shim
