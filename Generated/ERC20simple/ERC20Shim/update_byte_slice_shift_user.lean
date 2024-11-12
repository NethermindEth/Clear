import Clear.ReasoningPrinciple


import Generated.ERC20simple.ERC20Shim.update_byte_slice_shift_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_update_byte_slice_shift (result : Identifier) (value toInsert : Literal) (s₀ s₉ : State) : Prop := sorry

lemma update_byte_slice_shift_abs_of_concrete {s₀ s₉ : State} {result value toInsert} :
  Spec (update_byte_slice_shift_concrete_of_code.1 result value toInsert) s₀ s₉ →
  Spec (A_update_byte_slice_shift result value toInsert) s₀ s₉ := by
  unfold update_byte_slice_shift_concrete_of_code A_update_byte_slice_shift
  sorry

end

end Generated.ERC20simple.ERC20Shim
