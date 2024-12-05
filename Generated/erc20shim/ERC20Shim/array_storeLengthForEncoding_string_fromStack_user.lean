import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.array_storeLengthForEncoding_string_fromStack_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_array_storeLengthForEncoding_string_fromStack (updated_pos : Identifier) (pos length : Literal) (s₀ s₉ : State) : Prop := sorry

lemma array_storeLengthForEncoding_string_fromStack_abs_of_concrete {s₀ s₉ : State} {updated_pos pos length} :
  Spec (array_storeLengthForEncoding_string_fromStack_concrete_of_code.1 updated_pos pos length) s₀ s₉ →
  Spec (A_array_storeLengthForEncoding_string_fromStack updated_pos pos length) s₀ s₉ := by
  unfold array_storeLengthForEncoding_string_fromStack_concrete_of_code A_array_storeLengthForEncoding_string_fromStack
  sorry

end

end Generated.erc20shim.ERC20Shim
