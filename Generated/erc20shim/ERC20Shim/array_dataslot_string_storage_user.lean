import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.array_dataslot_string_storage_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_array_dataslot_string_storage (data : Identifier) (ptr : Literal) (s₀ s₉ : State) : Prop := sorry

lemma array_dataslot_string_storage_abs_of_concrete {s₀ s₉ : State} {data ptr} :
  Spec (array_dataslot_string_storage_concrete_of_code.1 data ptr) s₀ s₉ →
  Spec (A_array_dataslot_string_storage data ptr) s₀ s₉ := by
  unfold array_dataslot_string_storage_concrete_of_code A_array_dataslot_string_storage
  sorry

end

end Generated.erc20shim.ERC20Shim
