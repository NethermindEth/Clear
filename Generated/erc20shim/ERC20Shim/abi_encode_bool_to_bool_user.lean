import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.abi_encode_bool_to_bool_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_bool_to_bool  (value pos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_bool_to_bool_abs_of_concrete {s₀ s₉ : State} { value pos} :
  Spec (abi_encode_bool_to_bool_concrete_of_code.1  value pos) s₀ s₉ →
  Spec (A_abi_encode_bool_to_bool  value pos) s₀ s₉ := by
  unfold abi_encode_bool_to_bool_concrete_of_code A_abi_encode_bool_to_bool
  sorry

end

end Generated.erc20shim.ERC20Shim
