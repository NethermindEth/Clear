import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_string_storage
import Generated.ERC20simple.ERC20Shim.finalize_allocation

import Generated.ERC20simple.ERC20Shim.copy_array_from_storage_to_memory_string_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_copy_array_from_storage_to_memory_string (memPtr : Identifier) (slot : Literal) (s₀ s₉ : State) : Prop := sorry

lemma copy_array_from_storage_to_memory_string_abs_of_concrete {s₀ s₉ : State} {memPtr slot} :
  Spec (copy_array_from_storage_to_memory_string_concrete_of_code.1 memPtr slot) s₀ s₉ →
  Spec (A_copy_array_from_storage_to_memory_string memPtr slot) s₀ s₉ := by
  unfold copy_array_from_storage_to_memory_string_concrete_of_code A_copy_array_from_storage_to_memory_string
  sorry

end

end Generated.ERC20simple.ERC20Shim
