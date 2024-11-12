import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.array_storeLengthForEncoding_string_fromStack
import Generated.ERC20simple.ERC20Shim.copy_memory_to_memory_with_cleanup

import Generated.ERC20simple.ERC20Shim.abi_encode_string_memory_ptr_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_abi_encode_string_memory_ptr (end_clear_sanitised_hrafn : Identifier) (value pos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_string_memory_ptr_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn value pos} :
  Spec (abi_encode_string_memory_ptr_concrete_of_code.1 end_clear_sanitised_hrafn value pos) s₀ s₉ →
  Spec (A_abi_encode_string_memory_ptr end_clear_sanitised_hrafn value pos) s₀ s₉ := by
  unfold abi_encode_string_memory_ptr_concrete_of_code A_abi_encode_string_memory_ptr
  sorry

end

end Generated.ERC20simple.ERC20Shim
