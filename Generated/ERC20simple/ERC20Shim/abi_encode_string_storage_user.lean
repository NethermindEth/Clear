import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.extract_byte_array_length
import Generated.ERC20simple.ERC20Shim.array_storeLengthForEncoding_string
import Generated.ERC20simple.ERC20Shim.Common.switch_8164987986085659348
import Generated.ERC20simple.ERC20Shim.array_dataslot_string_storage

import Generated.ERC20simple.ERC20Shim.abi_encode_string_storage_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def A_abi_encode_string_storage (ret : Identifier) (value pos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_string_storage_abs_of_concrete {s₀ s₉ : State} {ret value pos} :
  Spec (abi_encode_string_storage_concrete_of_code.1 ret value pos) s₀ s₉ →
  Spec (A_abi_encode_string_storage ret value pos) s₀ s₉ := by
  unfold abi_encode_string_storage_concrete_of_code A_abi_encode_string_storage
  sorry

end

end Generated.ERC20simple.ERC20Shim
