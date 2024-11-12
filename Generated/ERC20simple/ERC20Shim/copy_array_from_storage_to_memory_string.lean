import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_string_storage
import Generated.ERC20simple.ERC20Shim.finalize_allocation

import Generated.ERC20simple.ERC20Shim.copy_array_from_storage_to_memory_string_gen

import Generated.ERC20simple.ERC20Shim.copy_array_from_storage_to_memory_string_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma copy_array_from_storage_to_memory_string_abs_of_code {s₀ s₉ : State} {memPtr slot} {fuel : Nat} :
  execCall fuel copy_array_from_storage_to_memory_string [memPtr] (s₀, [slot]) = s₉ →
  Spec (A_copy_array_from_storage_to_memory_string memPtr slot) s₀ s₉
:= λ h ↦ copy_array_from_storage_to_memory_string_abs_of_concrete (copy_array_from_storage_to_memory_string_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
