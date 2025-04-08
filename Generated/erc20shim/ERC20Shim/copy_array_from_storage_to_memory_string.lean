import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_string_storage
import Generated.erc20shim.ERC20Shim.finalize_allocation

import Generated.erc20shim.ERC20Shim.copy_array_from_storage_to_memory_string_gen

import Generated.erc20shim.ERC20Shim.copy_array_from_storage_to_memory_string_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

lemma copy_array_from_storage_to_memory_string_abs_of_code {s₀ s₉ : State} {memPtr slot} {fuel : Nat} :
  execCall fuel copy_array_from_storage_to_memory_string [memPtr] (s₀, [slot]) = s₉ →
  Spec (A_copy_array_from_storage_to_memory_string memPtr slot) s₀ s₉
:= λ h ↦ copy_array_from_storage_to_memory_string_abs_of_concrete (copy_array_from_storage_to_memory_string_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
