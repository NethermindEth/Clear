import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.array_storeLengthForEncoding_string_fromStack
import Generated.ERC20simple.ERC20Shim.copy_memory_to_memory_with_cleanup

import Generated.ERC20simple.ERC20Shim.abi_encode_string_memory_ptr_gen

import Generated.ERC20simple.ERC20Shim.abi_encode_string_memory_ptr_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma abi_encode_string_memory_ptr_abs_of_code {s₀ s₉ : State} {end_clear_sanitised_hrafn value pos} {fuel : Nat} :
  execCall fuel abi_encode_string_memory_ptr [end_clear_sanitised_hrafn] (s₀, [value, pos]) = s₉ →
  Spec (A_abi_encode_string_memory_ptr end_clear_sanitised_hrafn value pos) s₀ s₉
:= λ h ↦ abi_encode_string_memory_ptr_abs_of_concrete (abi_encode_string_memory_ptr_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
