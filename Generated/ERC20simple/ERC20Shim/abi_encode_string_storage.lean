import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.extract_byte_array_length
import Generated.ERC20simple.ERC20Shim.array_storeLengthForEncoding_string
import Generated.ERC20simple.ERC20Shim.Common.switch_8164987986085659348
import Generated.ERC20simple.ERC20Shim.array_dataslot_string_storage

import Generated.ERC20simple.ERC20Shim.abi_encode_string_storage_gen

import Generated.ERC20simple.ERC20Shim.abi_encode_string_storage_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

lemma abi_encode_string_storage_abs_of_code {s₀ s₉ : State} {ret value pos} {fuel : Nat} :
  execCall fuel abi_encode_string_storage [ret] (s₀, [value, pos]) = s₉ →
  Spec (A_abi_encode_string_storage ret value pos) s₀ s₉
:= λ h ↦ abi_encode_string_storage_abs_of_concrete (abi_encode_string_storage_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
