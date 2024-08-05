import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.extract_byte_array_length
import Generated.erc20shim.ERC20Shim.array_storeLengthForEncoding_string
import Generated.erc20shim.ERC20Shim.Common.switch_8164987986085659348
import Generated.erc20shim.ERC20Shim.array_dataslot_string_storage

import Generated.erc20shim.ERC20Shim.abi_encode_string_storage_gen

import Generated.erc20shim.ERC20Shim.abi_encode_string_storage_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

lemma abi_encode_string_storage_abs_of_code {s₀ s₉ : State} {ret value pos} {fuel : Nat} :
  execCall fuel abi_encode_string_storage [ret] (s₀, [value, pos]) = s₉ →
  Spec (A_abi_encode_string_storage ret value pos) s₀ s₉
:= λ h ↦ abi_encode_string_storage_abs_of_concrete (abi_encode_string_storage_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
