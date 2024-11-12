import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.validator_revert_address

import Generated.ERC20simple.ERC20Shim.abi_decode_address_gen

import Generated.ERC20simple.ERC20Shim.abi_decode_address_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma abi_decode_address_abs_of_code {s₀ s₉ : State} {value offset end_clear_sanitised_hrafn} {fuel : Nat} :
  execCall fuel abi_decode_address [value] (s₀, [offset, end_clear_sanitised_hrafn]) = s₉ →
  Spec (A_abi_decode_address value offset end_clear_sanitised_hrafn) s₀ s₉
:= λ h ↦ abi_decode_address_abs_of_concrete (abi_decode_address_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
