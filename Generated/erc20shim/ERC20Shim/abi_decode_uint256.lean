import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.validator_revert_uint256

import Generated.erc20shim.ERC20Shim.abi_decode_uint256_gen

import Generated.erc20shim.ERC20Shim.abi_decode_uint256_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

lemma abi_decode_uint256_abs_of_code {s₀ s₉ : State} {value offset end_clear_sanitised_hrafn} {fuel : Nat} :
  execCall fuel abi_decode_uint256 [value] (s₀, [offset, end_clear_sanitised_hrafn]) = s₉ →
  Spec (A_abi_decode_uint256 value offset end_clear_sanitised_hrafn) s₀ s₉
:= λ h ↦ abi_decode_uint256_abs_of_concrete (abi_decode_uint256_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
