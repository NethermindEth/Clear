import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.validator_revert_uint256

import Generated.erc20shim.ERC20Shim.abi_decode_uint256_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_abi_decode_uint256 (value : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_uint256_abs_of_concrete {s₀ s₉ : State} {value offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_uint256_concrete_of_code.1 value offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_uint256 value offset end_clear_sanitised_hrafn) s₀ s₉ := by
  unfold abi_decode_uint256_concrete_of_code A_abi_decode_uint256
  sorry

end

end Generated.erc20shim.ERC20Shim
