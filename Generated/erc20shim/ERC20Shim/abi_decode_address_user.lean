import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.validator_revert_address

import Generated.erc20shim.ERC20Shim.abi_decode_address_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_abi_decode_address (value : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_address_abs_of_concrete {s₀ s₉ : State} {value offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_address_concrete_of_code.1 value offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_address value offset end_clear_sanitised_hrafn) s₀ s₉ := by
  unfold abi_decode_address_concrete_of_code A_abi_decode_address
  sorry

end

end Generated.erc20shim.ERC20Shim
