import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_1438067688173587229

import Generated.erc20shim.ERC20Shim.validator_revert_uint256_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common 

def A_validator_revert_uint256  (value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma validator_revert_uint256_abs_of_concrete {s₀ s₉ : State} { value} :
  Spec (validator_revert_uint256_concrete_of_code.1  value) s₀ s₉ →
  Spec (A_validator_revert_uint256  value) s₀ s₉ := by
  unfold validator_revert_uint256_concrete_of_code A_validator_revert_uint256
  sorry

end

end Generated.erc20shim.ERC20Shim
