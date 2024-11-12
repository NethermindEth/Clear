import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.ERC20simple.ERC20Shim.update_storage_value_offsett_uint256_to_uint256

import Generated.ERC20simple.ERC20Shim.Common.switch_108332838879531311_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_switch_108332838879531311 (s₀ s₉ : State) : Prop := sorry

lemma switch_108332838879531311_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_108332838879531311_concrete_of_code s₀ s₉ →
  Spec A_switch_108332838879531311 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
