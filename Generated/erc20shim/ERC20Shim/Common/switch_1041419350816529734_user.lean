import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.update_storage_value_offsett_uint256_to_uint256

import Generated.erc20shim.ERC20Shim.Common.switch_1041419350816529734_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_switch_1041419350816529734 (s₀ s₉ : State) : Prop := sorry

lemma switch_1041419350816529734_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_1041419350816529734_concrete_of_code s₀ s₉ →
  Spec A_switch_1041419350816529734 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
