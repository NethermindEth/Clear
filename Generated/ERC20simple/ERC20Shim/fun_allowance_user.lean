import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_mapping_address_uint256_of_address
import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address

import Generated.ERC20simple.ERC20Shim.fun_allowance_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_fun_allowance (var : Identifier) (var_owner var_spender : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_allowance_abs_of_concrete {s₀ s₉ : State} {var var_owner var_spender} :
  Spec (fun_allowance_concrete_of_code.1 var var_owner var_spender) s₀ s₉ →
  Spec (A_fun_allowance var var_owner var_spender) s₀ s₉ := by
  unfold fun_allowance_concrete_of_code A_fun_allowance
  sorry

end

end Generated.ERC20simple.ERC20Shim
