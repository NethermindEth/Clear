import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_9141570808380448040
import Generated.erc20shim.ERC20Shim.abi_encode_tuple_address
import Generated.erc20shim.ERC20Shim.Common.if_2395397427938978657
import Generated.erc20shim.ERC20Shim.fun_update

import Generated.erc20shim.ERC20Shim.fun__transfer_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def A_fun__transfer  (var_from var_to var_value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun__transfer_abs_of_concrete {s₀ s₉ : State} { var_from var_to var_value} :
  Spec (fun__transfer_concrete_of_code.1  var_from var_to var_value) s₀ s₉ →
  Spec (A_fun__transfer  var_from var_to var_value) s₀ s₉ := by
  unfold fun__transfer_concrete_of_code A_fun__transfer
  sorry

end

end Generated.erc20shim.ERC20Shim
