import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_8836250053273208363
import Generated.ERC20simple.ERC20Shim.abi_encode_tuple_address
import Generated.ERC20simple.ERC20Shim.Common.if_3919842492790420297
import Generated.ERC20simple.ERC20Shim.fun_update

import Generated.ERC20simple.ERC20Shim.fun__transfer_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def A_fun__transfer  (var_from var_to var_value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun__transfer_abs_of_concrete {s₀ s₉ : State} { var_from var_to var_value} :
  Spec (fun__transfer_concrete_of_code.1  var_from var_to var_value) s₀ s₉ →
  Spec (A_fun__transfer  var_from var_to var_value) s₀ s₉ := by
  unfold fun__transfer_concrete_of_code A_fun__transfer
  sorry

end

end Generated.ERC20simple.ERC20Shim
