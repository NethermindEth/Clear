import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.fun_msgSender
import Generated.ERC20simple.ERC20Shim.fun__transfer

import Generated.ERC20simple.ERC20Shim.fun_transfer_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_fun_transfer (var : Identifier) (var_to var_value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_transfer_abs_of_concrete {s₀ s₉ : State} {var var_to var_value} :
  Spec (fun_transfer_concrete_of_code.1 var var_to var_value) s₀ s₉ →
  Spec (A_fun_transfer var var_to var_value) s₀ s₉ := by
  unfold fun_transfer_concrete_of_code A_fun_transfer
  sorry

end

end Generated.ERC20simple.ERC20Shim
