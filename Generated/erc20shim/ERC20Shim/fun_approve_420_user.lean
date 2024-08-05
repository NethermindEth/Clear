import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun__approve

import Generated.erc20shim.ERC20Shim.fun_approve_420_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_fun_approve_420  (var_owner var_spender var_value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_approve_420_abs_of_concrete {s₀ s₉ : State} { var_owner var_spender var_value} :
  Spec (fun_approve_420_concrete_of_code.1  var_owner var_spender var_value) s₀ s₉ →
  Spec (A_fun_approve_420  var_owner var_spender var_value) s₀ s₉ := by
  unfold fun_approve_420_concrete_of_code A_fun_approve_420
  sorry

end

end Generated.erc20shim.ERC20Shim
