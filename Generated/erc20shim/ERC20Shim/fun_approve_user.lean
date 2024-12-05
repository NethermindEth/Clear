import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun_msgSender
import Generated.erc20shim.ERC20Shim.fun_approve_426

import Generated.erc20shim.ERC20Shim.fun_approve_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_fun_approve (var : Identifier) (var_spender var_value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_approve_abs_of_concrete {s₀ s₉ : State} {var var_spender var_value} :
  Spec (fun_approve_concrete_of_code.1 var var_spender var_value) s₀ s₉ →
  Spec (A_fun_approve var var_spender var_value) s₀ s₉ := by
  unfold fun_approve_concrete_of_code A_fun_approve
  sorry

end

end Generated.erc20shim.ERC20Shim