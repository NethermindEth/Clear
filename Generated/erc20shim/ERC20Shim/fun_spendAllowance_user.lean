import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun_allowance
import Generated.erc20shim.ERC20Shim.Common.if_8475192588736690919
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.fun__approve

import Generated.erc20shim.ERC20Shim.fun_spendAllowance_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def A_fun_spendAllowance  (var_owner var_spender var_value : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_spendAllowance_abs_of_concrete {s₀ s₉ : State} { var_owner var_spender var_value} :
  Spec (fun_spendAllowance_concrete_of_code.1  var_owner var_spender var_value) s₀ s₉ →
  Spec (A_fun_spendAllowance  var_owner var_spender var_value) s₀ s₉ := by
  unfold fun_spendAllowance_concrete_of_code A_fun_spendAllowance
  sorry

end

end Generated.erc20shim.ERC20Shim
