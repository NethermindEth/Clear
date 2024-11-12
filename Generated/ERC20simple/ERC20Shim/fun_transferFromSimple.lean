import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_668760047301878650
import Generated.ERC20simple.ERC20Shim.checked_sub_uint256
import Generated.ERC20simple.ERC20Shim.checked_add_uint256

import Generated.ERC20simple.ERC20Shim.fun_transferFromSimple_gen

import Generated.ERC20simple.ERC20Shim.fun_transferFromSimple_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

lemma fun_transferFromSimple_abs_of_code {s₀ s₉ : State} {var var_1 var_2 var_from var_to var_value} {fuel : Nat} :
  execCall fuel fun_transferFromSimple [var, var_1, var_2] (s₀, [var_from, var_to, var_value]) = s₉ →
  Spec (A_fun_transferFromSimple var var_1 var_2 var_from var_to var_value) s₀ s₉
:= λ h ↦ fun_transferFromSimple_abs_of_concrete (fun_transferFromSimple_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
