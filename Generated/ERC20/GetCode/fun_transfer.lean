import Clear.ReasoningPrinciple

import Generated.ERC20.GetCode.Common.if_8423444027764651193

import Generated.ERC20.GetCode.fun_transfer_gen

import Generated.ERC20.GetCode.fun_transfer_user


namespace Generated.ERC20.GetCode

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities GetCode.Common 

lemma fun_transfer_abs_of_code {s₀ s₉ : State} {var_acc1out var_acc2out var_ammount var_acc1 var_acc2} {fuel : Nat} :
  execCall fuel fun_transfer [var_acc1out, var_acc2out] (s₀, [var_ammount, var_acc1, var_acc2]) = s₉ →
  Spec (A_fun_transfer var_acc1out var_acc2out var_ammount var_acc1 var_acc2) s₀ s₉
:= λ h ↦ fun_transfer_abs_of_concrete (fun_transfer_concrete_of_code.2 h)

end

end Generated.ERC20.GetCode
