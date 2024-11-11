import Clear.ReasoningPrinciple

import Generated.ERC20.GetCode.Common.if_8423444027764651193

import Generated.ERC20.GetCode.fun_transfer_gen


namespace Generated.ERC20.GetCode

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities GetCode.Common 

def A_fun_transfer (var_acc1out var_acc2out : Identifier) (var_ammount var_acc1 var_acc2 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_transfer_abs_of_concrete {s₀ s₉ : State} {var_acc1out var_acc2out var_ammount var_acc1 var_acc2} :
  Spec (fun_transfer_concrete_of_code.1 var_acc1out var_acc2out var_ammount var_acc1 var_acc2) s₀ s₉ →
  Spec (A_fun_transfer var_acc1out var_acc2out var_ammount var_acc1 var_acc2) s₀ s₉ := by
  unfold fun_transfer_concrete_of_code A_fun_transfer
  sorry

end

end Generated.ERC20.GetCode
