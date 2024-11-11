import Clear.ReasoningPrinciple


import Generated.ERC20.GetCode.Common.if_8423444027764651193_gen


namespace GetCode.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_8423444027764651193 (s₀ s₉ : State) : Prop := sorry

lemma if_8423444027764651193_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8423444027764651193_concrete_of_code s₀ s₉ →
  Spec A_if_8423444027764651193 s₀ s₉ := by
  sorry

end

end GetCode.Common
