import Clear.ReasoningPrinciple


import Generated.ERC20simple.ERC20Shim.Common.if_5295847412656974480_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5295847412656974480 (s₀ s₉ : State) : Prop := sorry

lemma if_5295847412656974480_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5295847412656974480_concrete_of_code s₀ s₉ →
  Spec A_if_5295847412656974480 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
