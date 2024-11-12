import Clear.ReasoningPrinciple


import Generated.peano.Peano.Common.if_6183625948864629624_gen


namespace Peano.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_6183625948864629624 (s₀ s₉ : State) : Prop := sorry

lemma if_6183625948864629624_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6183625948864629624_concrete_of_code s₀ s₉ →
  Spec A_if_6183625948864629624 s₀ s₉ := by
  sorry

end

end Peano.Common
