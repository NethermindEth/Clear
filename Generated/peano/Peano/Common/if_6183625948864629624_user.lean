import Clear.ReasoningPrinciple


import Generated.peano.Peano.Common.if_6183625948864629624_gen


namespace Peano.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

def A_if_6183625948864629624 (s₀ s₉ : State) : Prop := s₉ = if s₀["k"]! = 0 then 💔 s₀ else s₀

lemma if_6183625948864629624_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6183625948864629624_concrete_of_code s₀ s₉ →
  Spec A_if_6183625948864629624 s₀ s₉ := by
  unfold if_6183625948864629624_concrete_of_code A_if_6183625948864629624
  aesop_spec

end

end Peano.Common
