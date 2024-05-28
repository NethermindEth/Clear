import Clear.ReasoningPrinciple


import Generated.peano.Peano.Common.if_6183625948864629624_gen

import Generated.peano.Peano.Common.if_6183625948864629624_user


namespace Peano.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma if_6183625948864629624_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_6183625948864629624 s₀ = s₉ →
        Spec A_if_6183625948864629624 s₀ s₉ :=
  λ _ h ↦ if_6183625948864629624_abs_of_concrete (if_6183625948864629624_concrete_of_code.2 h)

end

end Peano.Common
