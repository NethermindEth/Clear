import Clear.ReasoningPrinciple


import Generated.ERC20simple.ERC20Shim.Common.if_5295847412656974480_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_5295847412656974480 (s₀ s₉ : State) : Prop :=
  (if s₀["expr_2"]!! = 0
   then s₀
   else 🚪s₀⟦"expr_3"↦0⟧⟦"expr_201_component"↦0⟧⟦"_3"↦s₀["var_from"]!!⟧⟦"expr_4"↦s₀["var_from"]!!⟧⟦"expr_201_component_1"↦s₀["var_from"]!!⟧⟦"_4"↦s₀["var_to"]!!⟧⟦"expr_5"↦s₀["var_to"]!!⟧⟦"expr_component"↦s₀["var_to"]!!⟧⟦"var"↦0⟧⟦"var_1"↦s₀["var_from"]!!⟧⟦"var_2"↦s₀["var_to"]!!⟧) =
  s₉

lemma if_5295847412656974480_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5295847412656974480_concrete_of_code s₀ s₉ →
  Spec A_if_5295847412656974480 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
