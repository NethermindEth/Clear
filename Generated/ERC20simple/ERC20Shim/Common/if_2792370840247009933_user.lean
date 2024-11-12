import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.panic_error_0x11

import Generated.ERC20simple.ERC20Shim.Common.if_2792370840247009933_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_if_2792370840247009933 (s₀ s₉ : State) : Prop := sorry

lemma if_2792370840247009933_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2792370840247009933_concrete_of_code s₀ s₉ →
  Spec A_if_2792370840247009933 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
