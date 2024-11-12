import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_9222169807163418225
import Generated.ERC20simple.ERC20Shim.panic_error_0x41

import Generated.ERC20simple.ERC20Shim.finalize_allocation_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def A_finalize_allocation  (memPtr size : Literal) (s₀ s₉ : State) : Prop := sorry

lemma finalize_allocation_abs_of_concrete {s₀ s₉ : State} { memPtr size} :
  Spec (finalize_allocation_concrete_of_code.1  memPtr size) s₀ s₉ →
  Spec (A_finalize_allocation  memPtr size) s₀ s₉ := by
  unfold finalize_allocation_concrete_of_code A_finalize_allocation
  sorry

end

end Generated.ERC20simple.ERC20Shim
