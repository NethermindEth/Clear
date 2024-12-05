import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.for_6088573059593786335

import Generated.erc20shim.ERC20Shim.copy_memory_to_memory_with_cleanup_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common 

def A_copy_memory_to_memory_with_cleanup  (src dst length : Literal) (s₀ s₉ : State) : Prop := sorry

lemma copy_memory_to_memory_with_cleanup_abs_of_concrete {s₀ s₉ : State} { src dst length} :
  Spec (copy_memory_to_memory_with_cleanup_concrete_of_code.1  src dst length) s₀ s₉ →
  Spec (A_copy_memory_to_memory_with_cleanup  src dst length) s₀ s₉ := by
  unfold copy_memory_to_memory_with_cleanup_concrete_of_code A_copy_memory_to_memory_with_cleanup
  sorry

end

end Generated.erc20shim.ERC20Shim
