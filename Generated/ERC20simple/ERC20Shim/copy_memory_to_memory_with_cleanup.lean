import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.for_6088573059593786335

import Generated.ERC20simple.ERC20Shim.copy_memory_to_memory_with_cleanup_gen

import Generated.ERC20simple.ERC20Shim.copy_memory_to_memory_with_cleanup_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common 

lemma copy_memory_to_memory_with_cleanup_abs_of_code {s₀ s₉ : State} { src dst length} {fuel : Nat} :
  execCall fuel copy_memory_to_memory_with_cleanup [] (s₀, [src, dst, length]) = s₉ →
  Spec (A_copy_memory_to_memory_with_cleanup  src dst length) s₀ s₉
:= λ h ↦ copy_memory_to_memory_with_cleanup_abs_of_concrete (copy_memory_to_memory_with_cleanup_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
