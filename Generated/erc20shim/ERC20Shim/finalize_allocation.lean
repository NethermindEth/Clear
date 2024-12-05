import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_9222169807163418225
import Generated.erc20shim.ERC20Shim.panic_error_0x41

import Generated.erc20shim.ERC20Shim.finalize_allocation_gen

import Generated.erc20shim.ERC20Shim.finalize_allocation_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

lemma finalize_allocation_abs_of_code {s₀ s₉ : State} { memPtr size} {fuel : Nat} :
  execCall fuel finalize_allocation [] (s₀, [memPtr, size]) = s₉ →
  Spec (A_finalize_allocation  memPtr size) s₀ s₉
:= λ h ↦ finalize_allocation_abs_of_concrete (finalize_allocation_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
