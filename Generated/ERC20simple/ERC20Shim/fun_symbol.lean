import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.copy_array_from_storage_to_memory_string

import Generated.ERC20simple.ERC20Shim.fun_symbol_gen

import Generated.ERC20simple.ERC20Shim.fun_symbol_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma fun_symbol_abs_of_code {s₀ s₉ : State} {var_mpos } {fuel : Nat} :
  execCall fuel fun_symbol [var_mpos] (s₀, []) = s₉ →
  Spec (A_fun_symbol var_mpos ) s₀ s₉
:= λ h ↦ fun_symbol_abs_of_concrete (fun_symbol_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
