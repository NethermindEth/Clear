import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.copy_array_from_storage_to_memory_string

import Generated.erc20shim.ERC20Shim.fun_symbol_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_fun_symbol (var_mpos : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma fun_symbol_abs_of_concrete {s₀ s₉ : State} {var_mpos } :
  Spec (fun_symbol_concrete_of_code.1 var_mpos ) s₀ s₉ →
  Spec (A_fun_symbol var_mpos ) s₀ s₉ := by
  unfold fun_symbol_concrete_of_code A_fun_symbol
  sorry

end

end Generated.erc20shim.ERC20Shim
