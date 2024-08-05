import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.fun_totalSupply_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_fun_totalSupply (var_ : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma fun_totalSupply_abs_of_concrete {s₀ s₉ : State} {var_ } :
  Spec (fun_totalSupply_concrete_of_code.1 var_ ) s₀ s₉ →
  Spec (A_fun_totalSupply var_ ) s₀ s₉ := by
  unfold fun_totalSupply_concrete_of_code A_fun_totalSupply
  sorry

end

end Generated.erc20shim.ERC20Shim
