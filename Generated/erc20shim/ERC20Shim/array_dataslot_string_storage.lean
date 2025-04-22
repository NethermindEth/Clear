import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.array_dataslot_string_storage_gen

import Generated.erc20shim.ERC20Shim.array_dataslot_string_storage_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma array_dataslot_string_storage_abs_of_code {s₀ s₉ : State} {data ptr} {fuel : Nat} :
  execCall fuel array_dataslot_string_storage [data] (s₀, [ptr]) = s₉ →
  Spec (A_array_dataslot_string_storage data ptr) s₀ s₉
:= λ h ↦ array_dataslot_string_storage_abs_of_concrete (array_dataslot_string_storage_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
