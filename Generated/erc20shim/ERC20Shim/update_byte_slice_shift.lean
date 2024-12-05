import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.update_byte_slice_shift_gen

import Generated.erc20shim.ERC20Shim.update_byte_slice_shift_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma update_byte_slice_shift_abs_of_code {s₀ s₉ : State} {result value toInsert} {fuel : Nat} :
  execCall fuel update_byte_slice_shift [result] (s₀, [value, toInsert]) = s₉ →
  Spec (A_update_byte_slice_shift result value toInsert) s₀ s₉
:= λ h ↦ update_byte_slice_shift_abs_of_concrete (update_byte_slice_shift_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
