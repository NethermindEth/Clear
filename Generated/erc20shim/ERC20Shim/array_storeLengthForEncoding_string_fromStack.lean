import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.array_storeLengthForEncoding_string_fromStack_gen

import Generated.erc20shim.ERC20Shim.array_storeLengthForEncoding_string_fromStack_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma array_storeLengthForEncoding_string_fromStack_abs_of_code {s₀ s₉ : State} {updated_pos pos length} {fuel : Nat} :
  execCall fuel array_storeLengthForEncoding_string_fromStack [updated_pos] (s₀, [pos, length]) = s₉ →
  Spec (A_array_storeLengthForEncoding_string_fromStack updated_pos pos length) s₀ s₉
:= λ h ↦ array_storeLengthForEncoding_string_fromStack_abs_of_concrete (array_storeLengthForEncoding_string_fromStack_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
