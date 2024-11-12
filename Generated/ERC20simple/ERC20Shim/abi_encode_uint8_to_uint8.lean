import Clear.ReasoningPrinciple


import Generated.ERC20simple.ERC20Shim.abi_encode_uint8_to_uint8_gen

import Generated.ERC20simple.ERC20Shim.abi_encode_uint8_to_uint8_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma abi_encode_uint8_to_uint8_abs_of_code {s₀ s₉ : State} { value pos} {fuel : Nat} :
  execCall fuel abi_encode_uint8_to_uint8 [] (s₀, [value, pos]) = s₉ →
  Spec (A_abi_encode_uint8_to_uint8  value pos) s₀ s₉
:= λ h ↦ abi_encode_uint8_to_uint8_abs_of_concrete (abi_encode_uint8_to_uint8_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
