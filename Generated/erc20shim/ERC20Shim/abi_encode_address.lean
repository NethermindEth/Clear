import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.abi_encode_address_gen

import Generated.erc20shim.ERC20Shim.abi_encode_address_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma abi_encode_address_abs_of_code {s₀ s₉ : State} { value pos} {fuel : Nat} :
  execCall fuel abi_encode_address [] (s₀, [value, pos]) = s₉ →
  Spec (A_abi_encode_address  value pos) s₀ s₉
:= λ h ↦ abi_encode_address_abs_of_concrete (abi_encode_address_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
