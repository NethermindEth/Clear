import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_string_memory_ptr

import Generated.ERC20simple.ERC20Shim.abi_encode_string_gen

import Generated.ERC20simple.ERC20Shim.abi_encode_string_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma abi_encode_string_abs_of_code {s₀ s₉ : State} {tail headStart value0} {fuel : Nat} :
  execCall fuel abi_encode_string [tail] (s₀, [headStart, value0]) = s₉ →
  Spec (A_abi_encode_string tail headStart value0) s₀ s₉
:= λ h ↦ abi_encode_string_abs_of_concrete (abi_encode_string_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
