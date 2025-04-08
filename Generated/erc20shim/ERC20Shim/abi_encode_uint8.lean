import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_uint8_to_uint8

import Generated.erc20shim.ERC20Shim.abi_encode_uint8_gen

import Generated.erc20shim.ERC20Shim.abi_encode_uint8_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

lemma abi_encode_uint8_abs_of_code {s₀ s₉ : State} {tail headStart value0} {fuel : Nat} :
  execCall fuel abi_encode_uint8 [tail] (s₀, [headStart, value0]) = s₉ →
  Spec (A_abi_encode_uint8 tail headStart value0) s₀ s₉
:= λ h ↦ abi_encode_uint8_abs_of_concrete (abi_encode_uint8_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
