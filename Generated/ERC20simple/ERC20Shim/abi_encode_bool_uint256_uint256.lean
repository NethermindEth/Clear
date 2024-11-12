import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_bool_to_bool
import Generated.ERC20simple.ERC20Shim.abi_encode_uint256_to_uint256

import Generated.ERC20simple.ERC20Shim.abi_encode_bool_uint256_uint256_gen

import Generated.ERC20simple.ERC20Shim.abi_encode_bool_uint256_uint256_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma abi_encode_bool_uint256_uint256_abs_of_code {s₀ s₉ : State} {tail headStart value0 value1 value2} {fuel : Nat} :
  execCall fuel abi_encode_bool_uint256_uint256 [tail] (s₀, [headStart, value0, value1, value2]) = s₉ →
  Spec (A_abi_encode_bool_uint256_uint256 tail headStart value0 value1 value2) s₀ s₉
:= λ h ↦ abi_encode_bool_uint256_uint256_abs_of_concrete (abi_encode_bool_uint256_uint256_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
