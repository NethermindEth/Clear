import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_7164014626810332831
import Generated.ERC20simple.ERC20Shim.revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b
import Generated.ERC20simple.ERC20Shim.abi_decode_address
import Generated.ERC20simple.ERC20Shim.abi_decode_uint256

import Generated.ERC20simple.ERC20Shim.abi_decode_addresst_uint256_gen

import Generated.ERC20simple.ERC20Shim.abi_decode_addresst_uint256_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

lemma abi_decode_addresst_uint256_abs_of_code {s₀ s₉ : State} {value0 value1 headStart dataEnd} {fuel : Nat} :
  execCall fuel abi_decode_addresst_uint256 [value0, value1] (s₀, [headStart, dataEnd]) = s₉ →
  Spec (A_abi_decode_addresst_uint256 value0 value1 headStart dataEnd) s₀ s₉
:= λ h ↦ abi_decode_addresst_uint256_abs_of_concrete (abi_decode_addresst_uint256_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
