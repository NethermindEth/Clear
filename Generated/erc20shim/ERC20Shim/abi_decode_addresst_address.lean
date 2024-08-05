import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_7164014626810332831
import Generated.erc20shim.ERC20Shim.revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b
import Generated.erc20shim.ERC20Shim.abi_decode_address

import Generated.erc20shim.ERC20Shim.abi_decode_addresst_address_gen

import Generated.erc20shim.ERC20Shim.abi_decode_addresst_address_user


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

lemma abi_decode_addresst_address_abs_of_code {s₀ s₉ : State} {value0 value1 headStart dataEnd} {fuel : Nat} :
  execCall fuel abi_decode_addresst_address [value0, value1] (s₀, [headStart, dataEnd]) = s₉ →
  Spec (A_abi_decode_addresst_address value0 value1 headStart dataEnd) s₀ s₉
:= λ h ↦ abi_decode_addresst_address_abs_of_concrete (abi_decode_addresst_address_concrete_of_code.2 h)

end

end Generated.erc20shim.ERC20Shim
