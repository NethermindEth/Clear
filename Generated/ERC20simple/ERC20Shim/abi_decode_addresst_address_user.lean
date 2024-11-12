import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_7164014626810332831
import Generated.ERC20simple.ERC20Shim.revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b
import Generated.ERC20simple.ERC20Shim.abi_decode_address

import Generated.ERC20simple.ERC20Shim.abi_decode_addresst_address_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def A_abi_decode_addresst_address (value0 value1 : Identifier) (headStart dataEnd : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_addresst_address_abs_of_concrete {s₀ s₉ : State} {value0 value1 headStart dataEnd} :
  Spec (abi_decode_addresst_address_concrete_of_code.1 value0 value1 headStart dataEnd) s₀ s₉ →
  Spec (A_abi_decode_addresst_address value0 value1 headStart dataEnd) s₀ s₉ := by
  unfold abi_decode_addresst_address_concrete_of_code A_abi_decode_addresst_address
  sorry

end

end Generated.ERC20simple.ERC20Shim
