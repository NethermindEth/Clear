import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_7164014626810332831
import Generated.erc20shim.ERC20Shim.revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b

import Generated.erc20shim.ERC20Shim.abi_decode_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def A_abi_decode  (headStart dataEnd : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_abs_of_concrete {s₀ s₉ : State} { headStart dataEnd} :
  Spec (abi_decode_concrete_of_code.1  headStart dataEnd) s₀ s₉ →
  Spec (A_abi_decode  headStart dataEnd) s₀ s₉ := by
  unfold abi_decode_concrete_of_code A_abi_decode
  sorry

end

end Generated.erc20shim.ERC20Shim
