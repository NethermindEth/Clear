import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_4024499920364541172
import Generated.erc20shim.ERC20Shim.Common.if_384845947645085899
import Generated.erc20shim.ERC20Shim.panic_error_0x22

import Generated.erc20shim.ERC20Shim.extract_byte_array_length_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def A_extract_byte_array_length (length : Identifier) (data : Literal) (s₀ s₉ : State) : Prop := sorry

lemma extract_byte_array_length_abs_of_concrete {s₀ s₉ : State} {length data} :
  Spec (extract_byte_array_length_concrete_of_code.1 length data) s₀ s₉ →
  Spec (A_extract_byte_array_length length data) s₀ s₉ := by
  unfold extract_byte_array_length_concrete_of_code A_extract_byte_array_length
  sorry

end

end Generated.erc20shim.ERC20Shim
