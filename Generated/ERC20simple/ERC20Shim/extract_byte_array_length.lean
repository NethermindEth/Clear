import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_4024499920364541172
import Generated.ERC20simple.ERC20Shim.Common.if_384845947645085899
import Generated.ERC20simple.ERC20Shim.panic_error_0x22

import Generated.ERC20simple.ERC20Shim.extract_byte_array_length_gen

import Generated.ERC20simple.ERC20Shim.extract_byte_array_length_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

lemma extract_byte_array_length_abs_of_code {s₀ s₉ : State} {length data} {fuel : Nat} :
  execCall fuel extract_byte_array_length [length] (s₀, [data]) = s₉ →
  Spec (A_extract_byte_array_length length data) s₀ s₉
:= λ h ↦ extract_byte_array_length_abs_of_concrete (extract_byte_array_length_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
