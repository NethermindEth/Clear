import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_tuple_address

import Generated.ERC20simple.ERC20Shim.Common.if_3919842492790420297_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_if_3919842492790420297 (s₀ s₉ : State) : Prop := sorry

lemma if_3919842492790420297_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3919842492790420297_concrete_of_code s₀ s₉ →
  Spec A_if_3919842492790420297 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
