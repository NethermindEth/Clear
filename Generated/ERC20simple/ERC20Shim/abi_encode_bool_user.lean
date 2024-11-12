import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.abi_encode_bool_to_bool

import Generated.ERC20simple.ERC20Shim.abi_encode_bool_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_abi_encode_bool (tail : Identifier) (headStart value0 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_bool_abs_of_concrete {s₀ s₉ : State} {tail headStart value0} :
  Spec (abi_encode_bool_concrete_of_code.1 tail headStart value0) s₀ s₉ →
  Spec (A_abi_encode_bool tail headStart value0) s₀ s₉ := by
  unfold abi_encode_bool_concrete_of_code A_abi_encode_bool
  sorry

end

end Generated.ERC20simple.ERC20Shim
