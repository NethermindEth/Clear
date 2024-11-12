import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b

import Generated.ERC20simple.ERC20Shim.Common.if_7164014626810332831_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_if_7164014626810332831 (s₀ s₉ : State) : Prop := sorry

lemma if_7164014626810332831_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7164014626810332831_concrete_of_code s₀ s₉ →
  Spec A_if_7164014626810332831 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
