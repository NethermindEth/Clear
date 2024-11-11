import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.panic_error_0x22

import Generated.erc20shim.ERC20Shim.Common.if_384845947645085899_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_if_384845947645085899 (s₀ s₉ : State) : Prop := sorry

lemma if_384845947645085899_abs_of_concrete {s₀ s₉ : State} :
  Spec if_384845947645085899_concrete_of_code s₀ s₉ →
  Spec A_if_384845947645085899 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common