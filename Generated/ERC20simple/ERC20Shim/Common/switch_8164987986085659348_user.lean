import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.array_dataslot_string_storage
import Generated.ERC20simple.ERC20Shim.Common.for_1821242857744567453

import Generated.ERC20simple.ERC20Shim.Common.switch_8164987986085659348_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def A_switch_8164987986085659348 (s₀ s₉ : State) : Prop := sorry

lemma switch_8164987986085659348_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8164987986085659348_concrete_of_code s₀ s₉ →
  Spec A_switch_8164987986085659348 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
