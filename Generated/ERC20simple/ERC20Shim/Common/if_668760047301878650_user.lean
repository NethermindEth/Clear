import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.checked_sub_uint256
import Generated.ERC20simple.ERC20Shim.checked_add_uint256

import Generated.ERC20simple.ERC20Shim.Common.if_668760047301878650_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

def A_if_668760047301878650 (s₀ s₉ : State) : Prop := sorry
  -- s₉ = if s₀["expr_2"]!! = 0
  --      then s₀
  --      else s₀⟦"var_newFrom"↦1⟧)

lemma if_668760047301878650_abs_of_concrete {s₀ s₉ : State} :
  Spec if_668760047301878650_concrete_of_code s₀ s₉ →
  Spec A_if_668760047301878650 s₀ s₉ := by
  sorry

end

end ERC20Shim.Common
