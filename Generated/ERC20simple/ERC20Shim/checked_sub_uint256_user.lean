import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_2792370840247009933
import Generated.ERC20simple.ERC20Shim.panic_error_0x11

import Generated.ERC20simple.ERC20Shim.checked_sub_uint256_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def A_checked_sub_uint256 (diff : Identifier) (x y : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = let computedDiff := x - y
       if x < computedDiff
       then s₀.diverge
       else s₀⟦diff ↦ computedDiff⟧

lemma checked_sub_uint256_abs_of_concrete {s₀ s₉ : State} {diff x y} :
  Spec (checked_sub_uint256_concrete_of_code.1 diff x y) s₀ s₉ →
  Spec (A_checked_sub_uint256 diff x y) s₀ s₉ := by
  unfold checked_sub_uint256_concrete_of_code A_checked_sub_uint256
  sorry

end

end Generated.ERC20simple.ERC20Shim
