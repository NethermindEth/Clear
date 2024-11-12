import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_2792370840247009933
import Generated.ERC20simple.ERC20Shim.panic_error_0x11

import Generated.ERC20simple.ERC20Shim.checked_add_uint256_gen


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

def A_checked_add_uint256 (sum : Identifier) (x y : Literal) (s₀ s₉ : State) : Prop := sorry

lemma checked_add_uint256_abs_of_concrete {s₀ s₉ : State} {sum x y} :
  Spec (checked_add_uint256_concrete_of_code.1 sum x y) s₀ s₉ →
  Spec (A_checked_add_uint256 sum x y) s₀ s₉ := by
  unfold checked_add_uint256_concrete_of_code A_checked_add_uint256
  sorry

end

end Generated.ERC20simple.ERC20Shim
