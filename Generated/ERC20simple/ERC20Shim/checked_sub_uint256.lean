import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_2792370840247009933
import Generated.ERC20simple.ERC20Shim.panic_error_0x11

import Generated.ERC20simple.ERC20Shim.checked_sub_uint256_gen

import Generated.ERC20simple.ERC20Shim.checked_sub_uint256_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

lemma checked_sub_uint256_abs_of_code {s₀ s₉ : State} {diff x y} {fuel : Nat} :
  execCall fuel checked_sub_uint256 [diff] (s₀, [x, y]) = s₉ →
  Spec (A_checked_sub_uint256 diff x y) s₀ s₉
:= λ h ↦ checked_sub_uint256_abs_of_concrete (checked_sub_uint256_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
