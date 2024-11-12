import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.checked_sub_uint256
import Generated.ERC20simple.ERC20Shim.checked_add_uint256

import Generated.ERC20simple.ERC20Shim.Common.if_668760047301878650_gen

import Generated.ERC20simple.ERC20Shim.Common.if_668760047301878650_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma if_668760047301878650_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_668760047301878650 s₀ = s₉ →
        Spec A_if_668760047301878650 s₀ s₉ :=
  λ _ h ↦ if_668760047301878650_abs_of_concrete (if_668760047301878650_concrete_of_code.2 h)

end

end ERC20Shim.Common
