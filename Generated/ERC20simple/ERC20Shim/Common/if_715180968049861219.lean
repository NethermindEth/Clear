import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.Common.if_6086122604910941386
import Generated.ERC20simple.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.ERC20simple.ERC20Shim.fun_approve_532

import Generated.ERC20simple.ERC20Shim.Common.if_715180968049861219_gen

import Generated.ERC20simple.ERC20Shim.Common.if_715180968049861219_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.ERC20simple ERC20Shim

lemma if_715180968049861219_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel if_715180968049861219 s₀ = s₉ →
        Spec A_if_715180968049861219 s₀ s₉ :=
  λ _ h ↦ if_715180968049861219_abs_of_concrete (if_715180968049861219_concrete_of_code.2 h)

end

end ERC20Shim.Common
