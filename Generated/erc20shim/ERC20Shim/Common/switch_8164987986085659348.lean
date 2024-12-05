import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.array_dataslot_string_storage
import Generated.erc20shim.ERC20Shim.Common.for_1821242857744567453

import Generated.erc20shim.ERC20Shim.Common.switch_8164987986085659348_gen

import Generated.erc20shim.ERC20Shim.Common.switch_8164987986085659348_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

lemma switch_8164987986085659348_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel switch_8164987986085659348 s₀ = s₉ →
        Spec A_switch_8164987986085659348 s₀ s₉ :=
  λ _ h ↦ switch_8164987986085659348_abs_of_concrete (switch_8164987986085659348_concrete_of_code.2 h)

end

end ERC20Shim.Common
