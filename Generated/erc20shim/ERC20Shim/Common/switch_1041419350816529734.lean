import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.update_storage_value_offsett_uint256_to_uint256

import Generated.erc20shim.ERC20Shim.Common.switch_1041419350816529734_gen

import Generated.erc20shim.ERC20Shim.Common.switch_1041419350816529734_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

lemma switch_1041419350816529734_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel switch_1041419350816529734 s₀ = s₉ →
        Spec A_switch_1041419350816529734 s₀ s₉ :=
  λ _ h ↦ switch_1041419350816529734_abs_of_concrete (switch_1041419350816529734_concrete_of_code.2 h)

end

end ERC20Shim.Common
