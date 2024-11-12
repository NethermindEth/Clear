import Clear.ReasoningPrinciple

import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.ERC20simple.ERC20Shim.update_storage_value_offsett_uint256_to_uint256

import Generated.ERC20simple.ERC20Shim.Common.switch_6048342142894339161_gen

import Generated.ERC20simple.ERC20Shim.Common.switch_6048342142894339161_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.ERC20simple ERC20Shim

lemma switch_6048342142894339161_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel switch_6048342142894339161 s₀ = s₉ →
        Spec A_switch_6048342142894339161 s₀ s₉ :=
  λ _ h ↦ switch_6048342142894339161_abs_of_concrete (switch_6048342142894339161_concrete_of_code.2 h)

end

end ERC20Shim.Common
