import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.Common.if_3989404597755436942
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.erc20shim.ERC20Shim.checked_add_uint256

import Generated.erc20shim.ERC20Shim.Common.switch_2364266820542243941_gen

import Generated.erc20shim.ERC20Shim.Common.switch_2364266820542243941_user


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

lemma switch_2364266820542243941_abs_of_code {s₀ : State} {fuel : Nat} :
  ∀ s₉, exec fuel switch_2364266820542243941 s₀ = s₉ →
        Spec A_switch_2364266820542243941 s₀ s₉ :=
  λ _ h ↦ switch_2364266820542243941_abs_of_concrete (switch_2364266820542243941_concrete_of_code.2 h)

end

end ERC20Shim.Common
