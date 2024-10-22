import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_mapping_address_uint256_of_address_gen
import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address_user

namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

def A_mapping_index_access_mapping_address_mapping_address_uint256_of_address (dataSlot : Identifier) (slot key : Literal) (s₀ s₉ : State) : Prop :=
  A_mapping_index_access_mapping_address_uint256_of_address dataSlot slot key s₀ s₉

lemma mapping_index_access_mapping_address_mapping_address_uint256_of_address_abs_of_concrete {s₀ s₉ : State} {dataSlot slot key} :
  Spec (mapping_index_access_mapping_address_mapping_address_uint256_of_address_concrete_of_code.1 dataSlot slot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_address_mapping_address_uint256_of_address dataSlot slot key) s₀ s₉ := by
  unfold mapping_index_access_mapping_address_mapping_address_uint256_of_address_concrete_of_code A_mapping_index_access_mapping_address_mapping_address_uint256_of_address
         A_mapping_index_access_mapping_address_uint256_of_address

  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  intro hasFuel
  clr_funargs
  sorry


end

end Generated.erc20shim.ERC20Shim
