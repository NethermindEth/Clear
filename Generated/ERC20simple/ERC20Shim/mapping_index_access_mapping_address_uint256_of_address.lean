import Clear.ReasoningPrinciple


import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address_gen

import Generated.ERC20simple.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address_user


namespace Generated.ERC20simple.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

lemma mapping_index_access_mapping_address_uint256_of_address_abs_of_code {s₀ s₉ : State} {dataSlot slot key} {fuel : Nat} :
  execCall fuel mapping_index_access_mapping_address_uint256_of_address [dataSlot] (s₀, [slot, key]) = s₉ →
  Spec (A_mapping_index_access_mapping_address_uint256_of_address dataSlot slot key) s₀ s₉
:= λ h ↦ mapping_index_access_mapping_address_uint256_of_address_abs_of_concrete (mapping_index_access_mapping_address_uint256_of_address_concrete_of_code.2 h)

end

end Generated.ERC20simple.ERC20Shim
