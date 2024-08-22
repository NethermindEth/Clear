import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_mapping_index_access_mapping_address_uint256_of_address (dataSlot : Identifier) (slot key : Literal) (s₀ s₉ : State) : Prop :=
  let s₁ := s₀ 🇪⟦ s₀.evm.mstore 0x00 (Address.ofUInt256 key) ⟧
  let s₂ := s₁ 🇪⟦ s₁.evm.mstore 0x20 slot ⟧
  match s₂.evm.keccak256 0x00 0x40 with
  | some ⟨addr, evm⟩ => s₉ = s₂ 🇪⟦ evm ⟧⟦ dataSlot ↦ addr ⟧
  | none => s₉.evm.hash_collision = True

-- Helper reifications
lemma shift_eq_size : Fin.shiftLeft (n := UInt256.size) 1 160 = Address.size := by
  constructor

lemma EVMAddrSize' {s : State} : (s, [Fin.shiftLeft 1 160]) = (s, [Address.size.toUInt256]) := by
  simp
  exact shift_eq_size

lemma mapping_index_access_mapping_address_uint256_of_address_abs_of_concrete {s₀ s₉ : State} {dataSlot slot key} :
  Spec (mapping_index_access_mapping_address_uint256_of_address_concrete_of_code.1 dataSlot slot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_address_uint256_of_address dataSlot slot key) s₀ s₉ := by
  unfold mapping_index_access_mapping_address_uint256_of_address_concrete_of_code A_mapping_index_access_mapping_address_uint256_of_address  
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs

  rw [ EVMSub', EVMShl', EVMAddrSize' ]; simp
  rw [ Address.and_size_eq_ofUInt256 ]
  rw [ multifill_cons, multifill_nil ]
  simp

  clr_varstore

  generalize prep_def : (mstore evm 0 ↑↑(Address.ofUInt256 key)).mstore 32 slot = state_prep

  cases state_prep.keccak256 0 64
  · aesop_spec
  · simp
    unfold setEvm State.insert
    aesop_spec

end

end Generated.erc20shim.ERC20Shim
