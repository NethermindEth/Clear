import Clear.ReasoningPrinciple


import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address_gen

import Generated.erc20shim.ERC20Shim.Predicate
import Generated.erc20shim.ERC20Shim.Variables

namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

abbrev AddressMap := Finmap (λ _ : Address ↦ UInt256)

set_option linter.setOption false
set_option pp.coercions false

def A_mapping_index_access_mapping_address_uint256_of_address (dataSlot : Identifier) (slot key : Literal) (s₀ s₉ : State) : Prop :=
  let account := Address.ofUInt256 key
  ∀ {map : AddressMap}, account ∈ map →
  ∀ address,
  s₀.evm.keccak_map.lookup [ ↑account , slot ] = some address →
  s₉.isOk ∧ s₉[dataSlot]!! = address

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
  intro hasFuel
  clr_funargs

  rw [ EVMSub', EVMShl', EVMAddrSize' ]; simp
  rw [ Address.and_size_eq_ofUInt256 ]
  rw [ multifill_cons, multifill_nil ]
  simp

  clr_varstore

  generalize acconut_def : Address.ofUInt256 key = account
  intro prog erc20 account_mem_balances address hasAddress

  generalize prep_def : (mstore evm 0 ↑↑account).mstore 32 slot = state_prep
  unfold keccak256 at prog
  rw [ interval'_eq_interval 2 two_ne_zero (by norm_cast)
     , mstore_mstore_of_ne, interval_of_mstore_eq_val_cons
     , mstore_mstore_of_ne, zero_add, interval_of_mstore_eq_val_cons
     , interval_of_0_eq_nil
     ] at prog
  unfold_let at prog
  rw [ mstore_preserves_keccak_map, mstore_preserves_keccak_map
     , hasAddress
     ] at prog
  simp at prog
  unfold setEvm State.insert State.lookup! at prog
  simp at prog

  rw [← prog]
  unfold State.lookup!
  simp

end

end Generated.erc20shim.ERC20Shim
