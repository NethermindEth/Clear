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
  ((preservesEvm s₀ s₉ ∧ s₉.isOk ∧ (∃ keccak,
  s₉.evm.keccak_map.lookup [ ↑(Address.ofUInt256 key), slot ] = some keccak ∧
  s₉.store = s₀⟦dataSlot ↦ keccak⟧.store) ∧
  s₉.evm.hash_collision = false)
  ∨ s₉.evm.hash_collision = true)
  ∧ (s₀.evm.hash_collision = true → s₉.evm.hash_collision = true)

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
  intro code
  unfold reviveJump at code

  generalize prep_def : (mstore evm 0 ↑↑account).mstore 32 slot = state_prep at code
  have Preserved_prep : Preserved evm state_prep := by
    rw [← prep_def];
    exact Preserved.trans mstore_preserved mstore_preserved

  split at code
  case h_1 _ res keccak_eq_some_res =>
    simp only [multifill_cons, multifill_nil'] at code
    unfold setEvm State.insert State.lookup! at code
    simp only [Fin.isValue, Finmap.lookup_insert, get!_some, isOk_Ok] at code
    rw [← State.insert_of_ok] at code
    rw [← code]

    have res_collision := hash_collision_of_keccak256_eq_some keccak_eq_some_res
    have prep_collision : state_prep.hash_collision = evm.hash_collision := by
      rw [← prep_def]
      exact Eq.trans hash_collision_of_mstore hash_collision_of_mstore
      
    have preserves_collision :
      evm.hash_collision = true → Ok res.2 varstore⟦dataSlot↦res.1⟧.evm.hash_collision = true := by      
      rw [State.insert_of_ok, get_evm_of_ok, res_collision, prep_collision]
      intro h; exact h
    
    apply And.intro
    swap; exact preserves_collision
    
    by_cases h : evm.hash_collision
    right
    -- hash_collision from the previous state
    exact preserves_collision h
    
    -- no hash collision from the previous state
    left; split_ands
    -- preservesEvm
    rw [preservesEvm_of_insert']
    apply preservesEvm_of_preserved
    rw [get_evm_of_ok, get_evm_of_ok]
    exact Preserved.trans Preserved_prep (Preserved_of_keccek256 keccak_eq_some_res)

    -- state is ok
    exact State.isOk_Ok

    -- keccak
    use res.1
    split_ands
    -- keccak lookup for last
    rotate_left
    -- varstore preservation
    rw [State.insert_of_ok]
    simp only [State.store]
    
    -- no hash collision
    rw [State.insert_of_ok, get_evm_of_ok, res_collision, prep_collision]
    rw [Bool.eq_false_eq_not_eq_true] at h; exact h
    
    -- keccak lookup
    rw [State.insert_of_ok, get_evm_of_ok]
    unfold keccak256 at keccak_eq_some_res
    rw [ interval'_eq_interval 2 two_ne_zero (by norm_cast)
       , ← prep_def
       , mstore_mstore_of_ne, interval_of_mstore_eq_val_cons
       , mstore_mstore_of_ne, zero_add, interval_of_mstore_eq_val_cons
       , interval_of_0_eq_nil
       ] at keccak_eq_some_res
    unfold_let at keccak_eq_some_res

    split at keccak_eq_some_res
    case h_1 _ v h_lookup =>
      rw [Option.some_inj] at keccak_eq_some_res
      rw [← keccak_eq_some_res]
      exact h_lookup
    case h_2 _ h_lookup =>
      split at keccak_eq_some_res
      swap; contradiction
      rw [Option.some_inj] at keccak_eq_some_res
      rw [← keccak_eq_some_res]
      simp only [];
      rw [Finmap.lookup_insert]

  case h_2 res keccak_eq_none =>
    simp only [multifill_cons, multifill_nil'] at code
    unfold setEvm State.insert State.lookup! at code
    simp only [Fin.isValue, Finmap.lookup_insert, get!_some, isOk_Ok] at code
    rw [← State.insert_of_ok] at code
    
    have final_destination : s₉.evm.hash_collision := by
      rw [← code, State.insert_of_ok, get_evm_of_ok]
      exact hash_collision_of_addHashCollision state_prep

    apply And.intro
    right; exact final_destination
    intro _; exact final_destination

  end

end Generated.erc20shim.ERC20Shim
