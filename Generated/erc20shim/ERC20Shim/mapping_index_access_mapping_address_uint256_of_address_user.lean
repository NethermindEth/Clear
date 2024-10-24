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
  -- s₉.store = s₀⟦dataSlot ↦ keccak⟧.store ∧
  s₉.store.lookup dataSlot = some keccak) ∧
  s₉.evm.hash_collision = false)
  ∨ s₉.evm.hash_collision = true)
  ∧ (s₀.evm.hash_collision = true → s₉.evm.hash_collision = true)

-- Helper reifications
lemma shift_eq_size : Fin.shiftLeft (n := UInt256.size) 1 160 = Address.size := by
  constructor

lemma EVMAddrSize' {s : State} : (s, [Fin.shiftLeft 1 160]) = (s, [Address.size.toUInt256]) := by
  simp
  exact shift_eq_size

set_option maxHeartbeats 200000
set_option maxRecDepth 800
set_option pp.deepTerms true
set_option pp.proofs true

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

  unfold keccak256 at code
  unfold_let at code

  split at code
  -- some
  case h_1 x h_lookup =>
    right -- no hash collision
    split at h_lookup
    case h_1 val heq =>
      rw [Option.some_inj] at h_lookup
      -- lookup existing
      rw [ interval'_eq_interval 2 two_ne_zero (by norm_cast)
         , ← prep_def
         , mstore_mstore_of_ne, interval_of_mstore_eq_val_cons
         , mstore_mstore_of_ne, zero_add, interval_of_mstore_eq_val_cons
         , interval_of_0_eq_nil
         ] at heq
      -- make sense of the code
      rw [← h_lookup] at code
      simp only [Fin.isValue, multifill_cons, multifill_nil'] at code
      unfold setEvm State.insert State.lookup! at code
      simp only [Fin.isValue, Finmap.lookup_insert, get!_some, isOk_Ok] at code
      rw [← State.insert_of_ok] at code

      rw [← code]
      simp only [isOk_Ok, isOutOfFuel_insert', isOutOfFuel_Ok, not_false_eq_true, isOk_insert, evm_insert,
  get_evm_of_ok, true_and]
      split_ands

      rw [preservesEvm_of_insert']
      apply preservesEvm_of_preserved
      simp [get_evm_of_ok]
      exact Preserved_prep
      use val, (prep_def ▸ heq)
      simp only [insert_of_ok, store]

    case h_2 val heq =>
      split at h_lookup
      swap; contradiction
      rw [Option.some_inj] at h_lookup
      
      have : Finmap.lookup [account.val.cast, slot] state_prep.keccak_map = none := by
        rw [ interval'_eq_interval 2 two_ne_zero (by norm_cast)
           , ← prep_def
           , mstore_mstore_of_ne, interval_of_mstore_eq_val_cons
           , mstore_mstore_of_ne, zero_add, interval_of_mstore_eq_val_cons
           , interval_of_0_eq_nil
           ] at heq
        exact (prep_def ▸ heq)
      have int_ne_mem_map : [↑↑account, slot] ∉ state_prep.keccak_map := sorry

      simp at code
      unfold setEvm State.insert State.lookup! at code
      simp at code
      simp only [← h_lookup, ← State.insert_of_ok] at code
      rw [← code]

      split_ands
      rw [preservesEvm_of_insert']
      apply preservesEvm_of_preserved
      simp [get_evm_of_ok]
      apply Preserved.trans Preserved_prep
    
      -- obtain ⟨res, σ'⟩ := x
      -- injection h_lookup with res_eq σ'_eq
      exact Preserved_of_updated_keccak_map (σ := state_prep) rfl
      done
    done

  case h_2 x h_lookup =>
    split at h_lookup
    done

  -- -- generalize interval_def : List.map (Nat.toUInt256 ∘ UInt256.fromBytes!)
  -- --                 (List.toChunks 32
  -- --                 (mkInterval' state_prep.machine_state.memory 0 64)) = interval at code

  -- -- have interval_eq : interval = mkInterval state_prep.machine_state.memory 0 2 := by sorry

  -- -- have : List.map (Nat.toUInt256 ∘ UInt256.fromBytes!)
  -- --                 (List.toChunks 32
  -- --                 (mkInterval' state_prep.machine_state.memory 0 64)) =
  -- --   mkInterval state_prep.machine_state.memory 0 2 := by sorry
  -- split at code
  -- next x h_lookup =>
  --   split at h_lookup
  --   done

  -- simp_rw [ interval'_eq_interval 2 two_ne_zero (by sorry)
  --    -- , mstore_mstore_of_ne, interval_of_mstore_eq_val_cons
  --    -- , mstore_mstore_of_ne, zero_add, interval_of_mstore_eq_val_cons
  --    -- , interval_of_0_eq_nil
  --    ] at code

  -- -- rw [ this ] at code
  -- rw [ mstore_preserves_keccak_map, mstore_preserves_keccak_map
  --    , hasAddress
  --    ]
  -- simp at prog
  -- unfold setEvm State.insert State.lookup! at prog
  -- simp at prog

  -- rw [← prog]
  -- unfold State.lookup!

  -- apply And.intro
  -- · apply preservesEvm_eq
  --   simp
  --   apply preserved_trans 
  --   · exact mstore_preserves
  --   · exact mstore_preserves
  -- · simp

  end

end Generated.erc20shim.ERC20Shim
