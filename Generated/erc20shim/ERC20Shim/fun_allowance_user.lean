import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun_allowance_gen

import Generated.erc20shim.ERC20Shim.Predicate

namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

set_option maxHeartbeats 1000000

def A_fun_allowance (var : Identifier) (var_owner var_spender : Literal) (s₀ s₉ : State) : Prop :=
  (∀ {erc20}, (IsERC20 erc20 s₀ ∧ s₀.evm.isEVMState) →
  let owner := Address.ofUInt256 var_owner
  let spender := Address.ofUInt256 var_spender
  IsERC20 erc20 s₉ ∧ preservesEvm s₀ s₉ ∧
  s₉[var]!! = (erc20.allowances.lookup ⟨owner, spender⟩).getD 0 ∧
  s₉.evm.hash_collision = false)
  ∨ s₉.evm.hash_collision = true

lemma fun_allowance_abs_of_concrete {s₀ s₉ : State} {var var_owner var_spender} :
  Spec (fun_allowance_concrete_of_code.1 var var_owner var_spender) s₀ s₉ →
  Spec (A_fun_allowance var var_owner var_spender) s₀ s₉ := by
  unfold fun_allowance_concrete_of_code A_fun_allowance

  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  rintro hasFuel ⟨s, mapping, ⟨s', mapping', code⟩⟩

  clr_varstore,

  -- what we can get right now from mapping function
  unfold A_mapping_index_access_mapping_address_mapping_address_uint256_of_address
         A_mapping_index_access_mapping_address_uint256_of_address at mapping
  clr_spec at mapping



  obtain ⟨s_isOk, ⟨preservesEvm, s_isEVMStatePreserved, ⟨⟨intermediate_keccak, keccak_using_intermediate, hStore⟩,hHashCollision⟩⟩, hHashCollision₁⟩ := mapping -- Adds a goal
  · -- No hash collision from first keccak

    obtain ⟨evmₛ, varstoreₛ, s_eq_ok⟩ := State_of_isOk s_isOk
    have keccak : Finmap.lookup [↑↑(Address.ofUInt256 var_owner), 1] s.evm.keccak_map = some (s["_2"]!!) := by
      unfold store State.insert at hStore
      unfold lookup!
      aesop
    rw [ ← Variables.allowances_def
     , s_eq_ok, get_evm_of_ok, ← s_eq_ok
     ] at keccak

    -- what we can get right now from mapping' function
    unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping'
    clr_spec at mapping'

    obtain ⟨s_isOk', ⟨preservesEvm', s_isEVMStatePreserved', ⟨⟨intermediate_keccak', keccak_using_intermediate', hStore'⟩,hHashCollision'⟩⟩, hHashCollision₁'⟩ := mapping' -- Adds a goal
    · -- No hash collision from second keccak
      left
      intro erc20 is_erc20 s₀_isEVMState
      obtain ⟨evmₛ', varstoreₛ', s_eq_ok'⟩ := State_of_isOk s_isOk'
      have keccak' : Finmap.lookup [↑↑(Address.ofUInt256 (s["var_spender"]!!)), s["_2"]!!] s'.evm.keccak_map = some (s'["_3"]!!) := by
        rw [s_eq_ok]
        rw [s_eq_ok] at hStore'
        rw [s_eq_ok']
        rw [s_eq_ok'] at hStore'
        unfold store at hStore'
        simp at hStore'
        unfold State.insert at hStore'
        simp at hStore'
        conv_lhs => rw[←s_eq_ok]; rw[←s_eq_ok']
        rw [hStore']
        unfold lookup!
        simp
        exact keccak_using_intermediate'
      rw [ s_eq_ok', get_evm_of_ok, ← s_eq_ok'
        ] at keccak'

      -- simplify contract
      unfold reviveJump at code
      simp [s_eq_ok, s_eq_ok'] at code
      rw [ ← State.insert_of_ok,  ← State.insert_of_ok, ← s_eq_ok' ] at code
      clr_varstore,

      -- get underlying Preserved from preservesEvm
      rw [ s_eq_ok, preservesEvm_of_insert, preservesEvm_of_insert ] at preservesEvm
      have hPreserved := Preserved_of_preservesEvm_of_Ok preservesEvm

      -- get underlying Preserved from preservesEvm'
      rw [ s_eq_ok, s_eq_ok'] at preservesEvm'
      have hPreserved' := Preserved_of_preservesEvm_of_Ok preservesEvm'

      -- make use of transitivity of Preserved
      have hPreserved'' : Clear.Preserved evm evmₛ' := Preserved.trans hPreserved hPreserved'

      refine' ⟨IsERC20_of_preservesEvm (by aesop) is_erc20, (by aesop), ?returns_correct_value⟩
      rw [← code]
      -- lookup allowance
      clr_varstore,
      by_cases mem : ⟨Address.ofUInt256 var_owner, Address.ofUInt256 var_spender⟩ ∈ erc20.allowances
      · -- there is such ⟨owner, spender⟩ in allowances
        split_ands <;> [skip; aesop]

        obtain ⟨address, intermediate, has_intermediate, has_address, allowance⟩ := is_erc20.hasAllowance mem

        have intermediate_def : s["_2"]!! = intermediate := by
          rw [s_eq_ok]
          rw [← Option.some_inj]
          trans
          · have := Eq.symm (s_eq_ok ▸ keccak)
            exact this
          · exact (keccak_map_lookup_eq_of_Preserved_of_lookup hPreserved has_intermediate
              ▸ has_intermediate)

        have address_def : s'["_3"]!! = address := by
          rw [s_eq_ok']
          rw [← Option.some_inj]
          trans
          · have := Eq.symm (s_eq_ok' ▸ keccak')
            exact this
          · rw [intermediate_def]
            have : s["var_spender"]!! = var_spender := by
              rw [s_eq_ok]
              rw [s_eq_ok] at hStore
              unfold store at hStore
              unfold State.insert at hStore
              simp at hStore
              rw [hStore]
              unfold lookup!
              simp
              rw [Finmap.lookup_insert_of_ne _ (by unfold Ne; apply String.ne_of_data_ne; simp)
                , Finmap.lookup_insert_of_ne _ (by unfold Ne; apply String.ne_of_data_ne; simp)
                , Finmap.lookup_insert_of_ne _ (by unfold Ne; apply String.ne_of_data_ne; simp)]
              simp
            rw [this]
            exact (keccak_map_lookup_eq_of_Preserved_of_lookup hPreserved'' has_address ▸ has_address)

        rw [address_def] at code ⊢
        rw [ allowance
          , Option.getD_some
          , State.get_evm_of_ok
          , ← sload_eq_of_preserved hPreserved''
          ]
      · -- there is *no* such account in allowances
        -- so sload should return 0

        split_ands <;> [skip; aesop]

        rw [ Finmap.lookup_eq_none.mpr mem
          , Option.getD_none
          ]

        -- in order to do that it should be given storage address outside of
        -- its domain
        apply sload_of_not_mem_dom
        have := State.get_evm_of_ok ▸ is_erc20.storageDom
        rw [ ← storage_eq_of_preserved hPreserved''
          , this
          ]
        clear this
        simp only [ Finset.not_mem_union, Set.mem_toFinset, Set.mem_def, setOf, not_exists, not_and ]
        have s_erc20 : IsERC20 erc20 (Ok evmₛ _) :=
          IsERC20_of_ok_of_Preserved hPreserved is_erc20
        have s_erc20' : IsERC20 erc20 (Ok evmₛ' _) :=
          IsERC20_of_ok_of_Preserved hPreserved' s_erc20

        split_ands
        -- address not in balances
        · intro account account_mem_balances
          obtain ⟨address, has_address, balance⟩ := is_erc20.hasBalance account_mem_balances
          rw [ ← keccak'
            , keccak_map_lookup_eq_of_Preserved_of_lookup
                hPreserved'' has_address ]
          by_contra h
          have : [↑↑account, ERC20Private.balances] ∈ evmₛ'.keccak_map.keys := by
            rw [Finmap.mem_keys]
            apply Finmap.lookup_isSome.mp
            have := get_evm_of_ok ▸ has_address
            rw [ ← keccak_map_lookup_eq_of_Preserved_of_lookup hPreserved'' has_address
              , this ]
            simp
          have IsEVMₛ' : evmₛ'.isEVMState := by aesop
          have keccak_inj := IsEVMₛ'.1 this (Eq.symm h)

          rw [← Fin.ofNat''_eq_cast, ← Fin.ofNat''_eq_cast] at keccak_inj
          unfold Fin.ofNat'' at keccak_inj
          simp at keccak_inj
          obtain ⟨keccak_inj₁, keccak_inj₂⟩ := keccak_inj

          have : ERC20Private.balances ≠ s["_2"]!! := by
            obtain blocked_range := get_evm_of_ok ▸ s_erc20.block_acc_range.2.1
            rw [ keccak ] at blocked_range
            apply not_mem_private_of_some at blocked_range
            rw [@ne_comm]
            unfold PrivateAddresses.toFinset at blocked_range
            rw [Finset.mem_def] at blocked_range
            simp at blocked_range -- Fails with: set_option maxHeartbeats 200000
            exact blocked_range.1
          contradiction

        -- address not in allowances
        · intro owner spender owner_spender_mem_allowances

          obtain ⟨erc_address, erc_intermediate, owner_lookup, spender_lookup, eq⟩ :=
            is_erc20.hasAllowance owner_spender_mem_allowances

          rw [ ← keccak'
          , keccak_map_lookup_eq_of_Preserved_of_lookup
              hPreserved'' owner_lookup ]
          by_contra h
          have : [↑↑owner, ERC20Private.allowances] ∈ evmₛ.keccak_map.keys := by
            rw [Finmap.mem_keys]
            apply Finmap.lookup_isSome.mp
            have owner_lookup' := get_evm_of_ok ▸ owner_lookup
            have spender_lookup' := get_evm_of_ok ▸ spender_lookup
            rw [ ← keccak_map_lookup_eq_of_Preserved_of_lookup hPreserved owner_lookup
              , owner_lookup' ]
            simp
          have owner_lookup' := get_evm_of_ok ▸ owner_lookup
          have := keccak_map_lookup_eq_of_Preserved_of_lookup hPreserved'' owner_lookup
          rw [this] at owner_lookup'
          have hSpender := h owner_lookup'


          have spender_lookup' := get_evm_of_ok ▸ spender_lookup
          have := keccak_map_lookup_eq_of_Preserved_of_lookup hPreserved'' spender_lookup'
          rw [this] at hSpender

          have : [↑↑(Address.ofUInt256 (s["var_spender"]!!)), s["_2"]!!] ∈ evmₛ'.keccak_map.keys := by
            clear * -keccak_using_intermediate' s_eq_ok'
            rw [s_eq_ok'] at keccak_using_intermediate'
            simp at keccak_using_intermediate'
            exact Finmap.mem_of_lookup_eq_some keccak_using_intermediate'
          have IsEVMₛ' : evmₛ'.isEVMState := by aesop
          have keccak_inj := IsEVMₛ'.1 this (Eq.symm hSpender)
          rw [← Fin.ofNat''_eq_cast, ← Fin.ofNat''_eq_cast] at keccak_inj
          unfold Fin.ofNat'' at keccak_inj
          simp at keccak_inj
          rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Fin.val_eq_val] at keccak_inj <;> [skip; exact Address.val_lt_UInt256_size; exact Address.val_lt_UInt256_size]

          obtain ⟨keccak_inj₁, keccak_inj₂⟩ := keccak_inj


          have hOwner : owner = Address.ofUInt256 var_owner := by
            have := keccak_map_lookup_eq_of_Preserved_of_lookup hPreserved owner_lookup
            rw [←keccak_inj₂] at owner_lookup
            rw [←keccak] at owner_lookup
            have owner_lookup'' := get_evm_of_ok ▸ owner_lookup
            rw [this] at owner_lookup''

            have : [↑↑(Address.ofUInt256 var_owner), ERC20Private.allowances] ∈ evmₛ.keccak_map.keys := by
              clear * -keccak_using_intermediate s_eq_ok
              rw [s_eq_ok] at keccak_using_intermediate
              simp at keccak_using_intermediate
              exact Finmap.mem_of_lookup_eq_some keccak_using_intermediate
            have IsEVMₛ : evmₛ.isEVMState := by aesop
            have keccak_inj := IsEVMₛ.1 this (Eq.symm owner_lookup'')
            rw [← Fin.ofNat''_eq_cast, ← Fin.ofNat''_eq_cast] at keccak_inj
            unfold Fin.ofNat'' at keccak_inj
            simp at keccak_inj
            rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Fin.val_eq_val] at keccak_inj <;> [skip; exact Address.val_lt_UInt256_size; exact Address.val_lt_UInt256_size]
            symm
            exact keccak_inj

          have hSpender : spender = Address.ofUInt256 var_spender := by
            have : s["var_spender"]!! = var_spender := by
              rw [s_eq_ok]
              rw [s_eq_ok] at hStore
              unfold store at hStore
              unfold State.insert at hStore
              simp at hStore
              rw [hStore]
              unfold lookup!
              simp
              rw [Finmap.lookup_insert_of_ne _ (by unfold Ne; apply String.ne_of_data_ne; simp)
                , Finmap.lookup_insert_of_ne _ (by unfold Ne; apply String.ne_of_data_ne; simp)
                , Finmap.lookup_insert_of_ne _ (by unfold Ne; apply String.ne_of_data_ne; simp)]
              simp
            rw [this] at keccak_inj₁
            symm
            exact keccak_inj₁
            done
          rw [←hOwner, ←hSpender] at mem
          contradiction

        -- address not in reserved space
        · obtain blocked_range := get_evm_of_ok ▸ (s_erc20'.block_acc_range.2.2)
          have := keccak_map_lookup_eq_of_Preserved_of_lookup hPreserved' keccak
          rw [this] at keccak
          rw [ keccak ] at blocked_range

          have blocked_range' := blocked_range (↑↑(Address.ofUInt256 (s["var_spender"]!!))) (s["_2"]!!) (by rfl)
          rw [←Finset.mem_map' Function.Embedding.some]

          -- TODO make simpler:
          have : Function.Embedding.some (s'["_3"]!!) = (some (s'["_3"]!!)) := by
            simp
          rw [this]
          rw [←keccak']

          unfold not_mem_private at blocked_range'
          rw [keccak'] at blocked_range'
          simp at blocked_range'
          rw [keccak']
          simp
          exact blocked_range'

      done
    · -- Hash collision from second keccak
      rename_i hHashCollisionTrue
      right
      have :   hash_collision (Ok evm Inhabited.default⟦"var_spender"↦var_spender⟧⟦"var_owner"↦var_owner⟧⟦"_1"↦1⟧.evm)
         = evm.hash_collision := by
        simp
      rw [this] at hHashCollision₁
      by_cases s_isOk' : s'.isOk
      · obtain ⟨evmₛ', varstoreₛ', s_eq_ok'⟩ := State_of_isOk s_isOk'
        -- simplify contract
        unfold reviveJump at code
        simp [s_eq_ok, s_eq_ok'] at code
        rw [ ← State.insert_of_ok,  ← State.insert_of_ok, ← s_eq_ok' ] at code
        clr_varstore,

        rw [←code]
        aesop
      · rcases s' with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; skip]
        · unfold reviveJump at code
          simp at code
          rw [←code]
          aesop
        · unfold reviveJump at code
          simp at code

          rename_i j
          unfold evm at hHashCollisionTrue
          simp at hHashCollisionTrue
  · -- Hash collision from first keccak
    rename_i hHashCollisionTrue
    right

    by_cases s_isOk : s.isOk
    · unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping'
      clr_spec at mapping'

      obtain ⟨s_isOk', ⟨preservesEvm', s_isEVMStatePreserved', ⟨⟨intermediate_keccak', keccak_using_intermediate', hStore'⟩,hHashCollision'⟩⟩, hHashCollision₁'⟩ := mapping' -- Adds a goal

      have :   hash_collision (Ok evm Inhabited.default⟦"var_spender"↦var_spender⟧⟦"var_owner"↦var_owner⟧⟦"_1"↦1⟧.evm)
          = evm.hash_collision := by
          simp
      rw [this] at hHashCollision₁
      by_cases s_isOk' : s'.isOk
      · obtain ⟨evmₛ', varstoreₛ', s_eq_ok'⟩ := State_of_isOk s_isOk'
        -- simplify contract
        unfold reviveJump at code
        simp [s_eq_ok'] at code
        rw [ ← State.insert_of_ok,  ← State.insert_of_ok, ← s_eq_ok' ] at code
        clr_varstore,

        · rw [←code]
          have : Ok evmₛ' varstore⟦var↦sload evmₛ' (s'["_3"]!!)⟧.evm.hash_collision
                = evmₛ'.hash_collision := by simp
          rw [this]
          aesop


      · rcases s' with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; skip]
        · unfold reviveJump at code
          simp at code
          rw [←code]
          aesop

        · unfold reviveJump at code
          simp at code
          rename_i j
          rcases j
      · rename_i hHashCollisionTrue'
        have : Ok evm Inhabited.default⟦"var_spender"↦var_spender⟧⟦"var_owner"↦var_owner⟧⟦"_1"↦1⟧.evm.hash_collision
              = evm.hash_collision := by simp
        rw [this] at hHashCollision₁
        rcases s' with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; skip]
        · unfold reviveJump at code
          simp at code
          rw [←code]
          aesop

        · unfold reviveJump at code
          simp at code
          unfold evm at hHashCollisionTrue'
          simp at hHashCollisionTrue'
    · unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping'
      unfold Spec at mapping'
      rcases s with ⟨evm, varstore⟩ | _ | _ <;> [skip; skip; skip]
      · aesop
      · simp at mapping'
        rcases s' with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec
      · simp at mapping'
        rcases s' with ⟨evm, varstore⟩ | _ | _ <;> [skip;skip;skip]
        · simp at mapping'
        · simp at mapping'
        · unfold evm at hHashCollisionTrue
          simp at hHashCollisionTrue

end

end Generated.erc20shim.ERC20Shim
