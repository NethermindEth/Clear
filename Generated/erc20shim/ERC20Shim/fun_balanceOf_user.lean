import Clear.ReasoningPrinciple

-- import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.fun_balanceOf_gen

import Generated.erc20shim.ERC20Shim.Predicate

namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_fun_balanceOf (var : Identifier) (var_account : Literal) (s₀ s₉ : State) : Prop :=
  (∀ {erc20}, (IsERC20 erc20 s₀ ∧ s₀.evm.isEVMState) →
  let account := Address.ofUInt256 var_account
  IsERC20 erc20 s₉ ∧ preservesEvm s₀ s₉ ∧
  s₉[var]!! = (erc20.balances.lookup account).getD 0 ∧
  s₉.evm.hash_collision = false)
  ∨ s₉.evm.hash_collision = true

lemma fun_balanceOf_abs_of_concrete {s₀ s₉ : State} {var var_account} :
  Spec (fun_balanceOf_concrete_of_code.1 var var_account) s₀ s₉ →
  Spec (A_fun_balanceOf var var_account) s₀ s₉ := by
  unfold fun_balanceOf_concrete_of_code A_fun_balanceOf

  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  rintro hasFuel ⟨s, mapping, code⟩

  clr_varstore

  -- what we can get right now from mapping function
  unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping
  clr_spec at mapping

  
  obtain ⟨⟨preservesEvm, s_isOk, s_isEVMStatePreserved, ⟨⟨keccak_value, keccak_using_keccak_value, hStore⟩,hHashCollision⟩⟩, hHashCollision₁⟩ := mapping -- Adds a goal
  · -- No hash collision from keccak
    left
    intro erc20 is_erc20 s₀_isEVMState

    obtain ⟨evmₛ, varstoreₛ, s_eq_ok⟩ := State_of_isOk s_isOk

    have keccak : Finmap.lookup [↑↑(Address.ofUInt256 var_account), 0] s.evm.keccak_map = some (s["_2"]!!) := by
      unfold store State.insert at hStore
      unfold lookup!
      aesop

    rw [ ← Variables.balances_def
      , s_eq_ok, get_evm_of_ok, ← s_eq_ok
      ] at keccak

    -- simplify contract
    unfold reviveJump at code
    simp [s_eq_ok] at code
    rw [ ← State.insert_of_ok,  ← State.insert_of_ok, ← s_eq_ok ] at code
    clr_varstore

    -- get underlying Preserved from preservesEvm
    rw [ s_eq_ok, preservesEvm_of_insert, preservesEvm_of_insert ] at preservesEvm
    have Preserved := Preserved_of_preservesEvm_of_Ok preservesEvm

    refine' ⟨IsERC20_of_preservesEvm (by aesop) is_erc20, (by aesop), ?returns_correct_value⟩

    rw [← code]
    -- lookup balance
    clr_varstore
    by_cases mem : Address.ofUInt256 var_account ∈ erc20.balances
    · -- there is such account in balances
      split_ands <;> [skip; aesop]

      obtain ⟨address, has_address, balance⟩ := is_erc20.hasBalance mem

      have address_def : s["_2"]!! = address := by
        rw [s_eq_ok]
        rw [← Option.some_inj]
        trans
        · exact Eq.symm (s_eq_ok ▸ keccak)
        · exact (keccak_map_lookup_eq_of_Preserved_of_lookup Preserved has_address
            ▸ has_address)

      rw [address_def] at code ⊢
      rw [ balance
        , Option.getD_some
        , State.get_evm_of_ok
        , ← sload_eq_of_preserved Preserved
        ]

    · -- there is *no* such account in balances
      -- so sload should return 0
    
      split_ands <;> [skip; aesop]

      rw [ Finmap.lookup_eq_none.mpr mem
        , Option.getD_none
        ]

      -- in order to do that it should be given storage address outside of
      -- it's domain
      apply sload_of_not_mem_dom
      have := State.get_evm_of_ok ▸ is_erc20.storageDom
      rw [ ← storage_eq_of_preserved Preserved
        , this
        ]
      clear this
      simp only [ Finset.not_mem_union, Set.mem_toFinset, Set.mem_def, setOf, not_exists, not_and ]
      have s_erc20 : IsERC20 erc20 (Ok evmₛ _) :=
        IsERC20_of_ok_of_Preserved Preserved is_erc20

      split_ands
      -- address not in balances
      · intro account account_mem_balances
        obtain ⟨address, has_address, balance⟩ := is_erc20.hasBalance account_mem_balances
        rw [ ← keccak
          , keccak_map_lookup_eq_of_Preserved_of_lookup
              Preserved has_address ]
        by_contra h
        have : [↑↑account, ERC20Private.balances] ∈ evmₛ.keccak_map.keys := by
          rw [Finmap.mem_keys]
          apply Finmap.lookup_isSome.mp
          have := get_evm_of_ok ▸ has_address
          rw [ ← keccak_map_lookup_eq_of_Preserved_of_lookup Preserved has_address
            , this ]
          simp
        have IsEVMₛ : evmₛ.isEVMState := by aesop
        have keccak_inj := IsEVMₛ.1 this (Eq.symm h)

        rw [← Fin.ofNat''_eq_cast, ← Fin.ofNat''_eq_cast] at keccak_inj
        unfold Fin.ofNat'' at keccak_inj
        simp at keccak_inj
        rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Fin.val_eq_val] at keccak_inj
        rw [keccak_inj] at account_mem_balances
        exact (mem account_mem_balances)
        · exact Address.ofUInt256_lt_UInt256_size
        · exact Address.val_lt_UInt256_size

      -- address not in allowances
      · intro owner spender mem_allowances
        obtain ⟨erc_address, erc_intermediate, owner_lookup, spender_lookup, eq⟩ :=
          is_erc20.hasAllowance mem_allowances
        rw [get_evm_of_ok] at owner_lookup spender_lookup
        have spender_lookup_s := keccak_map_lookup_eq_of_Preserved_of_lookup Preserved spender_lookup
        push_neg
        use erc_intermediate
        rw [ ← keccak ]
        by_contra h
        rw [not_and'] at h
        apply h at owner_lookup
        exact owner_lookup

        rw [spender_lookup_s]
        by_contra h
        have : [↑↑spender, erc_intermediate] ∈ evmₛ.keccak_map.keys := by
          rw [Finmap.mem_keys]
          apply Finmap.lookup_isSome.mp
          have := Eq.trans (Eq.symm spender_lookup_s) spender_lookup
          rw [this]
          simp
        have IsEVMₛ : evmₛ.isEVMState := by aesop
        have keccak_inj := IsEVMₛ.1 this h
        simp at keccak_inj
        have intermediate_ne_balances : erc_intermediate ≠ ERC20Private.balances := by
          obtain blocked_range := get_evm_of_ok ▸ is_erc20.block_acc_range.2.1
          rw [owner_lookup] at blocked_range
          unfold not_mem_private at blocked_range
          simp at blocked_range
          rw [← Finset.forall_mem_not_eq] at blocked_range
          have bal_mem_private: ERC20Private.balances ∈ ERC20Private.toFinset := by
            unfold PrivateAddresses.toFinset
            simp
          specialize blocked_range ERC20Private.balances
          exact blocked_range bal_mem_private

        tauto

      -- address not in reserved space
      · obtain blocked_range := get_evm_of_ok ▸ s_erc20.block_acc_range.1
        rw [ keccak ] at blocked_range
        apply not_mem_private_of_some at blocked_range
        exact blocked_range
  · -- Hash collision from keccak
    rename_i hHashCollisionTrue
    right
    have :   Ok evm Inhabited.default⟦"var_account"↦var_account⟧⟦"_1"↦0⟧.evm.hash_collision
        = evm.hash_collision := by
      simp
    rw [this] at hHashCollision₁
    rcases s with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; skip]
    · unfold reviveJump at code
      simp at code
      rw [←code]
      aesop
    · unfold reviveJump at code
      simp at code

      rename_i j
      unfold evm at hHashCollisionTrue
      simp at hHashCollisionTrue

end

end Generated.erc20shim.ERC20Shim
