import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun_allowance_gen

import Generated.erc20shim.ERC20Shim.Predicate

namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_fun_allowance (var : Identifier) (var_owner var_spender : Literal) (s₀ s₉ : State) : Prop :=
  ∀ {erc20}, IsERC20 erc20 s₀ →
  let owner := Address.ofUInt256 var_owner
  let spender := Address.ofUInt256 var_spender
  IsERC20 erc20 s₉ ∧ preservesEvm s₀ s₉ ∧
  s₉[var]!! = (erc20.allowances.lookup ⟨owner, spender⟩).getD 0

lemma fun_allowance_abs_of_concrete {s₀ s₉ : State} {var var_owner var_spender} :
  Spec (fun_allowance_concrete_of_code.1 var var_owner var_spender) s₀ s₉ →
  Spec (A_fun_allowance var var_owner var_spender) s₀ s₉ := by
  unfold fun_allowance_concrete_of_code A_fun_allowance

  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  intro hasFuel ⟨s, mapping, ⟨s', mapping', code⟩⟩ erc20 is_erc20

  clr_varstore

  -- what we can get right now from mapping function
  unfold A_mapping_index_access_mapping_address_mapping_address_uint256_of_address at mapping
  unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping
  clr_spec at mapping
  obtain ⟨preservesEvm, s_isOk, keccak⟩ := mapping
  obtain ⟨evmₛ, varstoreₛ, s_eq_ok⟩ := State_of_isOk s_isOk
  rw [ ← Variables.allowances_def
     , s_eq_ok, get_evm_of_ok, ← s_eq_ok
     ] at keccak

  -- what we can get right now from mapping' function
  unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping'
  clr_spec at mapping'
  obtain ⟨preservesEvm', s_isOk', keccak'⟩ := mapping'
  obtain ⟨evmₛ', varstoreₛ', s_eq_ok'⟩ := State_of_isOk s_isOk'
  rw [ s_eq_ok', get_evm_of_ok, ← s_eq_ok'
     ] at keccak'

  -- simplify contract
  unfold reviveJump at code
  simp [s_eq_ok, s_eq_ok'] at code
  rw [ ← State.insert_of_ok,  ← State.insert_of_ok, ← s_eq_ok' ] at code
  clr_varstore

  -- get underlying Preserved from preservesEvm
  rw [ s_eq_ok, preservesEvm_of_insert, preservesEvm_of_insert ] at preservesEvm
  have hPreserved := Preserved_of_preservesEvm_of_Ok preservesEvm

  -- get underlying Preserved from preservesEvm'
  rw [ s_eq_ok, s_eq_ok'] at preservesEvm'
  have hPreserved' := Preserved_of_preservesEvm_of_Ok preservesEvm'

  -- make use of transitivity of Preserved
  have hPreserved'' : Clear.Preserved evm evmₛ' := Preserved.trans hPreserved hPreserved'

  apply And.intro
  -- IsERC20 for the final state
  exact IsERC20_of_preservesEvm (by aesop) is_erc20

  rw [← code]
  apply And.intro
  -- preservesEvm s₀ s₉
  rw [ preservesEvm_of_insert' ]
  exact preservesEvm_of_preserved _ _ hPreserved''

  -- lookup allowance
  clr_varstore
  by_cases mem : ⟨Address.ofUInt256 var_owner, Address.ofUInt256 var_spender⟩ ∈ erc20.allowances
  · -- there is such ⟨owner, spender⟩ in allowances
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
        have : s["var_spender"]!! = var_spender := by sorry
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
      have keccak_inj := evmₛ'.keccak_inj this (Eq.symm h)

      --Up to here-ish

      rw [← Fin.ofNat''_eq_cast, ← Fin.ofNat''_eq_cast] at keccak_inj
      unfold Fin.ofNat'' at keccak_inj
      simp at keccak_inj
      obtain ⟨keccak_inj₁, keccak_inj₂⟩ := keccak_inj
      rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Fin.val_eq_val] at keccak_inj₁
      · rw [keccak_inj₁] at account_mem_balances
        exact (mem account_mem_balances)
      · exact Address.ofUInt256_lt_UInt256_size
      · exact Address.val_lt_UInt256_size

    -- address not in allowances
    · intro owner spender mem_allowances
      obtain ⟨erc_address, erc_intermediate, owner_lookup, spender_lookup, eq⟩ :=
        is_erc20.hasAllowance mem_allowances
      rw [get_evm_of_ok] at owner_lookup spender_lookup
      have spender_lookup_s := keccak_map_lookup_eq_of_Preserved_of_lookup hPreserved spender_lookup
      push_neg
      use erc_intermediate
      rw [ ← keccak' ]
      by_contra h
      rw [not_and'] at h
      apply h at owner_lookup
      exact owner_lookup

      rw [spender_lookup_s]
      by_contra h
      have : [spender, erc_intermediate] ∈ evmₛ.keccak_map.keys := by
        rw [Finmap.mem_keys]
        apply Finmap.lookup_isSome.mp
        have := Eq.trans (Eq.symm spender_lookup_s) spender_lookup
        rw [this]
        simp
      have keccak_inj := evmₛ.keccak_inj this h
      simp at keccak_inj
      have intermediate_ne_allowances : erc_intermediate ≠ ERC20Private.allowances := by
        obtain blocked_range := get_evm_of_ok ▸ is_erc20.block_acc_range.2
        rw [owner_lookup] at blocked_range
        unfold not_mem_private at blocked_range
        simp at blocked_range
        rw [← Finset.forall_mem_not_eq] at blocked_range
        have bal_mem_private: ERC20Private.allowances ∈ ERC20Private.toFinset := by
          unfold PrivateAddresses.toFinset
          simp
        specialize blocked_range ERC20Private.allowances
        exact blocked_range bal_mem_private

      tauto

    -- address not in reserved space
    · obtain blocked_range := get_evm_of_ok ▸ s_erc20.block_acc_range.1
      rw [ keccak ] at blocked_range
      apply not_mem_private_of_some at blocked_range
      exact blocked_range

end

end Generated.erc20shim.ERC20Shim
