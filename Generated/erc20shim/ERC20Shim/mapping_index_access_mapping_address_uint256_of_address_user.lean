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
  s₉ = s₀ ⟦ dataSlot ↦ address ⟧

  -- account ∈ erc20.balances →
  -- ∃ address, s₀.evm.keccak_map.lookup [ ↑account,  ERC20Private.balances ] = some address →
  -- s₉ = s₀ ⟦ dataSlot ↦ address ⟧

  -- let s₁ := s₀ 🇪⟦ s₀.evm.mstore 0x00 (Address.ofUInt256 key) ⟧
  -- let s₂ := s₁ 🇪⟦ s₁.evm.mstore 0x20 slot ⟧
  -- match s₂.evm.keccak256 0x00 0x40 with
  -- | some ⟨addr, evm⟩ => s₉ = s₂ 🇪⟦ evm ⟧⟦ dataSlot ↦ addr ⟧
  -- | none => s₉ = s₂ 🇪⟦ s₂.evm.addHashCollision ⟧

-- lemma mapping_of_ok {dataSlot : Identifier} {slot key : Literal} {s₀ s₉ : State}
--   : A_mapping_index_access_mapping_address_uint256_of_address dataSlot slot key s₀ s₉ →
--     isOk s₀ → isOk s₉ := by
--   intro mapping s₀_ok
--   unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping

--   have : s₀🇪⟦mstore s₀.evm 0 ↑↑(Address.ofUInt256 key)⟧.isOk := by
--     rw [isOk_setEvm]
--     assumption

--   simp at mapping
--   rw [ evm_get_set_of_isOk s₀_ok
--      , evm_get_set_of_isOk this
--      ] at mapping

--   -- split at mapping
--   -- <;> apply_fun isOk at mapping
--   -- <;> try rw [ isOk_insert ] at mapping
--   -- <;> [simp only [ isOk_setEvm ] at mapping; simp only [ isOk_setEvm ] at mapping]
--   -- <;> exact mapping.to_iff.mpr s₀_ok

--   split at mapping <;> apply_fun isOk at mapping
--   · rw [ isOk_insert ] at mapping
--     rw [ isOk_setEvm, isOk_setEvm, isOk_setEvm] at mapping
--     exact mapping.to_iff.mpr s₀_ok
--   · rw [ isOk_setEvm, isOk_setEvm, isOk_setEvm] at mapping
--     exact mapping.to_iff.mpr s₀_ok

-- lemma lookup_addr_fail {dataSlot : Identifier} {slot key : Literal} {s₀ s₉ : State}
--   : A_mapping_index_access_mapping_address_uint256_of_address dataSlot slot key s₀ s₉ →
--     s₉.evm.hash_collision = true →
--     s₉[dataSlot]!! = 0 := by
--   intro r_addr h
--   rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]

--   clr_funargs

--   unfold A_mapping_index_access_mapping_address_uint256_of_address at r_addr
--   simp at r_addr

--   sorry

-- lemma lookup_addr_ok {dataSlot : Identifier} {slot key : Literal} {s₀ s₉ : State}
--   : A_mapping_index_access_mapping_address_uint256_of_address dataSlot slot key s₀ s₉ →
--     s₉.evm.hash_collision = false →
--     ∃ addr, s₉[dataSlot]!! = addr := by
--   intro r_addr
--   sorry

  -- unfold A_mapping_index_access_mapping_address_uint256_of_address at r_addr
  -- simp at r_addr


  -- unfold setEvm at r_addr
  -- simp at r_addr
  -- generalize prep_def
  --   : (mstore s₀.evm 0 ↑↑(Address.ofUInt256 key)).mstore 32 slot = state_prep
  --   at r_addr

  -- cases (b.evm.keccak256 0x00 0x40) with
  -- | none =>

  --   use 0
  --   sorry
  -- | some a => sorry

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

  rcases (Finmap.mem_iff.mp account_mem_balances) with ⟨bal, h_bal⟩

  -- use address
  -- intro h_lookup
  generalize prep_def : (mstore evm 0 ↑↑account).mstore 32 slot = state_prep

  have : Option.isSome $ state_prep.keccak256 0 64 := by
    unfold keccak256
    rw [← prep_def, interval'_eq_interval 2 two_ne_zero (by norm_cast)]


    rw [ mstore_mstore_of_ne, interval_of_mstore_eq_val_cons
       , mstore_mstore_of_ne, zero_add, interval_of_mstore_eq_val_cons
       , interval_of_0_eq_nil
       ]
    unfold_let
    rw [mstore_preserves_keccak_map, mstore_preserves_keccak_map]
    rw [hasAddress]


  sorry
-- mkInterval (mstore evm x v) x = v :: (mkInterval evm (x + 32))
  -- mkInterval evm n n = []
  --   rw [ ← prep_def ]
  --   unfold mstore updateMemory
  --   sorry

  -- cases this
  -- · simp
  --   sorry
  -- · simp
  --   unfold setEvm State.insert
  --   aesop_spec

end

end Generated.erc20shim.ERC20Shim
