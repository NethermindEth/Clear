import Mathlib.Data.Finmap

import Clear.State
import Clear.Utilities

import Generated.erc20shim.ERC20Shim.Variables

open Clear State Utilities

namespace Generated.erc20shim.ERC20Shim

abbrev BalanceMap := Finmap (λ _ : Address ↦ UInt256)
abbrev AllowanceMap := Finmap (λ _ : Address × Address ↦ UInt256)

structure ERC20 where
  supply : UInt256
  balances : BalanceMap
  allowances : AllowanceMap

def acc (a : Option UInt256) : Prop :=
  match a with
  | some el => el ∉ ERC20Private.toFinset
  | none => true

structure IsERC20 (erc20 : ERC20) (s : State) : Prop where
  hasSupply : s.evm.sload ERC20Private.totalSupply = erc20.supply

  hasBalance :
    ∀ {account}, (account ∈ erc20.balances) →
    ∃ (address : UInt256),
    s.evm.keccak_map.lookup [ ↑account , ERC20Private.balances ] = some address ∧
    erc20.balances.lookup account = some (s.evm.sload address)

  hasAllowance :
    ∀ {owner spender}, (⟨owner, spender⟩ ∈ erc20.allowances) →
    ∃ (address  : UInt256) (intermediate : UInt256),
    s.evm.keccak_map.lookup [ ↑owner , ERC20Private.allowances ] = some intermediate →
    s.evm.keccak_map.lookup [ ↑spender , intermediate ] = some address →
    erc20.allowances.lookup ⟨owner, spender⟩ = some (s.evm.sload address)

  -- mem : account ∉ erc20.balances
  storageDom :
    s.evm.storage.keys =
      { address | ∃ account,
        account ∈ erc20.balances ∧
        some address = s.evm.keccak_map.lookup [ ↑account, ERC20Private.balances ] } ∪
      { address | ∃ owner spender,
        ⟨owner, spender⟩ ∈ erc20.allowances ∧
        ∃ intermediate, s.evm.keccak_map.lookup [ ↑owner , ERC20Private.allowances ] = some intermediate ∧
        s.evm.keccak_map.lookup [ ↑spender , intermediate ] = some address } ∪
      ERC20Private.toFinset

  block_acc_range :
    ∀ {account}, acc (s.evm.keccak_map.lookup [ ↑account, ERC20Private.balances ])

  -- block_allowance_range :
  --   ∀ {owner}, s.evm.keccak_map.lookup [ ↑owner, ERC20Private.allowances ] ∉ ERC20Private.toFinset

    -- equivalent statements
    -- s.evm.sload address ∈ erc20.balances.lookup account
    -- ⟨account, s.evm.sload address⟩ ∈ erc20.balances.entries

lemma IsERC20_of_insert {erc20} {s : State} :
  ∀ {var val}, IsERC20 erc20 s → IsERC20 erc20 (s⟦var↦val⟧) := by
  intro var val is_erc
  constructor <;> rw [State.evm_insert]
  · exact is_erc.hasSupply
  · exact is_erc.hasBalance
  · exact is_erc.hasAllowance
  · exact is_erc.storageDom

lemma IsERC20_of_ok_forall_store {erc20} {evm} {s₀ s₁} :
  IsERC20 erc20 (Ok evm s₀) → IsERC20 erc20 (Ok evm s₁) := by
  intro is_erc
  constructor <;> (rw [State.evm]; simp)
  · exact is_erc.hasSupply
  · exact is_erc.hasBalance
  · exact is_erc.hasAllowance
  · have := get_evm_of_ok ▸ is_erc.storageDom
    exact this

lemma IsERC20_of_ok_of_Preserved {erc20} {store} {σ₀ σ₁} (h : Preserved σ₀ σ₁) : 
  IsERC20 erc20 (Ok σ₀ store) → IsERC20 erc20 (Ok σ₁ store) := by
  sorry
  
lemma IsERC20_of_preservesEvm {erc20} {s₀ s₁} :
  preservesEvm s₀ s₁ → IsERC20 erc20 s₀ → IsERC20 erc20 s₁ := by
  sorry

lemma sload_of_IsERC20_outside {erc20} {s} (h : IsERC20 erc20 s) :
  ∀ {addr}, addr ∉ s.evm.storage.keys → s.evm.sload addr = 0 := by
  sorry

lemma t {erc20} {s₀ s₁} (is_erc20 : IsERC20 erc20 s₀) (h : preservesEvm s₀ s₁) :
  ∀ {addr}, addr ∉ s₀.evm.keccak_range ∧ addr ∈ s₁.evm.keccak_range →
  addr ∉ s₀.evm.storage.keys := by
  sorry

end Generated.erc20shim.ERC20Shim
