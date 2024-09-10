import Mathlib.Data.Finmap

import Clear.State

import Generated.erc20shim.ERC20Shim.Variables

open Clear

namespace Generated.erc20shim.ERC20Shim

abbrev BalanceMap := Finmap (λ _ : Address ↦ UInt256)
abbrev AllowanceMap := Finmap (λ _ : Address × Address ↦ UInt256)

structure ERC20 where
  supply : UInt256
  balances : BalanceMap
  allowances : AllowanceMap

-- structure HasBalance (balances : BalanceMap) (account : Address) (s : State) where
--   address : Address
--   keccak : s.evm.keccak_map.lookup [ ↑account , ERC20Private.balances ] = some address
--   balance : some (s.evm.sload address) = balances.lookup account

abbrev HasBalance (balances : BalanceMap) (account : Address) (s : State) :=
  ∃ address,
  s.evm.keccak_map.lookup [ ↑account , ERC20Private.balances ] = some address ∧
  some (s.evm.sload address) = balances.lookup account

namespace HasBalance

variable {balances : BalanceMap} {account : Address} {s : State}

-- theorem keccak (address(h : HasBalance balances account s) :
--   ∃ address, s.evm.keccak_map.lookup [ ↑account , ERC20Private.balances ] = some address := 
--   let ⟨addr, keccak, _⟩ := h
--   ⟨addr, keccak⟩

-- theorem balance (h : HasBalance balances account s) :
--   ∃ address, some (s.evm.sload address) = balances.lookup account :=
--   let ⟨addr, _, balance⟩ := h
--   ⟨addr, balance⟩

end HasBalance

-- structure HasAllowance (allowances : AllowanceMap) (owner : Address) (spender : Address) (s : State) where
--   address : Address
--   keccak : s.evm.keccak_map.lookup [ ↑owner, ↑spender, ERC20Private.allowances ] = some address
--   allowance : some (s.evm.sload address) = allowances.lookup ⟨owner, spender⟩

def HasAllowance (allowances : AllowanceMap) (owner : Address) (spender : Address) (s : State) : Prop :=
  ∃ address,
  s.evm.keccak_map.lookup [ ↑owner, ↑spender, ERC20Private.allowances ] = some address ∧
  some (s.evm.sload address) = allowances.lookup ⟨owner, spender⟩

-- def balance_predicate (erc20 : ERC20) (s : State) : Prop :=
--   ∀ account,
--   account ∈ erc20.balances → HasBalance erc20.balances account s

-- def balance_predicate (erc20 : ERC20) (s : State) : ? :=
--   ∀ account,
--   account ∈ erc20.balances → HasBalance erc20.balances account s

def allowance_predicate (erc20 : ERC20) (s : State) : Prop :=
  ∀ (owner spender : Address),
  ⟨owner, spender⟩ ∈ erc20.allowances → HasAllowance erc20.allowances owner spender s

end Generated.erc20shim.ERC20Shim
