import Mathlib.Data.Finmap
import Clear.Ast
import Clear.EVMState
import Clear.UInt256
import Clear.State

open Clear

namespace Generated.erc20shim.ERC20Shim

structure PrivateAddresses where
    balances    : UInt256
    allowances  : UInt256
    totalSupply : UInt256
    name        : UInt256
    symbol      : UInt256

def ERC20Private : PrivateAddresses :=
  { balances := 0, allowances := 1, totalSupply := 2, name := 3, symbol := 4 }


def ERC20Pred (balances : Finmap (λ (_ : Address) ↦ UInt256)) (s : State) : Prop :=
  ∀ account, account ∈ balances →
  ∃ addr, s.evm.keccak_map.lookup [ ↑account , ERC20Private.balances ] = some addr ∧
  some (s.evm.sload addr) = balances.lookup account

end Generated.erc20shim.ERC20Shim
