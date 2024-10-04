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

namespace Variables

lemma balances_def : ERC20Private.balances = 0 := by
  unfold ERC20Private
  simp only

lemma allowances_def : ERC20Private.allowances = 1 := by
  unfold ERC20Private
  simp only

lemma totalSupply_def : ERC20Private.totalSupply = 2 := by
  unfold ERC20Private
  simp only

lemma name_def : ERC20Private.name = 3 := by
  unfold ERC20Private
  simp only

lemma symbol_def : ERC20Private.symbol = 4 := by
  unfold ERC20Private
  simp only

end Variables

end Generated.erc20shim.ERC20Shim
