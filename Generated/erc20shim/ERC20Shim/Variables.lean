import Clear.UInt256

namespace Generated.erc20shim.ERC20Shim

structure PrivateAddresses where
    balances    : UInt256
    allowances  : UInt256
    totalSupply : UInt256
    name        : UInt256
    symbol      : UInt256

def ERC20Private : PrivateAddresses :=
  { balances := 0, allowances := 1, totalSupply := 2, name := 3, symbol := 4 }

end Generated.erc20shim.ERC20Shim
