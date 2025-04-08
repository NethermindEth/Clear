# How to generate `erc20shim.yul`

1. Clone https://github.com/OpenZeppelin/openzeppelin-contracts
2. Checkout `v5.0.2` in openzeppelin-contracts
3. Create a new file called `erc20shim.sol` in the `contracts/mocks/token` directory with the following:
```
pragma solidity ^0.8.20;

import {ERC20} from "contracts/token/ERC20/ERC20.sol";

contract ERC20Shim is ERC20 {
    constructor() ERC20("ERC20Shim", "E20S") {}
}
```
4. Install `solc-select` to be able to select specific `solc` versions. See: https://github.com/crytic/solc-select or https://search.nixos.org/packages?channel=unstable&show=solc-select
5. Run `solc-select install 0.8.21`
6. From the `contracts` directory, run:
```
SOLC_VERSION=0.8.21 solc --optimize --ir-optimized --yul-optimizations 'ho[esj]x[esVur]' contracts/mocks/token/erc20shim.sol > contracts/erc20shim.yul
```

You now have `erc20shim.yul` in the `contracts` directory.