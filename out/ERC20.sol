// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.19;

library GetCode {
    function transfer(uint ammount, uint acc1, uint acc2) public pure returns (uint acc1out, uint acc2out) {
        assembly {
            let _1 := lt(ammount,acc1)
            switch _1
            case 0 {
                acc1out := sub(acc1, ammount)
                acc2out := add(acc2, ammount)
            }
            case 1 {
            }
        }
    }
}