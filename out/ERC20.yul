/// @use-src 0:"ERC20.sol"
object "GetCode_17" {
    code { }
    /// @use-src 0:"ERC20.sol"
    object "GetCode_17_deployed" {
        code {
            /// @ast-id 16 @src 0:84:446  "function transfer(uint ammount, uint acc1, uint acc2) public pure returns (uint acc1out, uint acc2out) {..."
            function fun_transfer(var_ammount, var_acc1, var_acc2) -> var_acc1out, var_acc2out
            {
                /// @src 0:159:171  "uint acc1out"
                var_acc1out := /** @src 0:62:448  "library GetCode {..." */ 0
                /// @src 0:173:185  "uint acc2out"
                var_acc2out := /** @src 0:62:448  "library GetCode {..." */ 0
                /// @src 0:197:440  "assembly {..."
                let usr := lt(var_ammount, var_acc1)
                if eq(0, usr)
                {
                    var_acc1out := sub(var_acc1, var_ammount)
                    var_acc2out := add(var_acc2, var_ammount)
                }
            }
        }
        data ".metadata" hex"a2646970667358221220cc4bbf9d1c6fc5e759b3a0a355fafebc78c81062212738f212ad2922d71d0f9c64736f6c63430008130033"
    }
}

