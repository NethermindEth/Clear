Optimized IR:

Optimized IR:

Optimized IR:

Optimized IR:
/// @use-src 0:"contracts/interfaces/draft-IERC6093.sol", 1:"contracts/mocks/token/erc20shim.sol", 2:"contracts/token/ERC20/ERC20.sol", 3:"contracts/token/ERC20/IERC20.sol", 4:"contracts/token/ERC20/extensions/IERC20Metadata.sol", 5:"contracts/utils/Context.sol"
object "ERC20Shim_20" {
    code {
        {
            /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
            let _1 := memoryguard(0x80)
            let _2 := 64
            mstore(_2, _1)
            let _3 := callvalue()
            if _3
            {
                revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            }
            constructor_ERC20Shim()
            let _4 := _2
            let _5 := mload(_2)
            let _6 := datasize("ERC20Shim_20_deployed")
            let _7 := dataoffset("ERC20Shim_20_deployed")
            codecopy(_5, _7, _6)
            let _8 := _6
            return(_5, _6)
        }
        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
        {
            let _1 := 0
            let _2 := _1
            revert(_1, _1)
        }
        function panic_error_0x41()
        {
            let _1 := shl(224, 0x4e487b71)
            let _2 := 0
            mstore(_2, _1)
            let _3 := 0x41
            let _4 := 4
            mstore(_4, _3)
            let _5 := 0x24
            let _6 := _2
            revert(_2, _5)
        }
        function finalize_allocation(memPtr, size)
        {
            let _1 := not(31)
            let _2 := 31
            let _3 := add(size, _2)
            let _4 := and(_3, _1)
            let newFreePtr := add(memPtr, _4)
            let _5 := lt(newFreePtr, memPtr)
            let _6 := sub(shl(64, 1), 1)
            let _7 := gt(newFreePtr, _6)
            let _8 := or(_7, _5)
            if _8 { panic_error_0x41() }
            let _9 := 64
            mstore(_9, newFreePtr)
        }
        function allocate_memory(size) -> memPtr
        {
            let _1 := 64
            memPtr := mload(_1)
            finalize_allocation(memPtr, size)
        }
        function array_allocation_size_string(length) -> size
        {
            let _1 := sub(shl(64, 1), 1)
            let _2 := gt(length, _1)
            if _2 { panic_error_0x41() }
            let _3 := not(31)
            let _4 := 31
            let _5 := add(length, _4)
            size := and(_5, _3)
            let _6 := 0x20
            size := add(size, _6)
        }
        function allocate_memory_array_string(length) -> memPtr
        {
            let _1 := array_allocation_size_string(length)
            memPtr := allocate_memory(_1)
            mstore(memPtr, length)
        }
        function store_literal_in_memory_73d84741e39ae21500f019e1bd49b1509c4dad0285f14920732b98003dc4a297(memPtr)
        {
            let _1 := "ERC20Shim"
            mstore(memPtr, _1)
        }
        function copy_literal_to_memory_73d84741e39ae21500f019e1bd49b1509c4dad0285f14920732b98003dc4a297() -> memPtr
        {
            let _1 := 9
            memPtr := allocate_memory_array_string(_1)
            let _2 := 32
            let _3 := add(memPtr, _2)
            store_literal_in_memory_73d84741e39ae21500f019e1bd49b1509c4dad0285f14920732b98003dc4a297(_3)
        }
        function store_literal_in_memory_654a20c509642b4486f3c0baf150dce7367ca9e5f6186c81edaf3f66a3f7c7a3(memPtr)
        {
            let _1 := "E20S"
            mstore(memPtr, _1)
        }
        function copy_literal_to_memory_654a20c509642b4486f3c0baf150dce7367ca9e5f6186c81edaf3f66a3f7c7a3() -> memPtr
        {
            let _1 := 4
            memPtr := allocate_memory_array_string(_1)
            let _2 := 32
            let _3 := add(memPtr, _2)
            store_literal_in_memory_654a20c509642b4486f3c0baf150dce7367ca9e5f6186c81edaf3f66a3f7c7a3(_3)
        }
        /// @ast-id 19 @src 1:116:195  "constructor() ERC20(\"ERC20Shim\", \"E20S\") {..."
        function constructor_ERC20Shim()
        {
            /// @src 1:136:147  "\"ERC20Shim\""
            let _mpos := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ copy_literal_to_memory_73d84741e39ae21500f019e1bd49b1509c4dad0285f14920732b98003dc4a297()
            let _1 := copy_literal_to_memory_654a20c509642b4486f3c0baf150dce7367ca9e5f6186c81edaf3f66a3f7c7a3()
            /// @src 1:116:195  "constructor() ERC20(\"ERC20Shim\", \"E20S\") {..."
            constructor_ERC20(_mpos, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _1)
            /// @src 1:183:187  "1000"
            let _2 := 0x03e8
            /// @src 1:171:181  "msg.sender"
            let _3 := caller()
            /// @src 1:165:188  "_mint(msg.sender, 1000)"
            fun_mint(/** @src 1:171:181  "msg.sender" */ _3, /** @src 1:183:187  "1000" */ _2)
        }
        /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
        function panic_error_0x22()
        {
            let _1 := shl(224, 0x4e487b71)
            let _2 := 0
            mstore(_2, _1)
            let _3 := 0x22
            let _4 := 4
            mstore(_4, _3)
            let _5 := 0x24
            let _6 := _2
            revert(_2, _5)
        }
        function extract_byte_array_length(data) -> length
        {
            let _1 := 1
            length := shr(_1, data)
            let _2 := _1
            let outOfPlaceEncoding := and(data, _1)
            let _3 := iszero(outOfPlaceEncoding)
            if _3
            {
                let _4 := 0x7f
                length := and(length, _4)
            }
            let _5 := 32
            let _6 := lt(length, _5)
            let _7 := eq(outOfPlaceEncoding, _6)
            if _7 { panic_error_0x22() }
        }
        function array_dataslot_string_storage(ptr) -> data
        {
            let _1 := 0
            mstore(_1, ptr)
            let _2 := 0x20
            let _3 := _1
            data := keccak256(_1, _2)
        }
        function update_byte_slice_dynamic32(value, shiftBytes, toInsert) -> result
        {
            let _1 := 3
            let shiftBits := shl(_1, shiftBytes)
            let _2 := not(0)
            let mask := shl(shiftBits, _2)
            toInsert := shl(shiftBits, toInsert)
            let _3 := not(mask)
            value := and(value, _3)
            let _4 := and(toInsert, mask)
            result := or(value, _4)
        }
        function update_storage_value_uint256_to_uint256(slot, offset, value)
        {
            let _1 := sload(slot)
            let _2 := update_byte_slice_dynamic32(_1, offset, value)
            sstore(slot, _2)
        }
        function storage_set_to_zero_uint256(slot, offset)
        {
            let _1 := 0
            update_storage_value_uint256_to_uint256(slot, offset, _1)
        }
        function clear_storage_range_bytes1(start, end)
        {
            for { }
            lt(start, end)
            {
                let _1 := 1
                start := add(start, _1)
            }
            {
                let _2 := 0
                storage_set_to_zero_uint256(start, _2)
            }
        }
        function clean_up_bytearray_end_slots_string_storage(array, len, startIndex)
        {
            let _1 := 31
            let _2 := gt(len, _1)
            if _2
            {
                let dataArea := array_dataslot_string_storage(array)
                let _3 := _1
                let _4 := add(startIndex, _1)
                let _5 := shr(5, _4)
                let deleteStart := add(dataArea, _5)
                let _6 := 32
                let _7 := lt(startIndex, _6)
                if _7 { deleteStart := dataArea }
                let _8 := _1
                let _9 := add(len, _1)
                let _10 := shr(5, _9)
                let _11 := add(dataArea, _10)
                clear_storage_range_bytes1(deleteStart, _11)
            }
        }
        function extract_used_part_and_set_length_of_short_byte_array(data, len) -> used
        {
            let _1 := not(0)
            let _2 := 3
            let _3 := shl(_2, len)
            let _4 := shr(_3, _1)
            let _5 := not(_4)
            data := and(data, _5)
            let _6 := 1
            let _7 := shl(_6, len)
            used := or(data, _7)
        }
        function copy_byte_array_to_storage_from_string_to_string(slot, src)
        {
            let newLen := mload(src)
            let _1 := sub(shl(64, 1), 1)
            let _2 := gt(newLen, _1)
            if _2 { panic_error_0x41() }
            let _3 := sload(slot)
            let _4 := extract_byte_array_length(_3)
            clean_up_bytearray_end_slots_string_storage(slot, _4, newLen)
            let srcOffset := 0
            srcOffset := 0x20
            let _5 := 31
            let _6 := gt(newLen, _5)
            switch _6
            case 1 {
                let _7 := not(31)
                let loopEnd := and(newLen, _7)
                let dstPtr := array_dataslot_string_storage(slot)
                let i := 0
                for { }
                lt(i, loopEnd)
                {
                    let _8 := 0x20
                    i := add(i, _8)
                }
                {
                    let _9 := add(src, srcOffset)
                    let _10 := mload(_9)
                    sstore(dstPtr, _10)
                    let _11 := 1
                    dstPtr := add(dstPtr, _11)
                    let _12 := 32
                    srcOffset := add(srcOffset, _12)
                }
                let _13 := lt(loopEnd, newLen)
                if _13
                {
                    let _14 := add(src, srcOffset)
                    let lastValue := mload(_14)
                    let _15 := not(0)
                    let _16 := and(shl(3, newLen), 248)
                    let _17 := shr(_16, _15)
                    let _18 := not(_17)
                    let _19 := and(lastValue, _18)
                    sstore(dstPtr, _19)
                }
                let _20 := 1
                let _21 := _20
                let _22 := shl(_20, newLen)
                let _23 := add(_22, _20)
                sstore(slot, _23)
            }
            default {
                let value := 0
                if newLen
                {
                    let _24 := add(src, srcOffset)
                    value := mload(_24)
                }
                let _25 := extract_used_part_and_set_length_of_short_byte_array(value, newLen)
                sstore(slot, _25)
            }
        }
        function update_storage_value_offsett_string_to_string(slot, value)
        {
            copy_byte_array_to_storage_from_string_to_string(slot, value)
        }
        /// @ast-id 72 @src 2:1896:2009  "constructor(string memory name_, string memory symbol_) {..."
        function constructor_ERC20(var_name_mpos, var_symbol_mpos)
        {
            /// @src 2:1962:1975  "_name = name_"
            let _1 := 0x03
            update_storage_value_offsett_string_to_string(_1, /** @src 2:1970:1975  "name_" */ var_name_mpos)
            /// @src 2:1985:2002  "_symbol = symbol_"
            let _2 := 0x04
            update_storage_value_offsett_string_to_string(_2, /** @src 2:1995:2002  "symbol_" */ var_symbol_mpos)
        }
        /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
        function abi_encode_address(value, pos)
        {
            let _1 := sub(shl(160, 1), 1)
            let _2 := and(value, _1)
            mstore(pos, _2)
        }
        function abi_encode_tuple_address(headStart, value0) -> tail
        {
            let _1 := 32
            tail := add(headStart, _1)
            abi_encode_address(value0, headStart)
        }
        /// @ast-id 375 @src 2:7721:7929  "function _mint(address account, uint256 value) internal {..."
        function fun_mint(var_account, var_value)
        {
            /// @src 2:7791:7798  "account"
            let expr := var_account
            /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
            let _1 := sub(shl(160, 1), 1)
            let _2 := and(/** @src 2:7791:7812  "account == address(0)" */ var_account, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _1)
            /// @src 2:7791:7812  "account == address(0)"
            let _3 := iszero(/** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _2)
            /// @src 2:7787:7878  "if (account == address(0)) {..."
            if /** @src 2:7791:7812  "account == address(0)" */ _3
            /// @src 2:7787:7878  "if (account == address(0)) {..."
            {
                /// @src 2:7856:7866  "address(0)"
                let expr_1 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ 0
                let _4 := 64
                /// @src 2:7835:7867  "ERC20InvalidReceiver(address(0))"
                let _5 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ mload(_4)
                /// @src 2:7835:7867  "ERC20InvalidReceiver(address(0))"
                let _6 := shl(224, 0xec442f05)
                mstore(_5, _6)
                let _7 := 4
                let _8 := add(_5, _7)
                let _9 := abi_encode_tuple_address(_8, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ expr_1)
                /// @src 2:7835:7867  "ERC20InvalidReceiver(address(0))"
                let _10 := sub(_9, _5)
                revert(_5, _10)
            }
            /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
            let _11 := 0
            /// @src 2:7916:7921  "value"
            fun_update(/** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _11, /** @src 2:7907:7914  "account" */ var_account, /** @src 2:7916:7921  "value" */ var_value)
        }
        /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
        function mapping_index_access_mapping_address_uint256_of_address(slot, key) -> dataSlot
        {
            let _1 := and(key, sub(shl(160, 1), 1))
            let _2 := 0
            mstore(_2, _1)
            let _3 := 0x20
            mstore(_3, slot)
            let _4 := 0x40
            let _5 := _2
            dataSlot := keccak256(_2, _4)
        }
        function abi_encode_uint256_to_uint256(value, pos)
        { mstore(pos, value) }
        function abi_encode_address_uint256_uint256(headStart, value0, value1, value2) -> tail
        {
            let _1 := 96
            tail := add(headStart, _1)
            abi_encode_address(value0, headStart)
            let _2 := 32
            let _3 := add(headStart, _2)
            abi_encode_uint256_to_uint256(value1, _3)
            let _4 := 64
            let _5 := add(headStart, _4)
            abi_encode_uint256_to_uint256(value2, _5)
        }
        function update_byte_slice_shift(value, toInsert) -> result
        {
            toInsert := toInsert
            result := toInsert
        }
        function update_storage_value_offsett_uint256_to_uint256(slot, value)
        {
            let _1 := sload(slot)
            let _2 := update_byte_slice_shift(_1, value)
            sstore(slot, _2)
        }
        function panic_error_0x11()
        {
            let _1 := shl(224, 0x4e487b71)
            let _2 := 0
            mstore(_2, _1)
            let _3 := 0x11
            let _4 := 4
            mstore(_4, _3)
            let _5 := 0x24
            let _6 := _2
            revert(_2, _5)
        }
        function checked_add_uint256(x, y) -> sum
        {
            x := x
            y := y
            sum := add(x, y)
            let _1 := gt(x, sum)
            if _1 { panic_error_0x11() }
        }
        function abi_encode_uint256(headStart, value0) -> tail
        {
            let _1 := 32
            tail := add(headStart, _1)
            abi_encode_uint256_to_uint256(value0, headStart)
        }
        /// @ast-id 342 @src 2:6271:7378  "function _update(address from, address to, uint256 value) internal virtual {..."
        function fun_update(var_from, var_to, var_value)
        {
            /// @src 2:6360:6364  "from"
            let expr := var_from
            /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
            let _1 := sub(shl(160, 1), 1)
            let _2 := and(/** @src 2:6360:6378  "from == address(0)" */ var_from, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _1)
            /// @src 2:6360:6378  "from == address(0)"
            let _3 := iszero(/** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _2)
            /// @src 2:6356:6896  "if (from == address(0)) {..."
            switch /** @src 2:6360:6378  "from == address(0)" */ _3
            case /** @src 2:6356:6896  "if (from == address(0)) {..." */ 0 {
                /// @src 2:6570:6579  "_balances"
                let _4 := 0x00
                /// @src 2:6570:6585  "_balances[from]"
                let _5 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:6570:6579  "_balances" */ _4, /** @src 2:6580:6584  "from" */ var_from)
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _6 := sload(/** @src 2:6570:6585  "_balances[from]" */ _5)
                /// @src 2:6548:6585  "uint256 fromBalance = _balances[from]"
                let var_fromBalance := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _6
                /// @src 2:6603:6622  "fromBalance < value"
                let _7 := lt(/** @src 2:6603:6614  "fromBalance" */ _6, /** @src 2:6617:6622  "value" */ var_value)
                /// @src 2:6599:6714  "if (fromBalance < value) {..."
                if /** @src 2:6603:6622  "fromBalance < value" */ _7
                /// @src 2:6599:6714  "if (fromBalance < value) {..."
                {
                    /// @src 2:6674:6678  "from"
                    let expr_1 := var_from
                    /// @src 2:6680:6691  "fromBalance"
                    let expr_2 := _6
                    /// @src 2:6693:6698  "value"
                    let expr_3 := var_value
                    /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                    let _8 := 64
                    /// @src 2:6649:6699  "ERC20InsufficientBalance(from, fromBalance, value)"
                    let _9 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ mload(_8)
                    /// @src 2:6649:6699  "ERC20InsufficientBalance(from, fromBalance, value)"
                    let _10 := shl(226, 0x391434e3)
                    mstore(_9, _10)
                    let _11 := 4
                    let _12 := add(_9, _11)
                    let _13 := abi_encode_address_uint256_uint256(_12, var_from, _6, var_value)
                    let _14 := sub(_13, _9)
                    revert(_9, _14)
                }
                /// @src 2:6852:6871  "fromBalance - value"
                let expr_4 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ sub(/** @src 2:6852:6863  "fromBalance" */ _6, /** @src 2:6866:6871  "value" */ var_value)
                /// @src 2:6834:6843  "_balances"
                let _15 := _4
                /// @src 2:6834:6849  "_balances[from]"
                let _16 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:6834:6843  "_balances" */ _4, /** @src 2:6844:6848  "from" */ var_from)
                /// @src 2:6834:6871  "_balances[from] = fromBalance - value"
                update_storage_value_offsett_uint256_to_uint256(/** @src 2:6834:6849  "_balances[from]" */ _16, /** @src 2:6834:6871  "_balances[from] = fromBalance - value" */ expr_4)
            }
            default /// @src 2:6356:6896  "if (from == address(0)) {..."
            {
                /// @src 2:6496:6517  "_totalSupply += value"
                let _17 := 0x02
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _18 := sload(/** @src 2:6496:6517  "_totalSupply += value" */ _17)
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _19 := _18
                /// @src 2:6496:6517  "_totalSupply += value"
                let _20 := checked_add_uint256(/** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _18, /** @src 2:6512:6517  "value" */ var_value)
                /// @src 2:6496:6517  "_totalSupply += value"
                let _21 := _17
                update_storage_value_offsett_uint256_to_uint256(_17, _20)
            }
            /// @src 2:6910:6912  "to"
            let expr_5 := var_to
            /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
            let _22 := _1
            let _23 := and(/** @src 2:6910:6926  "to == address(0)" */ var_to, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _1)
            /// @src 2:6910:6926  "to == address(0)"
            let _24 := iszero(/** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _23)
            /// @src 2:6906:7331  "if (to == address(0)) {..."
            switch /** @src 2:6910:6926  "to == address(0)" */ _24
            case /** @src 2:6906:7331  "if (to == address(0)) {..." */ 0 {
                /// @src 2:7301:7306  "value"
                let expr_6 := var_value
                /// @src 2:7284:7293  "_balances"
                let _25 := 0x00
                /// @src 2:7284:7297  "_balances[to]"
                let _26 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:7284:7293  "_balances" */ _25, /** @src 2:7294:7296  "to" */ var_to)
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _27 := sload(/** @src 2:7284:7306  "_balances[to] += value" */ _26)
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _28 := _27
                let _29 := add(_27, /** @src 2:7284:7306  "_balances[to] += value" */ var_value)
                update_storage_value_offsett_uint256_to_uint256(_26, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _29)
            }
            default /// @src 2:6906:7331  "if (to == address(0)) {..."
            {
                /// @src 2:7073:7094  "_totalSupply -= value"
                let _30 := 0x02
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _31 := sload(/** @src 2:7073:7094  "_totalSupply -= value" */ _30)
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _32 := _31
                let _33 := sub(_31, /** @src 2:7089:7094  "value" */ var_value)
                /// @src 2:7073:7094  "_totalSupply -= value"
                let _34 := _30
                update_storage_value_offsett_uint256_to_uint256(_30, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _33)
            }
            /// @src 2:7355:7359  "from"
            let expr_7 := var_from
            /// @src 2:7361:7363  "to"
            let expr_8 := var_to
            /// @src 2:7365:7370  "value"
            let expr_9 := var_value
            /// @src 2:7346:7371  "Transfer(from, to, value)"
            let _35 := 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef
            let _36 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _2
            /// @src 2:7346:7371  "Transfer(from, to, value)"
            let _37 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _23
            let _38 := 64
            /// @src 2:7346:7371  "Transfer(from, to, value)"
            let _39 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ mload(_38)
            /// @src 2:7346:7371  "Transfer(from, to, value)"
            let _40 := abi_encode_uint256(_39, var_value)
            let _41 := sub(_40, _39)
            log3(_39, _41, _35, _2, _23)
        }
    }
    /// @use-src 1:"contracts/mocks/token/erc20shim.sol", 2:"contracts/token/ERC20/ERC20.sol", 5:"contracts/utils/Context.sol"
    object "ERC20Shim_20_deployed" {
        code {
            {
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _1 := memoryguard(0x80)
                let _2 := 64
                mstore(_2, _1)
                let _3 := 4
                let _4 := calldatasize()
                let _5 := lt(_4, _3)
                let _6 := iszero(_5)
                if _6
                {
                    let _7 := 0
                    let _8 := calldataload(_7)
                    let _9 := 224
                    let _10 := shr(_9, _8)
                    switch _10
                    case 0x06fdde03 { external_fun_name() }
                    case 0x095ea7b3 { external_fun_approve() }
                    case 0x18160ddd { external_fun_totalSupply() }
                    case 0x23b872dd { external_fun_transferFrom() }
                    case 0x313ce567 { external_fun_decimals() }
                    case 0x70a08231 { external_fun_balanceOf() }
                    case 0x95d89b41 { external_fun_symbol() }
                    case 0xa9059cbb { external_fun_transfer() }
                    case 0xdd62ed3e { external_fun_allowance() }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            }
            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            {
                let _1 := 0
                let _2 := _1
                revert(_1, _1)
            }
            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            {
                let _1 := 0
                let _2 := _1
                revert(_1, _1)
            }
            function abi_decode(headStart, dataEnd)
            {
                let _1 := 0
                let _2 := sub(dataEnd, headStart)
                let _3 := slt(_2, _1)
                if _3
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            function array_storeLengthForEncoding_string_fromStack(pos, length) -> updated_pos
            {
                mstore(pos, length)
                let _1 := 0x20
                updated_pos := add(pos, _1)
            }
            function copy_memory_to_memory_with_cleanup(src, dst, length)
            {
                let i := 0
                for { }
                lt(i, length)
                {
                    let _1 := 32
                    i := add(i, _1)
                }
                {
                    let _2 := add(src, i)
                    let _3 := mload(_2)
                    let _4 := add(dst, i)
                    mstore(_4, _3)
                }
                let _5 := 0
                let _6 := add(dst, length)
                mstore(_6, _5)
            }
            function abi_encode_string_memory_ptr(value, pos) -> end
            {
                let length := mload(value)
                pos := array_storeLengthForEncoding_string_fromStack(pos, length)
                let _1 := 0x20
                let _2 := add(value, _1)
                copy_memory_to_memory_with_cleanup(_2, pos, length)
                let _3 := not(31)
                let _4 := 31
                let _5 := add(length, _4)
                let _6 := and(_5, _3)
                end := add(pos, _6)
            }
            function abi_encode_string(headStart, value0) -> tail
            {
                let _1 := 32
                tail := add(headStart, _1)
                let _2 := _1
                mstore(headStart, _1)
                tail := abi_encode_string_memory_ptr(value0, tail)
            }
            function external_fun_name()
            {
                let _1 := callvalue()
                if _1
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _2 := calldatasize()
                let _3 := 4
                abi_decode(_3, _2)
                let ret := fun_name()
                let _4 := 64
                let memPos := mload(_4)
                let _5 := abi_encode_string(memPos, ret)
                let _6 := sub(_5, memPos)
                return(memPos, _6)
            }
            function validator_revert_address(value)
            {
                let _1 := sub(shl(160, 1), 1)
                let _2 := and(value, _1)
                let _3 := eq(value, _2)
                let _4 := iszero(_3)
                if _4
                {
                    let _5 := 0
                    let _6 := _5
                    revert(_5, _5)
                }
            }
            function abi_decode_address(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_address(value)
            }
            function validator_revert_uint256(value)
            {
                let _1 := 0
                if _1
                {
                    let _2 := _1
                    let _3 := _1
                    revert(_1, _1)
                }
            }
            function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            function abi_decode_addresst_uint256(headStart, dataEnd) -> value0, value1
            {
                let _1 := 64
                let _2 := sub(dataEnd, headStart)
                let _3 := slt(_2, _1)
                if _3
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_address(headStart, dataEnd)
                let _4 := 32
                let _5 := add(headStart, _4)
                value1 := abi_decode_uint256(_5, dataEnd)
            }
            function abi_encode_bool_to_bool(value, pos)
            {
                let _1 := iszero(value)
                let _2 := iszero(_1)
                mstore(pos, _2)
            }
            function abi_encode_bool(headStart, value0) -> tail
            {
                let _1 := 32
                tail := add(headStart, _1)
                abi_encode_bool_to_bool(value0, headStart)
            }
            function external_fun_approve()
            {
                let _1 := callvalue()
                if _1
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _2 := calldatasize()
                let _3 := 4
                let param, param_1 := abi_decode_addresst_uint256(_3, _2)
                let ret := fun_approve(param, param_1)
                let _4 := 64
                let memPos := mload(_4)
                let _5 := abi_encode_bool(memPos, ret)
                let _6 := sub(_5, memPos)
                return(memPos, _6)
            }
            function abi_encode_uint256_to_uint256(value, pos)
            { mstore(pos, value) }
            function abi_encode_uint256(headStart, value0) -> tail
            {
                let _1 := 32
                tail := add(headStart, _1)
                abi_encode_uint256_to_uint256(value0, headStart)
            }
            function external_fun_totalSupply()
            {
                let _1 := callvalue()
                if _1
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _2 := calldatasize()
                let _3 := 4
                abi_decode(_3, _2)
                let ret := fun_totalSupply()
                let _4 := 64
                let memPos := mload(_4)
                let _5 := abi_encode_uint256(memPos, ret)
                let _6 := sub(_5, memPos)
                return(memPos, _6)
            }
            function abi_decode_addresst_addresst_uint256(headStart, dataEnd) -> value0, value1, value2
            {
                let _1 := 96
                let _2 := sub(dataEnd, headStart)
                let _3 := slt(_2, _1)
                if _3
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_address(headStart, dataEnd)
                let _4 := 32
                let _5 := add(headStart, _4)
                value1 := abi_decode_address(_5, dataEnd)
                let _6 := 64
                let _7 := add(headStart, _6)
                value2 := abi_decode_uint256(_7, dataEnd)
            }
            function external_fun_transferFrom()
            {
                let _1 := callvalue()
                if _1
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _2 := calldatasize()
                let _3 := 4
                let param, param_1, param_2 := abi_decode_addresst_addresst_uint256(_3, _2)
                let ret := fun_transferFrom(param, param_1, param_2)
                let _4 := 64
                let memPos := mload(_4)
                let _5 := abi_encode_bool(memPos, ret)
                let _6 := sub(_5, memPos)
                return(memPos, _6)
            }
            function abi_encode_uint8_to_uint8(value, pos)
            {
                let _1 := 0xff
                let _2 := and(value, _1)
                mstore(pos, _2)
            }
            function abi_encode_uint8(headStart, value0) -> tail
            {
                let _1 := 32
                tail := add(headStart, _1)
                abi_encode_uint8_to_uint8(value0, headStart)
            }
            function external_fun_decimals()
            {
                let _1 := callvalue()
                if _1
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _2 := calldatasize()
                let _3 := 4
                abi_decode(_3, _2)
                let ret := fun_decimals()
                let _4 := 64
                let memPos := mload(_4)
                let _5 := abi_encode_uint8(memPos, ret)
                let _6 := sub(_5, memPos)
                return(memPos, _6)
            }
            function abi_decode_tuple_address(headStart, dataEnd) -> value0
            {
                let _1 := 32
                let _2 := sub(dataEnd, headStart)
                let _3 := slt(_2, _1)
                if _3
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_address(headStart, dataEnd)
            }
            function external_fun_balanceOf()
            {
                let _1 := callvalue()
                if _1
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _2 := calldatasize()
                let _3 := 4
                let _4 := abi_decode_tuple_address(_3, _2)
                let ret := fun_balanceOf(_4)
                let _5 := 64
                let memPos := mload(_5)
                let _6 := abi_encode_uint256(memPos, ret)
                let _7 := sub(_6, memPos)
                return(memPos, _7)
            }
            function external_fun_symbol()
            {
                let _1 := callvalue()
                if _1
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _2 := calldatasize()
                let _3 := 4
                abi_decode(_3, _2)
                let ret := fun_symbol()
                let _4 := 64
                let memPos := mload(_4)
                let _5 := abi_encode_string(memPos, ret)
                let _6 := sub(_5, memPos)
                return(memPos, _6)
            }
            function external_fun_transfer()
            {
                let _1 := callvalue()
                if _1
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _2 := calldatasize()
                let _3 := 4
                let param, param_1 := abi_decode_addresst_uint256(_3, _2)
                let ret := fun_transfer(param, param_1)
                let _4 := 64
                let memPos := mload(_4)
                let _5 := abi_encode_bool(memPos, ret)
                let _6 := sub(_5, memPos)
                return(memPos, _6)
            }
            function abi_decode_addresst_address(headStart, dataEnd) -> value0, value1
            {
                let _1 := 64
                let _2 := sub(dataEnd, headStart)
                let _3 := slt(_2, _1)
                if _3
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_address(headStart, dataEnd)
                let _4 := 32
                let _5 := add(headStart, _4)
                value1 := abi_decode_address(_5, dataEnd)
            }
            function external_fun_allowance()
            {
                let _1 := callvalue()
                if _1
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _2 := calldatasize()
                let _3 := 4
                let param, param_1 := abi_decode_addresst_address(_3, _2)
                let ret := fun_allowance(param, param_1)
                let _4 := 64
                let memPos := mload(_4)
                let _5 := abi_encode_uint256(memPos, ret)
                let _6 := sub(_5, memPos)
                return(memPos, _6)
            }
            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            {
                let _1 := 0
                let _2 := _1
                revert(_1, _1)
            }
            function panic_error_0x22()
            {
                let _1 := shl(224, 0x4e487b71)
                let _2 := 0
                mstore(_2, _1)
                let _3 := 0x22
                let _4 := 4
                mstore(_4, _3)
                let _5 := 0x24
                let _6 := _2
                revert(_2, _5)
            }
            function extract_byte_array_length(data) -> length
            {
                let _1 := 1
                length := shr(_1, data)
                let _2 := _1
                let outOfPlaceEncoding := and(data, _1)
                let _3 := iszero(outOfPlaceEncoding)
                if _3
                {
                    let _4 := 0x7f
                    length := and(length, _4)
                }
                let _5 := 32
                let _6 := lt(length, _5)
                let _7 := eq(outOfPlaceEncoding, _6)
                if _7 { panic_error_0x22() }
            }
            function array_storeLengthForEncoding_string(pos, length) -> updated_pos
            {
                mstore(pos, length)
                let _1 := 0x20
                updated_pos := add(pos, _1)
            }
            function array_dataslot_string_storage(ptr) -> data
            {
                let _1 := 0
                mstore(_1, ptr)
                let _2 := 0x20
                let _3 := _1
                data := keccak256(_1, _2)
            }
            function abi_encode_string_storage(value, pos) -> ret
            {
                let slotValue := sload(value)
                let length := extract_byte_array_length(slotValue)
                pos := array_storeLengthForEncoding_string(pos, length)
                let _1 := 1
                let _2 := and(slotValue, _1)
                switch _2
                case 0 {
                    let _3 := not(255)
                    let _4 := and(slotValue, _3)
                    mstore(pos, _4)
                    let _5 := iszero(length)
                    let _6 := iszero(_5)
                    let _7 := shl(5, _6)
                    ret := add(pos, _7)
                }
                case 1 {
                    let dataPos := array_dataslot_string_storage(value)
                    let i := 0
                    for { }
                    lt(i, length)
                    {
                        let _8 := 0x20
                        i := add(i, _8)
                    }
                    {
                        let _9 := sload(dataPos)
                        let _10 := add(pos, i)
                        mstore(_10, _9)
                        let _11 := _1
                        dataPos := add(dataPos, _1)
                    }
                    ret := add(pos, i)
                }
            }
            function panic_error_0x41()
            {
                let _1 := shl(224, 0x4e487b71)
                let _2 := 0
                mstore(_2, _1)
                let _3 := 0x41
                let _4 := 4
                mstore(_4, _3)
                let _5 := 0x24
                let _6 := _2
                revert(_2, _5)
            }
            function finalize_allocation(memPtr, size)
            {
                let _1 := not(31)
                let _2 := 31
                let _3 := add(size, _2)
                let _4 := and(_3, _1)
                let newFreePtr := add(memPtr, _4)
                let _5 := lt(newFreePtr, memPtr)
                let _6 := 0xffffffffffffffff
                let _7 := gt(newFreePtr, _6)
                let _8 := or(_7, _5)
                if _8 { panic_error_0x41() }
                let _9 := 64
                mstore(_9, newFreePtr)
            }
            function copy_array_from_storage_to_memory_string(slot) -> memPtr
            {
                let _1 := 64
                memPtr := mload(_1)
                let _2 := abi_encode_string_storage(slot, memPtr)
                let _3 := sub(_2, memPtr)
                finalize_allocation(memPtr, _3)
            }
            /// @ast-id 81 @src 2:2074:2163  "function name() public view virtual returns (string memory) {..."
            function fun_name() -> var__mpos
            {
                /// @src 2:2151:2156  "_name"
                let _1 := 0x03
                /// @src 2:2144:2156  "return _name"
                var__mpos := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ copy_array_from_storage_to_memory_string(/** @src 2:2151:2156  "_name" */ _1)
            }
            /// @ast-id 90 @src 2:2276:2369  "function symbol() public view virtual returns (string memory) {..."
            function fun_symbol() -> var_mpos
            {
                /// @src 2:2355:2362  "_symbol"
                let _1 := 0x04
                /// @src 2:2348:2362  "return _symbol"
                var_mpos := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ copy_array_from_storage_to_memory_string(/** @src 2:2355:2362  "_symbol" */ _1)
            }
            /// @ast-id 99 @src 2:3002:3084  "function decimals() public view virtual returns (uint8) {..."
            function fun_decimals() -> var
            {
                /// @src 2:3068:3077  "return 18"
                var := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ 18
            }
            /// @ast-id 108 @src 2:3144:3241  "function totalSupply() public view virtual returns (uint256) {..."
            function fun_totalSupply() -> var
            {
                /// @src 2:3222:3234  "_totalSupply"
                let _1 := 0x02
                /// @src 2:3215:3234  "return _totalSupply"
                var := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ sload(/** @src 2:3222:3234  "_totalSupply" */ _1)
            }
            /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
            function mapping_index_access_mapping_address_uint256_of_address(slot, key) -> dataSlot
            {
                let _1 := and(key, sub(shl(160, 1), 1))
                let _2 := 0
                mstore(_2, _1)
                let _3 := 0x20
                mstore(_3, slot)
                let _4 := 0x40
                let _5 := _2
                dataSlot := keccak256(_2, _4)
            }
            /// @ast-id 121 @src 2:3299:3415  "function balanceOf(address account) public view virtual returns (uint256) {..."
            function fun_balanceOf(var_account) -> var_
            {
                /// @src 2:3390:3399  "_balances"
                let _1 := 0x00
                /// @src 2:3390:3408  "_balances[account]"
                let _2 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:3390:3399  "_balances" */ _1, /** @src 2:3400:3407  "account" */ var_account)
                /// @src 2:3383:3408  "return _balances[account]"
                var_ := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ sload(/** @src 2:3390:3408  "_balances[account]" */ _2)
            }
            /// @ast-id 145 @src 2:3610:3788  "function transfer(address to, uint256 value) public virtual returns (bool) {..."
            function fun_transfer(var_to, var_value) -> var
            {
                /// @src 2:3711:3723  "_msgSender()"
                let _1 := fun_msgSender()
                /// @src 2:3754:3759  "value"
                fun__transfer(/** @src 2:3711:3723  "_msgSender()" */ _1, /** @src 2:3750:3752  "to" */ var_to, /** @src 2:3754:3759  "value" */ var_value)
                /// @src 2:3770:3781  "return true"
                var := /** @src 2:3777:3781  "true" */ 0x01
            }
            /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
            function mapping_index_access_mapping_address_mapping_address_uint256_of_address(slot, key) -> dataSlot
            {
                let _1 := and(key, sub(shl(160, 1), 1))
                let _2 := 0
                mstore(_2, _1)
                let _3 := 0x20
                mstore(_3, slot)
                let _4 := 0x40
                let _5 := _2
                dataSlot := keccak256(_2, _4)
            }
            /// @ast-id 162 @src 2:3846:3986  "function allowance(address owner, address spender) public view virtual returns (uint256) {..."
            function fun_allowance(var_owner, var_spender) -> var
            {
                /// @src 2:3952:3963  "_allowances"
                let _1 := 0x01
                /// @src 2:3952:3970  "_allowances[owner]"
                let _2 := mapping_index_access_mapping_address_mapping_address_uint256_of_address(/** @src 2:3952:3963  "_allowances" */ _1, /** @src 2:3964:3969  "owner" */ var_owner)
                /// @src 2:3952:3979  "_allowances[owner][spender]"
                let _3 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:3952:3970  "_allowances[owner]" */ _2, /** @src 2:3971:3978  "spender" */ var_spender)
                /// @src 2:3945:3979  "return _allowances[owner][spender]"
                var := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ sload(/** @src 2:3952:3979  "_allowances[owner][spender]" */ _3)
            }
            /// @ast-id 186 @src 2:4293:4479  "function approve(address spender, uint256 value) public virtual returns (bool) {..."
            function fun_approve(var_spender, var_value) -> var
            {
                /// @src 2:4398:4410  "_msgSender()"
                let _1 := fun_msgSender()
                /// @src 2:4445:4450  "value"
                fun_approve_426(/** @src 2:4398:4410  "_msgSender()" */ _1, /** @src 2:4436:4443  "spender" */ var_spender, /** @src 2:4445:4450  "value" */ var_value)
                /// @src 2:4461:4472  "return true"
                var := /** @src 2:4468:4472  "true" */ 0x01
            }
            /// @ast-id 218 @src 2:5039:5283  "function transferFrom(address from, address to, uint256 value) public virtual returns (bool) {..."
            function fun_transferFrom(var_from, var_to, var_value) -> var
            {
                /// @src 2:5160:5172  "_msgSender()"
                let _1 := fun_msgSender()
                /// @src 2:5213:5218  "value"
                fun_spendAllowance(/** @src 2:5198:5202  "from" */ var_from, /** @src 2:5160:5172  "_msgSender()" */ _1, /** @src 2:5213:5218  "value" */ var_value)
                /// @src 2:5249:5254  "value"
                fun__transfer(/** @src 2:5239:5243  "from" */ var_from, /** @src 2:5245:5247  "to" */ var_to, /** @src 2:5249:5254  "value" */ var_value)
                /// @src 2:5265:5276  "return true"
                var := /** @src 2:5272:5276  "true" */ 0x01
            }
            /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
            function abi_encode_address(value, pos)
            {
                let _1 := sub(shl(160, 1), 1)
                let _2 := and(value, _1)
                mstore(pos, _2)
            }
            function abi_encode_tuple_address(headStart, value0) -> tail
            {
                let _1 := 32
                tail := add(headStart, _1)
                abi_encode_address(value0, headStart)
            }
            /// @ast-id 265 @src 2:5656:5956  "function _transfer(address from, address to, uint256 value) internal {..."
            function fun__transfer(var_from, var_to, var_value)
            {
                /// @src 2:5739:5743  "from"
                let expr := var_from
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _1 := sub(shl(160, 1), 1)
                let _2 := and(/** @src 2:5739:5757  "from == address(0)" */ var_from, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _1)
                /// @src 2:5739:5757  "from == address(0)"
                let _3 := iszero(/** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _2)
                /// @src 2:5735:5821  "if (from == address(0)) {..."
                if /** @src 2:5739:5757  "from == address(0)" */ _3
                /// @src 2:5735:5821  "if (from == address(0)) {..."
                {
                    /// @src 2:5799:5809  "address(0)"
                    let expr_1 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ 0
                    let _4 := 64
                    /// @src 2:5780:5810  "ERC20InvalidSender(address(0))"
                    let _5 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ mload(_4)
                    /// @src 2:5780:5810  "ERC20InvalidSender(address(0))"
                    let _6 := shl(225, 0x4b637e8f)
                    mstore(_5, _6)
                    let _7 := 4
                    let _8 := add(_5, _7)
                    let _9 := abi_encode_tuple_address(_8, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ expr_1)
                    /// @src 2:5780:5810  "ERC20InvalidSender(address(0))"
                    let _10 := sub(_9, _5)
                    revert(_5, _10)
                }
                /// @src 2:5834:5836  "to"
                let expr_2 := var_to
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _11 := _1
                let _12 := and(/** @src 2:5834:5850  "to == address(0)" */ var_to, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _1)
                /// @src 2:5834:5850  "to == address(0)"
                let _13 := iszero(/** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _12)
                /// @src 2:5830:5916  "if (to == address(0)) {..."
                if /** @src 2:5834:5850  "to == address(0)" */ _13
                /// @src 2:5830:5916  "if (to == address(0)) {..."
                {
                    /// @src 2:5894:5904  "address(0)"
                    let expr_3 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ 0
                    let _14 := 64
                    /// @src 2:5873:5905  "ERC20InvalidReceiver(address(0))"
                    let _15 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ mload(_14)
                    /// @src 2:5873:5905  "ERC20InvalidReceiver(address(0))"
                    let _16 := shl(224, 0xec442f05)
                    mstore(_15, _16)
                    let _17 := 4
                    let _18 := add(_15, _17)
                    let _19 := abi_encode_tuple_address(_18, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ expr_3)
                    /// @src 2:5873:5905  "ERC20InvalidReceiver(address(0))"
                    let _20 := sub(_19, _15)
                    revert(_15, _20)
                }
                /// @src 2:5943:5948  "value"
                fun_update(/** @src 2:5933:5937  "from" */ var_from, /** @src 2:5939:5941  "to" */ var_to, /** @src 2:5943:5948  "value" */ var_value)
            }
            /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
            function abi_encode_address_uint256_uint256(headStart, value0, value1, value2) -> tail
            {
                let _1 := 96
                tail := add(headStart, _1)
                abi_encode_address(value0, headStart)
                let _2 := 32
                let _3 := add(headStart, _2)
                abi_encode_uint256_to_uint256(value1, _3)
                let _4 := 64
                let _5 := add(headStart, _4)
                abi_encode_uint256_to_uint256(value2, _5)
            }
            function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            function update_storage_value_offsett_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            function panic_error_0x11()
            {
                let _1 := shl(224, 0x4e487b71)
                let _2 := 0
                mstore(_2, _1)
                let _3 := 0x11
                let _4 := 4
                mstore(_4, _3)
                let _5 := 0x24
                let _6 := _2
                revert(_2, _5)
            }
            function checked_add_uint256(x, y) -> sum
            {
                x := x
                y := y
                sum := add(x, y)
                let _1 := gt(x, sum)
                if _1 { panic_error_0x11() }
            }
            /// @ast-id 342 @src 2:6271:7378  "function _update(address from, address to, uint256 value) internal virtual {..."
            function fun_update(var_from, var_to, var_value)
            {
                /// @src 2:6360:6364  "from"
                let expr := var_from
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _1 := sub(shl(160, 1), 1)
                let _2 := and(/** @src 2:6360:6378  "from == address(0)" */ var_from, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _1)
                /// @src 2:6360:6378  "from == address(0)"
                let _3 := iszero(/** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _2)
                /// @src 2:6356:6896  "if (from == address(0)) {..."
                switch /** @src 2:6360:6378  "from == address(0)" */ _3
                case /** @src 2:6356:6896  "if (from == address(0)) {..." */ 0 {
                    /// @src 2:6570:6579  "_balances"
                    let _4 := 0x00
                    /// @src 2:6570:6585  "_balances[from]"
                    let _5 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:6570:6579  "_balances" */ _4, /** @src 2:6580:6584  "from" */ var_from)
                    /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                    let _6 := sload(/** @src 2:6570:6585  "_balances[from]" */ _5)
                    /// @src 2:6548:6585  "uint256 fromBalance = _balances[from]"
                    let var_fromBalance := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _6
                    /// @src 2:6603:6622  "fromBalance < value"
                    let _7 := lt(/** @src 2:6603:6614  "fromBalance" */ _6, /** @src 2:6617:6622  "value" */ var_value)
                    /// @src 2:6599:6714  "if (fromBalance < value) {..."
                    if /** @src 2:6603:6622  "fromBalance < value" */ _7
                    /// @src 2:6599:6714  "if (fromBalance < value) {..."
                    {
                        /// @src 2:6674:6678  "from"
                        let expr_1 := var_from
                        /// @src 2:6680:6691  "fromBalance"
                        let expr_2 := _6
                        /// @src 2:6693:6698  "value"
                        let expr_3 := var_value
                        /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                        let _8 := 64
                        /// @src 2:6649:6699  "ERC20InsufficientBalance(from, fromBalance, value)"
                        let _9 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ mload(_8)
                        /// @src 2:6649:6699  "ERC20InsufficientBalance(from, fromBalance, value)"
                        let _10 := shl(226, 0x391434e3)
                        mstore(_9, _10)
                        let _11 := 4
                        let _12 := add(_9, _11)
                        let _13 := abi_encode_address_uint256_uint256(_12, var_from, _6, var_value)
                        let _14 := sub(_13, _9)
                        revert(_9, _14)
                    }
                    /// @src 2:6852:6871  "fromBalance - value"
                    let expr_4 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ sub(/** @src 2:6852:6863  "fromBalance" */ _6, /** @src 2:6866:6871  "value" */ var_value)
                    /// @src 2:6834:6843  "_balances"
                    let _15 := _4
                    /// @src 2:6834:6849  "_balances[from]"
                    let _16 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:6834:6843  "_balances" */ _4, /** @src 2:6844:6848  "from" */ var_from)
                    /// @src 2:6834:6871  "_balances[from] = fromBalance - value"
                    update_storage_value_offsett_uint256_to_uint256(/** @src 2:6834:6849  "_balances[from]" */ _16, /** @src 2:6834:6871  "_balances[from] = fromBalance - value" */ expr_4)
                }
                default /// @src 2:6356:6896  "if (from == address(0)) {..."
                {
                    /// @src 2:6496:6517  "_totalSupply += value"
                    let _17 := 0x02
                    /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                    let _18 := sload(/** @src 2:6496:6517  "_totalSupply += value" */ _17)
                    /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                    let _19 := _18
                    /// @src 2:6496:6517  "_totalSupply += value"
                    let _20 := checked_add_uint256(/** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _18, /** @src 2:6512:6517  "value" */ var_value)
                    /// @src 2:6496:6517  "_totalSupply += value"
                    let _21 := _17
                    update_storage_value_offsett_uint256_to_uint256(_17, _20)
                }
                /// @src 2:6910:6912  "to"
                let expr_5 := var_to
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _22 := _1
                let _23 := and(/** @src 2:6910:6926  "to == address(0)" */ var_to, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _1)
                /// @src 2:6910:6926  "to == address(0)"
                let _24 := iszero(/** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _23)
                /// @src 2:6906:7331  "if (to == address(0)) {..."
                switch /** @src 2:6910:6926  "to == address(0)" */ _24
                case /** @src 2:6906:7331  "if (to == address(0)) {..." */ 0 {
                    /// @src 2:7301:7306  "value"
                    let expr_6 := var_value
                    /// @src 2:7284:7293  "_balances"
                    let _25 := 0x00
                    /// @src 2:7284:7297  "_balances[to]"
                    let _26 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:7284:7293  "_balances" */ _25, /** @src 2:7294:7296  "to" */ var_to)
                    /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                    let _27 := sload(/** @src 2:7284:7306  "_balances[to] += value" */ _26)
                    /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                    let _28 := _27
                    let _29 := add(_27, /** @src 2:7284:7306  "_balances[to] += value" */ var_value)
                    update_storage_value_offsett_uint256_to_uint256(_26, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _29)
                }
                default /// @src 2:6906:7331  "if (to == address(0)) {..."
                {
                    /// @src 2:7073:7094  "_totalSupply -= value"
                    let _30 := 0x02
                    /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                    let _31 := sload(/** @src 2:7073:7094  "_totalSupply -= value" */ _30)
                    /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                    let _32 := _31
                    let _33 := sub(_31, /** @src 2:7089:7094  "value" */ var_value)
                    /// @src 2:7073:7094  "_totalSupply -= value"
                    let _34 := _30
                    update_storage_value_offsett_uint256_to_uint256(_30, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _33)
                }
                /// @src 2:7355:7359  "from"
                let expr_7 := var_from
                /// @src 2:7361:7363  "to"
                let expr_8 := var_to
                /// @src 2:7365:7370  "value"
                let expr_9 := var_value
                /// @src 2:7346:7371  "Transfer(from, to, value)"
                let _35 := 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef
                let _36 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _2
                /// @src 2:7346:7371  "Transfer(from, to, value)"
                let _37 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _23
                let _38 := 64
                /// @src 2:7346:7371  "Transfer(from, to, value)"
                let _39 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ mload(_38)
                /// @src 2:7346:7371  "Transfer(from, to, value)"
                let _40 := abi_encode_uint256(_39, var_value)
                let _41 := sub(_40, _39)
                log3(_39, _41, _35, _2, _23)
            }
            /// @ast-id 426 @src 2:8989:9117  "function _approve(address owner, address spender, uint256 value) internal {..."
            function fun_approve_426(var_owner, var_spender, var_value)
            {
                /// @src 2:9082:9087  "owner"
                let expr := var_owner
                /// @src 2:9105:9109  "true"
                let _1 := 0x01
                fun__approve(var_owner, /** @src 2:9089:9096  "spender" */ var_spender, /** @src 2:9098:9103  "value" */ var_value, /** @src 2:9105:9109  "true" */ _1)
            }
            /// @ast-id 486 @src 2:9949:10381  "function _approve(address owner, address spender, uint256 value, bool emitEvent) internal virtual {..."
            function fun__approve(var_owner, var_spender, var_value, var_emitEvent)
            {
                /// @src 2:10061:10066  "owner"
                let expr := var_owner
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _1 := sub(shl(160, 1), 1)
                let _2 := and(/** @src 2:10061:10080  "owner == address(0)" */ var_owner, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _1)
                /// @src 2:10061:10080  "owner == address(0)"
                let _3 := iszero(/** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _2)
                /// @src 2:10057:10146  "if (owner == address(0)) {..."
                if /** @src 2:10061:10080  "owner == address(0)" */ _3
                /// @src 2:10057:10146  "if (owner == address(0)) {..."
                {
                    /// @src 2:10124:10134  "address(0)"
                    let expr_1 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ 0
                    let _4 := 64
                    /// @src 2:10103:10135  "ERC20InvalidApprover(address(0))"
                    let _5 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ mload(_4)
                    /// @src 2:10103:10135  "ERC20InvalidApprover(address(0))"
                    let _6 := shl(224, 0xe602df05)
                    mstore(_5, _6)
                    let _7 := 4
                    let _8 := add(_5, _7)
                    let _9 := abi_encode_tuple_address(_8, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ expr_1)
                    /// @src 2:10103:10135  "ERC20InvalidApprover(address(0))"
                    let _10 := sub(_9, _5)
                    revert(_5, _10)
                }
                /// @src 2:10159:10166  "spender"
                let expr_2 := var_spender
                /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                let _11 := _1
                let _12 := and(/** @src 2:10159:10180  "spender == address(0)" */ var_spender, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _1)
                /// @src 2:10159:10180  "spender == address(0)"
                let _13 := iszero(/** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _12)
                /// @src 2:10155:10245  "if (spender == address(0)) {..."
                if /** @src 2:10159:10180  "spender == address(0)" */ _13
                /// @src 2:10155:10245  "if (spender == address(0)) {..."
                {
                    /// @src 2:10223:10233  "address(0)"
                    let expr_3 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ 0
                    let _14 := 64
                    /// @src 2:10203:10234  "ERC20InvalidSpender(address(0))"
                    let _15 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ mload(_14)
                    /// @src 2:10203:10234  "ERC20InvalidSpender(address(0))"
                    let _16 := shl(225, 0x4a1406b1)
                    mstore(_15, _16)
                    let _17 := 4
                    let _18 := add(_15, _17)
                    let _19 := abi_encode_tuple_address(_18, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ expr_3)
                    /// @src 2:10203:10234  "ERC20InvalidSpender(address(0))"
                    let _20 := sub(_19, _15)
                    revert(_15, _20)
                }
                /// @src 2:10284:10289  "value"
                let expr_4 := var_value
                /// @src 2:10254:10265  "_allowances"
                let _21 := 0x01
                /// @src 2:10254:10272  "_allowances[owner]"
                let _22 := mapping_index_access_mapping_address_mapping_address_uint256_of_address(/** @src 2:10254:10265  "_allowances" */ _21, /** @src 2:10266:10271  "owner" */ var_owner)
                /// @src 2:10254:10281  "_allowances[owner][spender]"
                let _23 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:10254:10272  "_allowances[owner]" */ _22, /** @src 2:10273:10280  "spender" */ var_spender)
                /// @src 2:10254:10289  "_allowances[owner][spender] = value"
                update_storage_value_offsett_uint256_to_uint256(/** @src 2:10254:10281  "_allowances[owner][spender]" */ _23, /** @src 2:10254:10289  "_allowances[owner][spender] = value" */ var_value)
                /// @src 2:10299:10375  "if (emitEvent) {..."
                if /** @src 2:10303:10312  "emitEvent" */ var_emitEvent
                /// @src 2:10299:10375  "if (emitEvent) {..."
                {
                    /// @src 2:10342:10347  "owner"
                    let expr_5 := var_owner
                    /// @src 2:10349:10356  "spender"
                    let expr_6 := var_spender
                    /// @src 2:10358:10363  "value"
                    let expr_7 := var_value
                    /// @src 2:10333:10364  "Approval(owner, spender, value)"
                    let _24 := 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925
                    let _25 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _2
                    /// @src 2:10333:10364  "Approval(owner, spender, value)"
                    let _26 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _12
                    let _27 := 64
                    /// @src 2:10333:10364  "Approval(owner, spender, value)"
                    let _28 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ mload(_27)
                    /// @src 2:10333:10364  "Approval(owner, spender, value)"
                    let _29 := abi_encode_uint256(_28, var_value)
                    let _30 := sub(_29, _28)
                    log3(_28, _30, _24, _2, _12)
                }
            }
            /// @ast-id 534 @src 2:10663:11140  "function _spendAllowance(address owner, address spender, uint256 value) internal virtual {..."
            function fun_spendAllowance(var_owner, var_spender, var_value)
            {
                /// @src 2:10762:10814  "uint256 currentAllowance = allowance(owner, spender)"
                let var_currentAllowance := /** @src 2:10789:10814  "allowance(owner, spender)" */ fun_allowance(/** @src 2:10799:10804  "owner" */ var_owner, /** @src 2:10806:10813  "spender" */ var_spender)
                /// @src 2:10848:10865  "type(uint256).max"
                let _1 := not(0)
                /// @src 2:10828:10865  "currentAllowance != type(uint256).max"
                let _2 := eq(/** @src 2:10828:10844  "currentAllowance" */ var_currentAllowance, /** @src 2:10848:10865  "type(uint256).max" */ _1)
                /// @src 2:10828:10865  "currentAllowance != type(uint256).max"
                let _3 := iszero(_2)
                /// @src 2:10824:11134  "if (currentAllowance != type(uint256).max) {..."
                if /** @src 2:10828:10865  "currentAllowance != type(uint256).max" */ _3
                /// @src 2:10824:11134  "if (currentAllowance != type(uint256).max) {..."
                {
                    /// @src 2:10885:10909  "currentAllowance < value"
                    let _4 := lt(/** @src 2:10885:10901  "currentAllowance" */ var_currentAllowance, /** @src 2:10904:10909  "value" */ var_value)
                    /// @src 2:10881:11011  "if (currentAllowance < value) {..."
                    if /** @src 2:10885:10909  "currentAllowance < value" */ _4
                    /// @src 2:10881:11011  "if (currentAllowance < value) {..."
                    {
                        /// @src 2:10963:10970  "spender"
                        let expr := var_spender
                        /// @src 2:10972:10988  "currentAllowance"
                        let expr_1 := var_currentAllowance
                        /// @src 2:10990:10995  "value"
                        let expr_2 := var_value
                        /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                        let _5 := 64
                        /// @src 2:10936:10996  "ERC20InsufficientAllowance(spender, currentAllowance, value)"
                        let _6 := /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ mload(_5)
                        /// @src 2:10936:10996  "ERC20InsufficientAllowance(spender, currentAllowance, value)"
                        let _7 := shl(225, 0x7dc7a0d9)
                        mstore(_6, _7)
                        let _8 := 4
                        let _9 := add(_6, _8)
                        let _10 := abi_encode_address_uint256_uint256(_9, var_spender, var_currentAllowance, var_value)
                        let _11 := sub(_10, _6)
                        revert(_6, _11)
                    }
                    /// @src 2:11061:11066  "owner"
                    let expr_3 := var_owner
                    /// @src 2:11068:11075  "spender"
                    let expr_4 := var_spender
                    /// @src 2:11103:11108  "false"
                    let _12 := 0x00
                    /// @src 1:82:197  "contract ERC20Shim is ERC20 {..."
                    let _13 := sub(/** @src 2:11077:11093  "currentAllowance" */ var_currentAllowance, /** @src 2:11096:11101  "value" */ var_value)
                    /// @src 2:11103:11108  "false"
                    fun__approve(var_owner, var_spender, /** @src 1:82:197  "contract ERC20Shim is ERC20 {..." */ _13, /** @src 2:11103:11108  "false" */ _12)
                }
            }
            /// @ast-id 788 @src 5:656:752  "function _msgSender() internal view virtual returns (address) {..."
            function fun_msgSender() -> var
            {
                /// @src 5:728:745  "return msg.sender"
                var := /** @src 5:735:745  "msg.sender" */ caller()
            }
        }
        data ".metadata" hex"a26469706673582212203d932434e4bd4197eab8db2a518b0e9104ba58a8d5544c262968763c71506a0b64736f6c63430008150033"
    }
}

Optimized IR:

Optimized IR:

Optimized IR:

Optimized IR:

