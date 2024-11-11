Optimized IR:
/// @use-src 0:"ERC20shim.sol", 1:"interfaces/draft-IERC6093.sol", 2:"token/ERC20/ERC20.sol", 3:"token/ERC20/IERC20.sol", 4:"token/ERC20/extensions/IERC20Metadata.sol", 5:"utils/Context.sol"
object "ERC20Shim_14" {
    code {
        {
            /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
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
            let _6 := datasize("ERC20Shim_14_deployed")
            let _7 := dataoffset("ERC20Shim_14_deployed")
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
            let allocSize := array_allocation_size_string(length)
            memPtr := allocate_memory(allocSize)
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
        /// @ast-id 13 @src 0:111:154  "constructor() ERC20(\"ERC20Shim\", \"E20S\") {}"
        function constructor_ERC20Shim()
        {
            /// @src 0:131:142  "\"ERC20Shim\""
            let _2_mpos := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ copy_literal_to_memory_73d84741e39ae21500f019e1bd49b1509c4dad0285f14920732b98003dc4a297()
            /// @src 0:144:150  "\"E20S\""
            let _3_mpos := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ copy_literal_to_memory_654a20c509642b4486f3c0baf150dce7367ca9e5f6186c81edaf3f66a3f7c7a3()
            /// @src 0:111:154  "constructor() ERC20(\"ERC20Shim\", \"E20S\") {}"
            constructor_ERC20(_2_mpos, _3_mpos)
        }
        /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
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
            let convertedValue := value
            let _1 := sload(slot)
            let _2 := update_byte_slice_dynamic32(_1, offset, value)
            sstore(slot, _2)
        }
        function storage_set_to_zero_uint256(slot, offset)
        {
            let zero := 0
            update_storage_value_uint256_to_uint256(slot, offset, zero)
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
        function mask_bytes_dynamic(data, bytes) -> result
        {
            let _1 := not(0)
            let _2 := 3
            let _3 := shl(_2, bytes)
            let _4 := shr(_3, _1)
            let mask := not(_4)
            result := and(data, mask)
        }
        function extract_used_part_and_set_length_of_short_byte_array(data, len) -> used
        {
            data := mask_bytes_dynamic(data, len)
            let _1 := 1
            let _2 := shl(_1, len)
            used := or(data, _2)
        }
        function copy_byte_array_to_storage_from_string_to_string(slot, src)
        {
            let newLen := mload(src)
            let _1 := sub(shl(64, 1), 1)
            let _2 := gt(newLen, _1)
            if _2 { panic_error_0x41() }
            let _3 := sload(slot)
            let oldLen := extract_byte_array_length(_3)
            clean_up_bytearray_end_slots_string_storage(slot, oldLen, newLen)
            let srcOffset := 0
            srcOffset := 0x20
            let _4 := 31
            let _5 := gt(newLen, _4)
            switch _5
            case 1 {
                let _6 := not(31)
                let loopEnd := and(newLen, _6)
                let dstPtr := array_dataslot_string_storage(slot)
                let i := 0
                for { }
                lt(i, loopEnd)
                {
                    let _7 := 0x20
                    i := add(i, _7)
                }
                {
                    let _8 := add(src, srcOffset)
                    let _9 := mload(_8)
                    sstore(dstPtr, _9)
                    let _10 := 1
                    dstPtr := add(dstPtr, _10)
                    let _11 := 32
                    srcOffset := add(srcOffset, _11)
                }
                let _12 := lt(loopEnd, newLen)
                if _12
                {
                    let _13 := add(src, srcOffset)
                    let lastValue := mload(_13)
                    let _14 := _4
                    let _15 := and(newLen, _4)
                    let _16 := mask_bytes_dynamic(lastValue, _15)
                    sstore(dstPtr, _16)
                }
                let _17 := 1
                let _18 := _17
                let _19 := shl(_17, newLen)
                let _20 := add(_19, _17)
                sstore(slot, _20)
            }
            default {
                let value := 0
                if newLen
                {
                    let _21 := add(src, srcOffset)
                    value := mload(_21)
                }
                let _22 := extract_used_part_and_set_length_of_short_byte_array(value, newLen)
                sstore(slot, _22)
            }
        }
        function update_storage_value_offsett_string_to_string(slot, value)
        {
            copy_byte_array_to_storage_from_string_to_string(slot, value)
        }
        /// @ast-id 66 @src 2:1601:1714  "constructor(string memory name_, string memory symbol_) {..."
        function constructor_ERC20(var_name_mpos, var_symbol_mpos)
        {
            /// @src 2:1675:1680  "name_"
            let _4_mpos := var_name_mpos
            let expr_mpos := var_name_mpos
            /// @src 2:1667:1680  "_name = name_"
            let _1 := 0x03
            update_storage_value_offsett_string_to_string(_1, var_name_mpos)
            /// @src 2:1700:1707  "symbol_"
            let _mpos := var_symbol_mpos
            let expr_62_mpos := var_symbol_mpos
            /// @src 2:1690:1707  "_symbol = symbol_"
            let _2 := 0x04
            update_storage_value_offsett_string_to_string(_2, var_symbol_mpos)
        }
    }
    /// @use-src 0:"ERC20shim.sol", 2:"token/ERC20/ERC20.sol", 5:"utils/Context.sol"
    object "ERC20Shim_14_deployed" {
        code {
            {
                /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
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
                    let selector := shr(_9, _8)
                    switch selector
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
                let memEnd := abi_encode_string(memPos, ret)
                let _5 := sub(memEnd, memPos)
                return(memPos, _5)
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
                let offset := 32
                let _4 := add(headStart, offset)
                value1 := abi_decode_uint256(_4, dataEnd)
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
                let memEnd := abi_encode_bool(memPos, ret)
                let _5 := sub(memEnd, memPos)
                return(memPos, _5)
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
                let memEnd := abi_encode_uint256(memPos, ret)
                let _5 := sub(memEnd, memPos)
                return(memPos, _5)
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
                let offset := 32
                let _4 := add(headStart, offset)
                value1 := abi_decode_address(_4, dataEnd)
                let offset_1 := 64
                let _5 := add(headStart, offset_1)
                value2 := abi_decode_uint256(_5, dataEnd)
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
                let memEnd := abi_encode_bool(memPos, ret)
                let _5 := sub(memEnd, memPos)
                return(memPos, _5)
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
                let memEnd := abi_encode_uint8(memPos, ret)
                let _5 := sub(memEnd, memPos)
                return(memPos, _5)
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
                let param := abi_decode_tuple_address(_3, _2)
                let ret := fun_balanceOf(param)
                let _4 := 64
                let memPos := mload(_4)
                let memEnd := abi_encode_uint256(memPos, ret)
                let _5 := sub(memEnd, memPos)
                return(memPos, _5)
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
                let memEnd := abi_encode_string(memPos, ret)
                let _5 := sub(memEnd, memPos)
                return(memPos, _5)
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
                let memEnd := abi_encode_bool(memPos, ret)
                let _5 := sub(memEnd, memPos)
                return(memPos, _5)
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
                let offset := 32
                let _4 := add(headStart, offset)
                value1 := abi_decode_address(_4, dataEnd)
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
                let memEnd := abi_encode_uint256(memPos, ret)
                let _5 := sub(memEnd, memPos)
                return(memPos, _5)
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
                let end := abi_encode_string_storage(slot, memPtr)
                let _2 := sub(end, memPtr)
                finalize_allocation(memPtr, _2)
            }
            /// @ast-id 75 @src 2:1779:1868  "function name() public view virtual returns (string memory) {..."
            function fun_name() -> var__mpos
            {
                /// @src 2:1856:1861  "_name"
                let _2_slot := 0x03
                let expr_72_slot := _2_slot
                /// @src 2:1849:1861  "return _name"
                var__mpos := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ copy_array_from_storage_to_memory_string(/** @src 2:1856:1861  "_name" */ _2_slot)
            }
            /// @ast-id 84 @src 2:1981:2074  "function symbol() public view virtual returns (string memory) {..."
            function fun_symbol() -> var_mpos
            {
                /// @src 2:2060:2067  "_symbol"
                let _4_slot := 0x04
                let expr_81_slot := _4_slot
                /// @src 2:2053:2067  "return _symbol"
                var_mpos := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ copy_array_from_storage_to_memory_string(/** @src 2:2060:2067  "_symbol" */ _4_slot)
            }
            /// @ast-id 93 @src 2:2707:2789  "function decimals() public view virtual returns (uint8) {..."
            function fun_decimals() -> var
            {
                /// @src 2:2773:2782  "return 18"
                var := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ 18
            }
            /// @ast-id 102 @src 2:2849:2946  "function totalSupply() public view virtual returns (uint256) {..."
            function fun_totalSupply() -> var_
            {
                /// @src 2:2927:2939  "_totalSupply"
                let _1 := 0x02
                /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                let _2 := sload(/** @src 2:2927:2939  "_totalSupply" */ _1)
                /// @src 2:2920:2939  "return _totalSupply"
                var_ := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _2
            }
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
            /// @ast-id 115 @src 2:3004:3120  "function balanceOf(address account) public view virtual returns (uint256) {..."
            function fun_balanceOf(var_account) -> var
            {
                /// @src 2:3095:3104  "_balances"
                let _9_slot := 0x00
                let expr_110_slot := _9_slot
                /// @src 2:3105:3112  "account"
                let _1 := var_account
                let expr := var_account
                /// @src 2:3095:3113  "_balances[account]"
                let _2 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:3095:3104  "_balances" */ _9_slot, /** @src 2:3095:3113  "_balances[account]" */ var_account)
                /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                let _3 := sload(/** @src 2:3095:3113  "_balances[account]" */ _2)
                /// @src 2:3088:3113  "return _balances[account]"
                var := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _3
            }
            /// @ast-id 139 @src 2:3315:3493  "function transfer(address to, uint256 value) public virtual returns (bool) {..."
            function fun_transfer(var_to, var_value) -> var
            {
                /// @src 2:3416:3428  "_msgSender()"
                let expr := fun_msgSender()
                /// @src 2:3400:3428  "address owner = _msgSender()"
                let var_owner := expr
                /// @src 2:3448:3453  "owner"
                let _1 := expr
                let expr_1 := expr
                /// @src 2:3455:3457  "to"
                let _2 := var_to
                let expr_2 := var_to
                /// @src 2:3459:3464  "value"
                let _3 := var_value
                let expr_3 := var_value
                fun__transfer(expr, var_to, var_value)
                /// @src 2:3475:3486  "return true"
                var := /** @src 2:3482:3486  "true" */ 0x01
            }
            /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
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
            /// @ast-id 156 @src 2:3551:3691  "function allowance(address owner, address spender) public view virtual returns (uint256) {..."
            function fun_allowance(var_owner, var_spender) -> var
            {
                /// @src 2:3657:3668  "_allowances"
                let _slot := 0x01
                let expr_149_slot := _slot
                /// @src 2:3669:3674  "owner"
                let _1 := var_owner
                let expr := var_owner
                /// @src 2:3657:3675  "_allowances[owner]"
                let _2 := mapping_index_access_mapping_address_mapping_address_uint256_of_address(/** @src 2:3657:3668  "_allowances" */ _slot, /** @src 2:3657:3675  "_allowances[owner]" */ var_owner)
                let _21_slot := _2
                let expr_151_slot := _2
                /// @src 2:3676:3683  "spender"
                let _3 := var_spender
                let expr_1 := var_spender
                /// @src 2:3657:3684  "_allowances[owner][spender]"
                let _4 := mapping_index_access_mapping_address_uint256_of_address(_2, var_spender)
                /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                let _5 := sload(/** @src 2:3657:3684  "_allowances[owner][spender]" */ _4)
                /// @src 2:3650:3684  "return _allowances[owner][spender]"
                var := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _5
            }
            /// @ast-id 180 @src 2:3998:4184  "function approve(address spender, uint256 value) public virtual returns (bool) {..."
            function fun_approve(var_spender, var_value) -> var
            {
                /// @src 2:4103:4115  "_msgSender()"
                let expr := fun_msgSender()
                /// @src 2:4087:4115  "address owner = _msgSender()"
                let var_owner := expr
                /// @src 2:4134:4139  "owner"
                let _1 := expr
                let expr_1 := expr
                /// @src 2:4141:4148  "spender"
                let _2 := var_spender
                let expr_2 := var_spender
                /// @src 2:4150:4155  "value"
                let _3 := var_value
                let expr_3 := var_value
                fun_approve_420(expr, var_spender, var_value)
                /// @src 2:4166:4177  "return true"
                var := /** @src 2:4173:4177  "true" */ 0x01
            }
            /// @ast-id 212 @src 2:4776:5020  "function transferFrom(address from, address to, uint256 value) public virtual returns (bool) {..."
            function fun_transferFrom(var_from, var_to, var_value) -> var
            {
                /// @src 2:4897:4909  "_msgSender()"
                let expr := fun_msgSender()
                /// @src 2:4879:4909  "address spender = _msgSender()"
                let var_spender := expr
                /// @src 2:4935:4939  "from"
                let _1 := var_from
                let expr_1 := var_from
                /// @src 2:4941:4948  "spender"
                let _2 := expr
                let expr_2 := expr
                /// @src 2:4950:4955  "value"
                let _3 := var_value
                let expr_3 := var_value
                fun_spendAllowance(var_from, expr, var_value)
                /// @src 2:4976:4980  "from"
                let _4 := var_from
                let expr_4 := var_from
                /// @src 2:4982:4984  "to"
                let _5 := var_to
                let expr_5 := var_to
                /// @src 2:4986:4991  "value"
                let _6 := var_value
                let expr_6 := var_value
                fun__transfer(var_from, var_to, var_value)
                /// @src 2:5002:5013  "return true"
                var := /** @src 2:5009:5013  "true" */ 0x01
            }
            /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
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
            /// @ast-id 259 @src 2:5393:5693  "function _transfer(address from, address to, uint256 value) internal {..."
            function fun__transfer(var_from, var_to, var_value)
            {
                /// @src 2:5476:5480  "from"
                let _1 := var_from
                let expr := var_from
                /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                let _2 := sub(shl(160, 1), 1)
                let _3 := and(/** @src 2:5476:5494  "from == address(0)" */ var_from, /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _2)
                /// @src 2:5476:5494  "from == address(0)"
                let expr_1 := iszero(/** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _3)
                /// @src 2:5472:5558  "if (from == address(0)) {..."
                if expr_1
                {
                    /// @src 2:5536:5546  "address(0)"
                    let expr_2 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ 0
                    let _4 := 64
                    /// @src 2:5517:5547  "ERC20InvalidSender(address(0))"
                    let _5 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ mload(_4)
                    /// @src 2:5517:5547  "ERC20InvalidSender(address(0))"
                    let _6 := shl(225, 0x4b637e8f)
                    mstore(_5, _6)
                    let _7 := 4
                    let _8 := add(_5, _7)
                    let _9 := abi_encode_tuple_address(_8, /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ expr_2)
                    /// @src 2:5517:5547  "ERC20InvalidSender(address(0))"
                    let _10 := sub(_9, _5)
                    revert(_5, _10)
                }
                /// @src 2:5571:5573  "to"
                let _11 := var_to
                let expr_3 := var_to
                /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                let _12 := _2
                let _13 := and(/** @src 2:5571:5587  "to == address(0)" */ var_to, /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _2)
                /// @src 2:5571:5587  "to == address(0)"
                let expr_4 := iszero(/** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _13)
                /// @src 2:5567:5653  "if (to == address(0)) {..."
                if expr_4
                {
                    /// @src 2:5631:5641  "address(0)"
                    let expr_5 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ 0
                    let _14 := 64
                    /// @src 2:5610:5642  "ERC20InvalidReceiver(address(0))"
                    let _15 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ mload(_14)
                    /// @src 2:5610:5642  "ERC20InvalidReceiver(address(0))"
                    let _16 := shl(224, 0xec442f05)
                    mstore(_15, _16)
                    let _17 := 4
                    let _18 := add(_15, _17)
                    let _19 := abi_encode_tuple_address(_18, /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ expr_5)
                    /// @src 2:5610:5642  "ERC20InvalidReceiver(address(0))"
                    let _20 := sub(_19, _15)
                    revert(_15, _20)
                }
                /// @src 2:5670:5674  "from"
                let _21 := var_from
                let expr_6 := var_from
                /// @src 2:5676:5678  "to"
                let _22 := var_to
                let expr_7 := var_to
                /// @src 2:5680:5685  "value"
                let _23 := var_value
                let expr_8 := var_value
                fun_update(var_from, var_to, var_value)
            }
            /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
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
                let convertedValue := value
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
            /// @ast-id 336 @src 2:6008:7115  "function _update(address from, address to, uint256 value) internal virtual {..."
            function fun_update(var_from, var_to, var_value)
            {
                /// @src 2:6097:6101  "from"
                let _1 := var_from
                let expr := var_from
                /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                let _2 := sub(shl(160, 1), 1)
                let _3 := and(/** @src 2:6097:6115  "from == address(0)" */ var_from, /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _2)
                /// @src 2:6097:6115  "from == address(0)"
                let expr_1 := iszero(/** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _3)
                /// @src 2:6093:6633  "if (from == address(0)) {..."
                switch expr_1
                case 0 {
                    /// @src 2:6307:6316  "_balances"
                    let _46_slot := 0x00
                    let expr_282_slot := _46_slot
                    /// @src 2:6317:6321  "from"
                    let _4 := var_from
                    let expr_2 := var_from
                    /// @src 2:6307:6322  "_balances[from]"
                    let _5 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:6307:6316  "_balances" */ _46_slot, /** @src 2:6307:6322  "_balances[from]" */ var_from)
                    /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                    let _6 := sload(/** @src 2:6307:6322  "_balances[from]" */ _5)
                    let _7 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _6
                    /// @src 2:6307:6322  "_balances[from]"
                    let expr_3 := _6
                    /// @src 2:6285:6322  "uint256 fromBalance = _balances[from]"
                    let var_fromBalance := _6
                    /// @src 2:6340:6351  "fromBalance"
                    let _8 := _6
                    let expr_4 := _6
                    /// @src 2:6354:6359  "value"
                    let _9 := var_value
                    let expr_5 := var_value
                    /// @src 2:6340:6359  "fromBalance < value"
                    let expr_6 := lt(_6, var_value)
                    /// @src 2:6336:6451  "if (fromBalance < value) {..."
                    if expr_6
                    {
                        /// @src 2:6411:6415  "from"
                        let _10 := var_from
                        let expr_7 := var_from
                        /// @src 2:6417:6428  "fromBalance"
                        let _11 := _6
                        let expr_8 := _6
                        /// @src 2:6430:6435  "value"
                        let _12 := var_value
                        let expr_9 := var_value
                        /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                        let _13 := 64
                        /// @src 2:6386:6436  "ERC20InsufficientBalance(from, fromBalance, value)"
                        let _14 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ mload(_13)
                        /// @src 2:6386:6436  "ERC20InsufficientBalance(from, fromBalance, value)"
                        let _15 := shl(226, 0x391434e3)
                        mstore(_14, _15)
                        let _16 := 4
                        let _17 := add(_14, _16)
                        let _18 := abi_encode_address_uint256_uint256(_17, var_from, _6, var_value)
                        let _19 := sub(_18, _14)
                        revert(_14, _19)
                    }
                    /// @src 2:6589:6600  "fromBalance"
                    let _20 := _6
                    let expr_10 := _6
                    /// @src 2:6603:6608  "value"
                    let _21 := var_value
                    let expr_11 := var_value
                    /// @src 2:6589:6608  "fromBalance - value"
                    let expr_12 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ sub(/** @src 2:6589:6608  "fromBalance - value" */ _6, var_value)
                    /// @src 2:6571:6580  "_balances"
                    let _59_slot := _46_slot
                    let expr_slot := _46_slot
                    /// @src 2:6581:6585  "from"
                    let _22 := var_from
                    let expr_13 := var_from
                    /// @src 2:6571:6586  "_balances[from]"
                    let _23 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:6571:6580  "_balances" */ _46_slot, /** @src 2:6571:6586  "_balances[from]" */ var_from)
                    /// @src 2:6571:6608  "_balances[from] = fromBalance - value"
                    update_storage_value_offsett_uint256_to_uint256(_23, expr_12)
                }
                default /// @src 2:6093:6633  "if (from == address(0)) {..."
                {
                    /// @src 2:6249:6254  "value"
                    let _24 := var_value
                    let expr_14 := var_value
                    /// @src 2:6233:6254  "_totalSupply += value"
                    let _25 := 0x02
                    /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                    let _26 := sload(/** @src 2:6233:6254  "_totalSupply += value" */ _25)
                    let _27 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _26
                    /// @src 2:6233:6254  "_totalSupply += value"
                    let expr_15 := checked_add_uint256(_26, var_value)
                    let _28 := _25
                    update_storage_value_offsett_uint256_to_uint256(_25, expr_15)
                }
                /// @src 2:6647:6649  "to"
                let _29 := var_to
                let expr_16 := var_to
                /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                let _30 := _2
                let _31 := and(/** @src 2:6647:6663  "to == address(0)" */ var_to, /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _2)
                /// @src 2:6647:6663  "to == address(0)"
                let expr_17 := iszero(/** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _31)
                /// @src 2:6643:7068  "if (to == address(0)) {..."
                switch expr_17
                case 0 {
                    /// @src 2:7038:7043  "value"
                    let _32 := var_value
                    let expr_18 := var_value
                    /// @src 2:7021:7030  "_balances"
                    let _66_slot := 0x00
                    let expr_320_slot := _66_slot
                    /// @src 2:7031:7033  "to"
                    let _33 := var_to
                    let expr_19 := var_to
                    /// @src 2:7021:7034  "_balances[to]"
                    let _34 := mapping_index_access_mapping_address_uint256_of_address(/** @src 2:7021:7030  "_balances" */ _66_slot, /** @src 2:7021:7034  "_balances[to]" */ var_to)
                    /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                    let _35 := sload(/** @src 2:7021:7043  "_balances[to] += value" */ _34)
                    let _36 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _35
                    /// @src 2:7021:7043  "_balances[to] += value"
                    let expr_20 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ add(/** @src 2:7021:7043  "_balances[to] += value" */ _35, var_value)
                    update_storage_value_offsett_uint256_to_uint256(_34, expr_20)
                }
                default /// @src 2:6643:7068  "if (to == address(0)) {..."
                {
                    /// @src 2:6826:6831  "value"
                    let _37 := var_value
                    let expr_21 := var_value
                    /// @src 2:6810:6831  "_totalSupply -= value"
                    let _38 := 0x02
                    /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                    let _39 := sload(/** @src 2:6810:6831  "_totalSupply -= value" */ _38)
                    let _40 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _39
                    /// @src 2:6810:6831  "_totalSupply -= value"
                    let expr_22 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ sub(/** @src 2:6810:6831  "_totalSupply -= value" */ _39, var_value)
                    let _41 := _38
                    update_storage_value_offsett_uint256_to_uint256(_38, expr_22)
                }
                /// @src 2:7092:7096  "from"
                let _42 := var_from
                let expr_23 := var_from
                /// @src 2:7098:7100  "to"
                let _43 := var_to
                let expr_24 := var_to
                /// @src 2:7102:7107  "value"
                let _44 := var_value
                let expr_25 := var_value
                /// @src 2:7083:7108  "Transfer(from, to, value)"
                let _45 := 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef
                let _46 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _3
                /// @src 2:7083:7108  "Transfer(from, to, value)"
                let _47 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _31
                let _48 := 64
                /// @src 2:7083:7108  "Transfer(from, to, value)"
                let _49 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ mload(_48)
                /// @src 2:7083:7108  "Transfer(from, to, value)"
                let _50 := abi_encode_uint256(_49, var_value)
                let _51 := sub(_50, _49)
                log3(_49, _51, _45, _3, _31)
            }
            /// @ast-id 420 @src 2:8726:8854  "function _approve(address owner, address spender, uint256 value) internal {..."
            function fun_approve_420(var_owner, var_spender, var_value)
            {
                /// @src 2:8819:8824  "owner"
                let _1 := var_owner
                let expr := var_owner
                /// @src 2:8826:8833  "spender"
                let _2 := var_spender
                let expr_1 := var_spender
                /// @src 2:8835:8840  "value"
                let _3 := var_value
                let expr_2 := var_value
                /// @src 2:8842:8846  "true"
                let expr_3 := 0x01
                fun__approve(var_owner, var_spender, var_value, expr_3)
            }
            /// @ast-id 480 @src 2:9701:10133  "function _approve(address owner, address spender, uint256 value, bool emitEvent) internal virtual {..."
            function fun__approve(var_owner, var_spender, var_value, var_emitEvent)
            {
                /// @src 2:9813:9818  "owner"
                let _1 := var_owner
                let expr := var_owner
                /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                let _2 := sub(shl(160, 1), 1)
                let _3 := and(/** @src 2:9813:9832  "owner == address(0)" */ var_owner, /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _2)
                /// @src 2:9813:9832  "owner == address(0)"
                let expr_1 := iszero(/** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _3)
                /// @src 2:9809:9898  "if (owner == address(0)) {..."
                if expr_1
                {
                    /// @src 2:9876:9886  "address(0)"
                    let expr_2 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ 0
                    let _4 := 64
                    /// @src 2:9855:9887  "ERC20InvalidApprover(address(0))"
                    let _5 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ mload(_4)
                    /// @src 2:9855:9887  "ERC20InvalidApprover(address(0))"
                    let _6 := shl(224, 0xe602df05)
                    mstore(_5, _6)
                    let _7 := 4
                    let _8 := add(_5, _7)
                    let _9 := abi_encode_tuple_address(_8, /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ expr_2)
                    /// @src 2:9855:9887  "ERC20InvalidApprover(address(0))"
                    let _10 := sub(_9, _5)
                    revert(_5, _10)
                }
                /// @src 2:9911:9918  "spender"
                let _11 := var_spender
                let expr_3 := var_spender
                /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                let _12 := _2
                let _13 := and(/** @src 2:9911:9932  "spender == address(0)" */ var_spender, /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _2)
                /// @src 2:9911:9932  "spender == address(0)"
                let expr_4 := iszero(/** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _13)
                /// @src 2:9907:9997  "if (spender == address(0)) {..."
                if expr_4
                {
                    /// @src 2:9975:9985  "address(0)"
                    let expr_5 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ 0
                    let _14 := 64
                    /// @src 2:9955:9986  "ERC20InvalidSpender(address(0))"
                    let _15 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ mload(_14)
                    /// @src 2:9955:9986  "ERC20InvalidSpender(address(0))"
                    let _16 := shl(225, 0x4a1406b1)
                    mstore(_15, _16)
                    let _17 := 4
                    let _18 := add(_15, _17)
                    let _19 := abi_encode_tuple_address(_18, /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ expr_5)
                    /// @src 2:9955:9986  "ERC20InvalidSpender(address(0))"
                    let _20 := sub(_19, _15)
                    revert(_15, _20)
                }
                /// @src 2:10036:10041  "value"
                let _21 := var_value
                let expr_6 := var_value
                /// @src 2:10006:10017  "_allowances"
                let _90_slot := 0x01
                let expr_462_slot := _90_slot
                /// @src 2:10018:10023  "owner"
                let _22 := var_owner
                let expr_7 := var_owner
                /// @src 2:10006:10024  "_allowances[owner]"
                let _23 := mapping_index_access_mapping_address_mapping_address_uint256_of_address(/** @src 2:10006:10017  "_allowances" */ _90_slot, /** @src 2:10006:10024  "_allowances[owner]" */ var_owner)
                let _93_slot := _23
                let expr_465_slot := _23
                /// @src 2:10025:10032  "spender"
                let _24 := var_spender
                let expr_8 := var_spender
                /// @src 2:10006:10033  "_allowances[owner][spender]"
                let _25 := mapping_index_access_mapping_address_uint256_of_address(_23, var_spender)
                /// @src 2:10006:10041  "_allowances[owner][spender] = value"
                update_storage_value_offsett_uint256_to_uint256(_25, var_value)
                /// @src 2:10055:10064  "emitEvent"
                let _26 := var_emitEvent
                let expr_9 := var_emitEvent
                /// @src 2:10051:10127  "if (emitEvent) {..."
                if var_emitEvent
                {
                    /// @src 2:10094:10099  "owner"
                    let _27 := var_owner
                    let expr_10 := var_owner
                    /// @src 2:10101:10108  "spender"
                    let _28 := var_spender
                    let expr_11 := var_spender
                    /// @src 2:10110:10115  "value"
                    let _29 := var_value
                    let expr_12 := var_value
                    /// @src 2:10085:10116  "Approval(owner, spender, value)"
                    let _30 := 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925
                    let _31 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _3
                    /// @src 2:10085:10116  "Approval(owner, spender, value)"
                    let _32 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ _13
                    let _33 := 64
                    /// @src 2:10085:10116  "Approval(owner, spender, value)"
                    let _34 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ mload(_33)
                    /// @src 2:10085:10116  "Approval(owner, spender, value)"
                    let _35 := abi_encode_uint256(_34, var_value)
                    let _36 := sub(_35, _34)
                    log3(_34, _36, _30, _3, _13)
                }
            }
            /// @ast-id 528 @src 2:10415:10891  "function _spendAllowance(address owner, address spender, uint256 value) internal virtual {..."
            function fun_spendAllowance(var_owner, var_spender, var_value)
            {
                /// @src 2:10551:10556  "owner"
                let _1 := var_owner
                let expr := var_owner
                /// @src 2:10558:10565  "spender"
                let _2 := var_spender
                let expr_1 := var_spender
                /// @src 2:10541:10566  "allowance(owner, spender)"
                let expr_2 := fun_allowance(var_owner, var_spender)
                /// @src 2:10514:10566  "uint256 currentAllowance = allowance(owner, spender)"
                let var_currentAllowance := expr_2
                /// @src 2:10580:10596  "currentAllowance"
                let _3 := expr_2
                let expr_3 := expr_2
                /// @src 2:10599:10616  "type(uint256).max"
                let expr_4 := not(0)
                /// @src 2:10580:10616  "currentAllowance < type(uint256).max"
                let expr_5 := lt(expr_2, /** @src 2:10599:10616  "type(uint256).max" */ expr_4)
                /// @src 2:10576:10885  "if (currentAllowance < type(uint256).max) {..."
                if expr_5
                {
                    /// @src 2:10636:10652  "currentAllowance"
                    let _4 := expr_2
                    let expr_6 := expr_2
                    /// @src 2:10655:10660  "value"
                    let _5 := var_value
                    let expr_7 := var_value
                    /// @src 2:10636:10660  "currentAllowance < value"
                    let expr_8 := lt(expr_2, var_value)
                    /// @src 2:10632:10762  "if (currentAllowance < value) {..."
                    if expr_8
                    {
                        /// @src 2:10714:10721  "spender"
                        let _6 := var_spender
                        let expr_9 := var_spender
                        /// @src 2:10723:10739  "currentAllowance"
                        let _7 := expr_2
                        let expr_10 := expr_2
                        /// @src 2:10741:10746  "value"
                        let _8 := var_value
                        let expr_11 := var_value
                        /// @src 0:76:157  "contract ERC20Shim is ERC20 {..."
                        let _9 := 64
                        /// @src 2:10687:10747  "ERC20InsufficientAllowance(spender, currentAllowance, value)"
                        let _10 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ mload(_9)
                        /// @src 2:10687:10747  "ERC20InsufficientAllowance(spender, currentAllowance, value)"
                        let _11 := shl(225, 0x7dc7a0d9)
                        mstore(_10, _11)
                        let _12 := 4
                        let _13 := add(_10, _12)
                        let _14 := abi_encode_address_uint256_uint256(_13, var_spender, expr_2, var_value)
                        let _15 := sub(_14, _10)
                        revert(_10, _15)
                    }
                    /// @src 2:10812:10817  "owner"
                    let _16 := var_owner
                    let expr_12 := var_owner
                    /// @src 2:10819:10826  "spender"
                    let _17 := var_spender
                    let expr_13 := var_spender
                    /// @src 2:10828:10844  "currentAllowance"
                    let _18 := expr_2
                    let expr_14 := expr_2
                    /// @src 2:10847:10852  "value"
                    let _19 := var_value
                    let expr_15 := var_value
                    /// @src 2:10828:10852  "currentAllowance - value"
                    let expr_16 := /** @src 0:76:157  "contract ERC20Shim is ERC20 {..." */ sub(/** @src 2:10828:10852  "currentAllowance - value" */ expr_2, var_value)
                    /// @src 2:10854:10859  "false"
                    let expr_17 := 0x00
                    fun__approve(var_owner, var_spender, expr_16, expr_17)
                }
            }
            /// @ast-id 782 @src 5:656:752  "function _msgSender() internal view virtual returns (address) {..."
            function fun_msgSender() -> var
            {
                /// @src 5:728:745  "return msg.sender"
                var := /** @src 5:735:745  "msg.sender" */ caller()
            }
        }
        data ".metadata" hex"a264697066735822122099efbdf9b628e3942b552f3a7d187d2809d8f5445662bf9615318a012804f2ea64736f6c63430008130033"
    }
}

Optimized IR:

Optimized IR:

Optimized IR:

Optimized IR:

Optimized IR:

Optimized IR:

Optimized IR:
