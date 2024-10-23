import Clear.State
import Clear.EVMState

open Clear Ast EVMState UInt256

namespace Clear.PrimOps

set_option autoImplicit true

@[simp]
abbrev fromBool := Bool.toUInt256

def evmAddMod (a b c : UInt256) : UInt256 :=
  if c = 0 then 0 else
  -- "All intermediate calculations of this operation are **not** subject to the 2^256 modulo."
  Fin.mod (a.val + b.val) c

def evmMulMod (a b c : UInt256) : UInt256 :=
  if c = 0 then 0 else
  -- "All intermediate calculations of this operation are **not** subject to the 2^256 modulo."
  Fin.mod (a.val * b.val) c

def evmExp (a b : UInt256) : UInt256 :=
  a ^ b.val

def evmMod (x y : UInt256) : UInt256 :=
  if y == 0 then 0 else x % y

set_option linter.unusedVariables false in
def primCall (s : State) : PrimOp → List Literal → State × List Literal
  | .Add, [a,b]               => (s, [a + b])
  | .Sub, [a,b]               => (s, [a - b])
  | .Mul, [a,b]               => (s, [a * b])
  | .Div, [a,b]               => (s, [a / b])
  | .Sdiv, [a,b]              => (s, [UInt256.sdiv a b])
  | .Mod, [a,b]               => (s, [evmMod a b])
  | .Smod, [a,b]              => (s, [UInt256.smod a b])
  | .Addmod, [a,b,c]          => (s, [evmAddMod a b c])
  | .Mulmod, [a,b,c]          => (s, [evmMulMod a b c])
  | .Exp, [a,b]               => (s, [evmExp a b])
  | .Signextend, [a,b]        => (s, [UInt256.signextend a b])
  | .Lt, [a,b]                => (s, [fromBool (a < b)])
  | .Gt, [a,b]                => (s, [fromBool (a > b)])
  | .Slt, [a,b]               => (s, [fromBool (UInt256.slt a b)])
  | .Sgt, [a,b]               => (s, [fromBool (UInt256.sgt a b)])
  | .Eq, [a,b]                => (s, [fromBool (a = b)])
  | .Iszero, [a]              => (s, [fromBool (a = 0)])
  | .And, [a,b]               => (s, [Fin.land a b])
  | .Or, [a,b]                => (s, [Fin.lor a b])
  | .Xor, [a,b]               => (s, [Fin.xor a b])
  | .Not, [a]                 => (s, [UInt256.lnot a])
  | .Byte, [a,b]              => (s, [UInt256.byteAt a b])
  | .Shl, [a,b]               => (s, [Fin.shiftLeft b a])
  | .Shr, [a,b]               => (s, [Fin.shiftRight b a])
  | .Sar, [a,b]               => (s, [UInt256.sar a b])
  | .Keccak256, [a,b]         =>
    match s.evm.keccak256 a b with
    | .some a => (s.setEvm a.snd, [a.fst])
    -- This is the hash collision case. It's essentially an unrecoverable
    -- error, and we model it similar to how we model infinite loops, except we
    -- put the error in the EVM instead, so we don't have to bother with it in
    -- the interpreter.
    | .none => (s.setEvm s.evm.addHashCollision, [0])
  | .Address, []              => (s, [s.evm.execution_env.code_owner])
  | .Balance, [a]             => (s, [s.evm.balanceOf a])
  | .Origin, []               => (s, [s.evm.execution_env.sender])
  | .Caller, []               => (s, [s.evm.execution_env.source])
  | .Callvalue, []            => (s, [s.evm.execution_env.wei_value])
  | .Calldataload, [a]        => (s, [s.evm.calldataload a])
  | .Calldatasize, []         => (s, [s.evm.execution_env.input_data.size])
  | .Calldatacopy, [a,b,c]    => (s.setEvm (s.evm.calldatacopy a b c), [])
  | .Codesize, []             => (s, [s.evm.execution_env.code.length])
  | .Codecopy, [a,b,c]        => (s.setEvm (s.evm.codeCopy a b c), [])
  | .Gasprice, []             => (s, [s.evm.execution_env.gas_price])
  | .Extcodesize, [a]         => (s, [s.evm.extCodeSize a])
  | .Extcodecopy, [a,b,c,d]   => (s.setEvm (s.evm.extCodeCopy a b c d), [])
  | .Returndatasize, []       => (s, [s.evm.returndatasize])
  | .Returndatacopy, [a,b,c]  =>
    match s.evm.returndatacopy a b c with
    | .some evm' => (s.setEvm evm', [])
    | .none => (s.setEvm (s.evm.evm_revert a c), [])
  | .Extcodehash, [a]         => (s, [s.evm.extCodeHash a])
  | .Blockhash, [a]           => (s, [s.evm.blockHash a])
  | .Coinbase, []             => (s, [s.evm.coinBase])
  | .Timestamp, []            => (s, [s.evm.timeStamp])
  | .Gaslimit, []             => (s, [s.evm.gasLimit])
  | .Chainid, []              => (s, [s.evm.chainId])
  | .Selfbalance, []          => (s, [s.evm.selfbalance])
  | .Mload, [a]               => (s, [s.evm.mload a])
  | .Mstore, [a,b]            => (s.setEvm (s.evm.mstore a b), [])
  | .Sload, [a]               => (s, [s.evm.sload a])
  | .Sstore, [a,b]            => (s.setEvm (s.evm.sstore a b), [])
  | .Msize, []                => (s, [s.evm.msize])
  | .Gas, []                  => (s, [s.evm.gas])
  | .Revert, [a,b]            => (s.setEvm (s.evm.evm_revert a b), [])
  | .Return, [a,b]            => (s.setEvm (s.evm.evm_return a b), [])
  -- TODO: These are just dummy implementations, need to be carefully rewritten.
  | .Pop, [a]                 => (s, [])
  | .Call, [a, b, c, d, e, f, g]    => (s, [])
  | .Staticcall, [a, b, c, d, e, f] => (s, [])
  | .Delegatecall, []         => (s, [])
  | .Loadimmutable, [a]       => (s, [])
  | .Log1, [a, b, c]          => (s, [])
  | .Log2, [a, b, c, d]       => (s, [])
  | .Log3, [a, b, c, d, e]    => (s, [])
  | .Log4, []                 => (s, [])
  | .Number, []               => (s, [])
  -- Since the compiler should disallow argument mismatches, it is safe to
  -- return the default here.
  | _, _                      => (s, [])

lemma EVMAdd'            : primCall s .Add [a,b]                     = (s, [a + b]) := rfl
lemma EVMSub'            : primCall s .Sub [a,b]                     = (s, [a - b]) := rfl
lemma EVMMul'            : primCall s .Mul [a,b]                     = (s, [a * b]) := rfl
lemma EVMDiv'            : primCall s .Div [a,b]                     = (s, [a / b]) := rfl
lemma EVMSdiv'           : primCall s .Sdiv [a,b]                    = (s, [UInt256.sdiv a b]) := rfl
lemma EVMMod'            : primCall s .Mod [a,b]                     = (s, [evmMod a b]) := rfl
lemma EVMSmod'           : primCall s .Smod [a,b]                    = (s, [UInt256.smod a b]) := rfl
lemma EVMAddmod'         : primCall s .Addmod [a,b,c]                = (s, [evmAddMod a b c]) := rfl
lemma EVMMulmod'         : primCall s .Mulmod [a,b,c]                = (s, [evmMulMod a b c]) := rfl
lemma EVMExp'            : primCall s .Exp [a,b]                     = (s, [evmExp a b]) := rfl
lemma EVMSignextend'     : primCall s .Signextend [a,b]              = (s, [UInt256.signextend a b]) := rfl
lemma EVMLt'             : primCall s .Lt [a,b]                      = (s, [fromBool (a < b)]) := rfl
lemma EVMGt'             : primCall s .Gt [a,b]                      = (s, [fromBool (a > b)]) := rfl
lemma EVMSlt'            : primCall s .Slt [a,b]                     = (s, [fromBool (UInt256.slt a b)]) := rfl
lemma EVMSgt'            : primCall s .Sgt [a,b]                     = (s, [fromBool (UInt256.sgt a b)]) := rfl
lemma EVMEq'             : primCall s .Eq [a,b]                      = (s, [fromBool (a = b)]) := rfl
lemma EVMIszero'         : primCall s .Iszero [a]                    = (s, [fromBool (a = 0)]) := rfl
lemma EVMAnd'            : primCall s .And [a,b]                     = (s, [Fin.land a b]) := rfl
lemma EVMOr'             : primCall s .Or [a,b]                      = (s, [Fin.lor a b]) := rfl
lemma EVMXor'            : primCall s .Xor [a,b]                     = (s, [Fin.xor a b]) := rfl
lemma EVMNot'            : primCall s .Not [a]                       = (s, [UInt256.lnot a]) := rfl
lemma EVMByte'           : primCall s .Byte [a,b]                    = (s, [UInt256.byteAt a b]) := rfl
lemma EVMShl'            : primCall s .Shl [a,b]                     = (s, [Fin.shiftLeft b a]) := rfl
lemma EVMShr'            : primCall s .Shr [a,b]                     = (s, [Fin.shiftRight b a]) := rfl
lemma EVMSar'            : primCall s .Sar [a,b]                     = (s, [UInt256.sar a b]) := rfl
lemma EVMKeccak256'      : primCall s .Keccak256 [a,b]               = match s.evm.keccak256 a b with | .some a => (s.setEvm a.snd, [a.fst]) | .none => (s.setEvm s.evm.addHashCollision, [0]) := rfl
lemma EVMAddress'        : primCall s .Address []                    = (s, ([s.evm.execution_env.code_owner] : List Literal)) := rfl
lemma EVMBalance'        : primCall s .Balance [a]                   = (s, [s.evm.balanceOf a]) := rfl
lemma EVMOrigin'         : primCall s .Origin []                     = (s, ([s.evm.execution_env.sender] : List Literal)) := rfl
lemma EVMCaller'         : primCall s .Caller []                     = (s, ([s.evm.execution_env.source] : List Literal)) := rfl
lemma EVMCallvalue'      : primCall s .Callvalue []                  = (s, [s.evm.execution_env.wei_value]) := rfl
lemma EVMCalldataload'   : primCall s .Calldataload [a]              = (s, [s.evm.calldataload a]) := rfl
lemma EVMCalldatasize'   : primCall s .Calldatasize []               = (s, ([s.evm.execution_env.input_data.size] : List Literal)) := rfl
lemma EVMCalldatacopy'   : primCall s .Calldatacopy [a,b,c]          = (s.setEvm (s.evm.calldatacopy a b c), []) := rfl
lemma EVMCodesize'       : primCall s .Codesize []                   = (s, ([s.evm.execution_env.code.length] : List Literal)) := rfl
lemma EVMCodecopy'       : primCall s .Codecopy [a,b,c]              = (s.setEvm (s.evm.codeCopy a b c), []) := rfl
lemma EVMGasprice'       : primCall s .Gasprice []                   = (s, ([s.evm.execution_env.gas_price] : List Literal)) := rfl
lemma EVMExtcodesize'    : primCall s .Extcodesize [a]               = (s, [s.evm.extCodeSize a]) := rfl
lemma EVMExtcodecopy'    : primCall s .Extcodecopy [a,b,c,d]         = (s.setEvm (s.evm.extCodeCopy a b c d), []) := rfl
lemma EVMReturndatasize' : primCall s .Returndatasize []             = (s, [s.evm.returndatasize]) := rfl
lemma EVMReturndatacopy' : primCall s .Returndatacopy [a,b,c]        = match s.evm.returndatacopy a b c with | .some evm' => (s.setEvm evm', []) | .none => (s.setEvm (s.evm.evm_revert a c), []) := rfl
lemma EVMExtcodehash'    : primCall s .Extcodehash [a]               = (s, [s.evm.extCodeHash a]) := rfl
lemma EVMBlockhash'      : primCall s .Blockhash [a]                 = (s, [s.evm.blockHash a]) := rfl
lemma EVMCoinbase'       : primCall s .Coinbase []                   = (s, ([s.evm.coinBase] : List Literal)) := rfl
lemma EVMTimestamp'      : primCall s .Timestamp []                  = (s, [s.evm.timeStamp]) := rfl
lemma EVMGaslimit'       : primCall s .Gaslimit []                   = (s, [s.evm.gasLimit]) := rfl
lemma EVMChainid'        : primCall s .Chainid []                    = (s, [s.evm.chainId]) := rfl
lemma EVMSelfbalance'    : primCall s .Selfbalance []                = (s, [s.evm.selfbalance]) := rfl
lemma EVMMload'          : primCall s .Mload [a]                     = (s, [s.evm.mload a]) := rfl
lemma EVMMstore'         : primCall s .Mstore [a,b]                  = (s.setEvm (s.evm.mstore a b), []) := rfl
lemma EVMSload'          : primCall s .Sload [a]                     = (s, [s.evm.sload a]) := rfl
lemma EVMSstore'         : primCall s .Sstore [a,b]                  = (s.setEvm (s.evm.sstore a b), []) := rfl
lemma EVMMsize'          : primCall s .Msize []                      = (s, [s.evm.msize]) := rfl
lemma EVMGas'            : primCall s .Gas []                        = (s, [s.evm.gas]) := rfl
lemma EVMRevert'         : primCall s .Revert [a, b]                 = (s.setEvm (s.evm.evm_revert a b), []) := rfl
lemma EVMReturn'         : primCall s .Return [a, b]                 = (s.setEvm (s.evm.evm_return a b), []) := rfl
lemma EVMPop'            : primCall s .Pop [a]                       = (s, []) := rfl
lemma EVMCall'           : primCall s .Call [a, b, c, d, e, f, g]    = (s, []) := rfl
lemma EVMStaticcall'     : primCall s .Staticcall [a, b, c, d, e, f] = (s, []) := rfl
lemma EVMDelegatecall'   : primCall s .Delegatecall []               = (s, []) := rfl
lemma EVMLoadimmutable'  : primCall s .Loadimmutable [a]             = (s, []) := rfl
lemma EVMLog1'           : primCall s .Log1 [a, b, c]                = (s, []) := rfl
lemma EVMLog2'           : primCall s .Log2 [a, b, c, d]             = (s, []) := rfl
lemma EVMLog3'           : primCall s .Log3 [a, b, c, d, e]          = (s, []) := rfl
lemma EVMLog4'           : primCall s .Log4 []                       = (s, []) := rfl
lemma EVMNumber'         : primCall s .Number []                     = (s, []) := rfl

end Clear.PrimOps
