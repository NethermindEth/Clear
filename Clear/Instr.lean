import Mathlib.Data.Nat.Defs
import Clear.UInt256

inductive AInstr : Type where
| STOP
| ADD
| MUL
| SUB
| DIV
| SDIV
| MOD
| SMOD
| ADDMOD
| MULMOD
| EXP
| SIGNEXTEND
| LT
| GT
| SLT
| SGT
| EQ
| ISZERO
| AND
| OR
| XOR
| NOT
| BYTE
| SHL
| SHR
| SAR
deriving DecidableEq

inductive EInstr : Type where
| KECCAK256
| ADDRESS
| BALANCE
| ORIGIN
| CALLER
| CALLVALUE
| CALLDATALOAD
| CALLDATASIZE
| CALLDATACOPY
| GASPRICE
| CODESIZE
| CODECOPY
| EXTCODESIZE
| EXTCODECOPY
| RETURNDATASIZE
| RETURNDATACOPY
| EXTCODEHASH
deriving DecidableEq

inductive BInstr : Type where
| BLOCKHASH
| COINBASE
| TIMESTAMP
| NUMBER
| PREVRANDAO
| DIFFICULTY
| GASLIMIT
| CHAINID
| SELFBALANCE
deriving DecidableEq


inductive MInstr : Type where
| POP
| MLOAD
| MSTORE
| MSTORE8
| SLOAD
| SSTORE
| PC
| MSIZE
| GAS
| PUSH (n : Fin 32)
| DUP (n : Fin 16)
| SWAP (n : Fin 16)
| LOG ( n : Fin 5)
deriving DecidableEq

inductive SInstr : Type where
| JUMP
| JUMPI
| JUMPDEST
| CREATE
| CALL
| CALLCODE
| RETURN
| DELEGATECALL
| CREATE2
| STATICCALL
| REVERT
| INVALID
| SELFDESTRUCT
deriving DecidableEq


inductive Instr where
| Arith (_ : AInstr)
| Env (_ : EInstr)
| Block (_ : BInstr)
| Memory (_ : MInstr)
deriving DecidableEq

namespace Clear.Instr

  def serializeAInstr (i : AInstr) : UInt8 :=
    open AInstr in
    match i with
    | STOP => 0
    | ADD  => 1
    | MUL  => 2
    | SUB  => 3
    | DIV  => 4
    | SDIV => 5
    | MOD  => 6
    | SMOD => 7
    | ADDMOD => 8
    | MULMOD => 9
    | EXP => 10
    | SIGNEXTEND => 11
    | AInstr.LT => 16
    | GT => 17
    | SLT => 18
    | SGT => 19
    | EQ => 20
    | ISZERO => 21
    | AND => 22
    | OR => 23
    | XOR => 24
    | NOT => 25
    | BYTE => 26
    | SHL => 27
    | SHR => 28
    | SAR => 29

  def serializeEInstr (i : EInstr) : UInt8 :=
    open EInstr in
    match i with
    | KECCAK256 => 32
    | ADDRESS => 48
    | BALANCE => 49
    | ORIGIN => 50
    | CALLER => 51
    | CALLVALUE => 52
    | CALLDATALOAD => 53
    | CALLDATASIZE => 54
    | CALLDATACOPY => 55
    | CODESIZE => 56
    | CODECOPY => 57
    | GASPRICE => 58
    | EXTCODESIZE => 59
    | EXTCODECOPY => 60
    | RETURNDATASIZE => 61
    | RETURNDATACOPY => 62
    | EXTCODEHASH => 63

  def serializeBInstr (i : BInstr) : UInt8 :=
    open BInstr in
    match i with
    | BLOCKHASH => 64
    | COINBASE => 65
    | TIMESTAMP => 66
    | NUMBER => 67
    | PREVRANDAO => 68
    | DIFFICULTY => 68
    | GASLIMIT => 69
    | CHAINID => 70
    | SELFBALANCE => 71

  def serializeMInstr (i : MInstr) : UInt8 :=
    open MInstr in
    match i with
    | POP => 80
    | MLOAD => 81
    | MSTORE => 82
    | MSTORE8 => 83
    | SLOAD => 84
    | SSTORE => 85
    | PC => 88
    | MSIZE => 89
    | GAS => 90
    | PUSH n => UInt8.ofNat (95 + n.val)
    | DUP n => UInt8.ofNat (127 + n.val)
    | SWAP n => UInt8.ofNat (143 + n.val)
    | LOG n => UInt8.ofNat (159 + n.val)

  def serializeSInstr (i : SInstr) : UInt8 :=
    open SInstr in
    match i with
    | JUMP => 86
    | JUMPI => 87
    | JUMPDEST => 91
    | CREATE => 240
    | CALL => 241
    | CALLCODE => 242
    | RETURN => 243
    | DELEGATECALL => 244
    | CREATE2 => 245
    | STATICCALL => 250
    | REVERT => 253
    | INVALID => 254
    | SELFDESTRUCT => 255

  def serializeInstr (i : Instr) : UInt8 :=
    match i with
    | Instr.Arith a => serializeAInstr a
    | Instr.Env e => serializeEInstr e
    | Instr.Block b => serializeBInstr b
    | Instr.Memory m => serializeMInstr m

   def δ (i : Instr) : Option ℕ :=
     match i with
     | Instr.Arith AInstr.STOP => some 0
     | Instr.Arith AInstr.ADD   => some 2
     | Instr.Arith AInstr.MUL  => some 2
     | Instr.Arith AInstr.SUB  => some 2
     | Instr.Arith AInstr.DIV   => some 2
     | Instr.Arith AInstr.SDIV => some 2
     | Instr.Arith AInstr.MOD  => some 2
     | Instr.Arith AInstr.SMOD => some 2
     | Instr.Arith AInstr.ADDMOD => some 3
     | Instr.Arith AInstr.MULMOD => some 3
     | Instr.Arith AInstr.EXP  => some 2
     | Instr.Arith AInstr.SIGNEXTEND => some 2
     | Instr.Arith AInstr.LT => some 2
     | Instr.Arith AInstr.GT => some 2
     | Instr.Arith AInstr.SLT => some 2
     | Instr.Arith AInstr.SGT => some 2
     | Instr.Arith AInstr.EQ => some 2
     | Instr.Arith AInstr.ISZERO => some 1
     | Instr.Arith AInstr.AND => some 2
     | Instr.Arith AInstr.OR => some 2
     | Instr.Arith AInstr.XOR => some 2
     | Instr.Arith AInstr.NOT => some 1
     | Instr.Arith AInstr.BYTE => some 2
     | Instr.Arith AInstr.SHL => some 2
     | Instr.Arith AInstr.SHR => some 2
     | Instr.Arith AInstr.SAR => some 2
     | Instr.Env EInstr.KECCAK256 => some 2
     | Instr.Env .ADDRESS => some 0
     | Instr.Env .BALANCE => some 1
     | Instr.Env .ORIGIN => some 0
     | Instr.Env .CALLER => some 0
     | Instr.Env .CALLVALUE => some 0
     | Instr.Env .CALLDATALOAD => some 1
     | Instr.Env .CALLDATASIZE => some 0
     | Instr.Env .CALLDATACOPY => some 3
     | Instr.Env .CODESIZE => some 0
     | Instr.Env .CODECOPY  => some 3
     | Instr.Env .GASPRICE => some 0
     | Instr.Env .EXTCODESIZE => some 4
     | Instr.Env .EXTCODECOPY => some 4
     | Instr.Env .RETURNDATASIZE => some 0
     | Instr.Env .RETURNDATACOPY => some 3
     | Instr.Env .EXTCODEHASH  => some 1
     | Instr.Block .BLOCKHASH  => some 1
     | Instr.Block .COINBASE => some 0
     | Instr.Block .TIMESTAMP  => some 0
     | Instr.Block .NUMBER => some 0
     | Instr.Block .PREVRANDAO  => some 0
     | Instr.Block .DIFFICULTY => some 0
     | Instr.Block .GASLIMIT => some 0
     | Instr.Block .CHAINID => some 0
     | Instr.Block .SELFBALANCE  => some 0
  --  | BASEFEE => 72
     | Instr.Memory .POP => some 1
     | Instr.Memory .MLOAD => some 2
     | Instr.Memory .MSTORE => some 2
     | Instr.Memory .MSTORE8  => some 1
     | Instr.Memory .SLOAD  => some 2
     | Instr.Memory .SSTORE  => some 2
     | Instr.Memory .PC => some 0
     | Instr.Memory .MSIZE  => some 0
     | Instr.Memory .GAS  => some 0
     | Instr.Memory (.PUSH _) => some 0
     | Instr.Memory (.DUP n) => some (n.val + 1)
     | Instr.Memory (.SWAP n) => some (n.val + 1)
     | Instr.Memory (.LOG n) => some (n.val + 2)

   def α (i : Instr) : Option ℕ :=
     match i with
     | Instr.Arith .STOP => some 0
     | Instr.Arith .ADD  => some 1
     | Instr.Arith .MUL  => some 1
     | Instr.Arith .SUB  => some 1
     | Instr.Arith .DIV  => some 1
     | Instr.Arith .SDIV => some 1
     | Instr.Arith .MOD   => some 1
     | Instr.Arith .SMOD => some 1
     | Instr.Arith .ADDMOD => some 1
     | Instr.Arith .MULMOD => some 1
     | Instr.Arith .EXP  => some 1
     | Instr.Arith .SIGNEXTEND  => some 1
     | Instr.Arith .LT => some 1
     | Instr.Arith .GT => some 1
     | Instr.Arith .SLT  => some 1
     | Instr.Arith .SGT => some 1
     | Instr.Arith .EQ => some 1
     | Instr.Arith .ISZERO => some 1
     | Instr.Arith .AND  => some 1
     | Instr.Arith .OR  => some 1
     | Instr.Arith .XOR => some 1
     | Instr.Arith .NOT  => some 1
     | Instr.Arith .BYTE  => some 1
     | Instr.Arith .SHL  => some 1
     | Instr.Arith .SHR  => some 1
     | Instr.Arith .SAR  => some 1
     | Instr.Env .KECCAK256  => some 1
     | Instr.Env .ADDRESS => some 1
     | Instr.Env .BALANCE  => some 1
     | Instr.Env .ORIGIN => some 1
     | Instr.Env .CALLER => some 1
     | Instr.Env .CALLVALUE => some 1
     | Instr.Env .CALLDATALOAD  => some 1
     | Instr.Env .CALLDATASIZE => some 1
     | Instr.Env .CALLDATACOPY => some 0
     | Instr.Env .CODESIZE  => some 1
     | Instr.Env .CODECOPY => some 0
     | Instr.Env .GASPRICE => some 1
     | Instr.Env .EXTCODESIZE  => some 1
     | Instr.Env .EXTCODECOPY => some 0
     | Instr.Env .RETURNDATASIZE  => some 1
     | Instr.Env .RETURNDATACOPY => some 0
     | Instr.Env .EXTCODEHASH => some 1
     | Instr.Block .BLOCKHASH => some 1
     | Instr.Block .COINBASE => some 1
     | Instr.Block .TIMESTAMP => some 1
     | Instr.Block .NUMBER => some 1
     | Instr.Block .PREVRANDAO => some 1
     | Instr.Block .DIFFICULTY => some 1
     | Instr.Block .GASLIMIT => some 1
     | Instr.Block .CHAINID => some 1
     | Instr.Block .SELFBALANCE => some 1
  --  | BASEFEE => 72
     | Instr.Memory .POP => some 0
     | Instr.Memory .MLOAD => some 1
     | Instr.Memory .MSTORE => some 0
     | Instr.Memory .MSTORE8 => some 0
     | Instr.Memory .SLOAD => some 1
     | Instr.Memory .SSTORE => some 0
     | Instr.Memory .PC => some 1
     | Instr.Memory .MSIZE => some 1
     | Instr.Memory .GAS => some 1
     | Instr.Memory (.PUSH _) => some 1
     | Instr.Memory (.DUP n) => some (n.val + 1)
     | Instr.Memory (.SWAP n) => some (n.val + 1)
     | Instr.Memory (.LOG n) => some (n.val + 2)

  def parseInstr (v : UInt8) : Option Instr :=
     match v with
     | 0 => some (Instr.Arith .STOP)
     | 1 => some (Instr.Arith .ADD)
     | 2 => some (Instr.Arith .MUL)
     | 3 => some (Instr.Arith .SUB)
     | 4 => some (Instr.Arith .DIV)
     | 5 => some (Instr.Arith .SDIV)
     | 6 => some (Instr.Arith .MOD)
     | 7 => some (Instr.Arith .SMOD)
     | 8 => some (Instr.Arith .ADDMOD)
     | 9 => some (Instr.Arith .MULMOD)
     | 10 => some (Instr.Arith .EXP)
     | 11 => some (Instr.Arith .SIGNEXTEND)
     | 16 => some (Instr.Arith .LT)
     | 17 => some (Instr.Arith .GT)
     | 18 => some (Instr.Arith .SLT)
     | 19 => some (Instr.Arith .SGT)
     | 20 => some (Instr.Arith .EQ)
     | 21 => some (Instr.Arith .ISZERO)
     | 22 => some (Instr.Arith .AND)
     | 23 => some (Instr.Arith .OR)
     | 24 => some (Instr.Arith .XOR)
     | 25 => some (Instr.Arith .NOT)
     | 26 => some (Instr.Arith .BYTE)
     | 27 => some (Instr.Arith .SHL)
     | 28 => some (Instr.Arith .SHR)
     | 29 => some (Instr.Arith .SAR )
     | 32 => some (Instr.Env .KECCAK256)
     | 48 => some (Instr.Env .ADDRESS)
     | 49 => some (Instr.Env .BALANCE)
     | 50 => some (Instr.Env .ORIGIN)
     | 51 => some (Instr.Env .CALLER)
     | 52 => some (Instr.Env .CALLVALUE)
     | 53 => some (Instr.Env .CALLDATALOAD)
     | 54 => some (Instr.Env .CALLDATASIZE)
     | 55 => some (Instr.Env .CALLDATACOPY)
     | 56 => some (Instr.Env .CODESIZE)
     | 57 => some (Instr.Env .CODECOPY)
     | 58 => some (Instr.Env .GASPRICE)
     | 59 => some (Instr.Env .EXTCODESIZE)
     | 60 => some (Instr.Env .EXTCODECOPY)
     | 61 => some (Instr.Env .RETURNDATASIZE)
     | 62 => some (Instr.Env .RETURNDATACOPY)
     | 63 => some (Instr.Env .EXTCODEHASH)
     | 64 => some (Instr.Block .BLOCKHASH)
     | 65 => some (Instr.Block .COINBASE)
     | 66 => some (Instr.Block .TIMESTAMP)
     | 67 => some (Instr.Block .NUMBER)
     | 68 => some (Instr.Block .DIFFICULTY)
     | 69 => some (Instr.Block .GASLIMIT)
     | 70 => some (Instr.Block .CHAINID)
     | 71 => some (Instr.Block .SELFBALANCE)
--     | 72 => some BASEFEE
     | 80 => some (Instr.Memory .POP)
     | 81 => some (Instr.Memory .MLOAD)
     | 82 => some (Instr.Memory .MSTORE)
     | 83 => some (Instr.Memory .MSTORE8)
     | 84 => some (Instr.Memory .SLOAD)
     | 85 => some (Instr.Memory .SSTORE)
     | 88 => some (Instr.Memory .PC)
     | 89 => some (Instr.Memory .MSIZE)
     | 90 => some (Instr.Memory .GAS)
     | 96 => some (Instr.Memory (.PUSH 1))
     | 97 => some (Instr.Memory (.PUSH 2))
     | 98 => some (Instr.Memory (.PUSH 3))
     | 99 => some (Instr.Memory (.PUSH 4))
     | 100 => some (Instr.Memory (.PUSH 5))
     | 101 => some (Instr.Memory (.PUSH 6))
     | 102 => some (Instr.Memory (.PUSH 7))
     | 103 => some (Instr.Memory (.PUSH 8))
     | 104 => some (Instr.Memory (.PUSH 9))
     | 105 => some (Instr.Memory (.PUSH 10))
     | 106 => some (Instr.Memory (.PUSH 11))
     | 107 => some (Instr.Memory (.PUSH 12))
     | 108 => some (Instr.Memory (.PUSH 13))
     | 109 => some (Instr.Memory (.PUSH 14))
     | 110 => some (Instr.Memory (.PUSH 15))
     | 111 => some (Instr.Memory (.PUSH 16))
     | 112 => some (Instr.Memory (.PUSH 17))
     | 113 => some (Instr.Memory (.PUSH 18))
     | 114 => some (Instr.Memory (.PUSH 19))
     | 115 => some (Instr.Memory (.PUSH 20))
     | 116 => some (Instr.Memory (.PUSH 21))
     | 117 => some (Instr.Memory (.PUSH 22))
     | 118 => some (Instr.Memory (.PUSH 23))
     | 119 => some (Instr.Memory (.PUSH 24))
     | 120 => some (Instr.Memory (.PUSH 25))
     | 121 => some (Instr.Memory (.PUSH 26))
     | 122 => some (Instr.Memory (.PUSH 27))
     | 123 => some (Instr.Memory (.PUSH 28))
     | 124 => some (Instr.Memory (.PUSH 29))
     | 125 => some (Instr.Memory (.PUSH 30))
     | 126 => some (Instr.Memory (.PUSH 31))
     | 127 => some (Instr.Memory (.PUSH 32))
     | 128 => some (Instr.Memory (.DUP 1))
     | 129 => some (Instr.Memory (.DUP 2))
     | 130 => some (Instr.Memory (.DUP 3))
     | 131 => some (Instr.Memory (.DUP 4))
     | 132 => some (Instr.Memory (.DUP 5))
     | 133 => some (Instr.Memory (.DUP 6))
     | 134 => some (Instr.Memory (.DUP 7))
     | 135 => some (Instr.Memory (.DUP 8))
     | 136 => some (Instr.Memory (.DUP 9))
     | 137 => some (Instr.Memory (.DUP 10))
     | 138 => some (Instr.Memory (.DUP 11))
     | 139 => some (Instr.Memory (.DUP 12))
     | 140 => some (Instr.Memory (.DUP 13))
     | 141 => some (Instr.Memory (.DUP 14))
     | 142 => some (Instr.Memory (.DUP 15))
     | 143 => some (Instr.Memory (.DUP 16))
     | 144 => some (Instr.Memory (.SWAP 1))
     | 145 => some (Instr.Memory (.SWAP 2))
     | 146 => some (Instr.Memory (.SWAP 3))
     | 147 => some (Instr.Memory (.SWAP 4))
     | 148 => some (Instr.Memory (.SWAP 5))
     | 149 => some (Instr.Memory (.SWAP 6))
     | 150 => some (Instr.Memory (.SWAP 7))
     | 151 => some (Instr.Memory (.SWAP 8))
     | 152 => some (Instr.Memory (.SWAP 9))
     | 153 => some (Instr.Memory (.SWAP 10))
     | 154 => some (Instr.Memory (.SWAP 11))
     | 155 => some (Instr.Memory (.SWAP 12))
     | 156 => some (Instr.Memory (.SWAP 13))
     | 157 => some (Instr.Memory (.SWAP 14))
     | 158 => some (Instr.Memory (.SWAP 15))
     | 159 => some (Instr.Memory (.SWAP 16))
     | 169 => some (Instr.Memory (.LOG 1))
     | 170 => some (Instr.Memory (.LOG 2))
     | 171 => some (Instr.Memory (.LOG 3))
     | 174 => some (Instr.Memory (.LOG 4))
     | 175 => some (Instr.Memory (.LOG 5))
     | _   => none

def ofByteArray (b : ByteArray) : List Instr :=
  b.foldl (λ ac i => match parseInstr i with
                     | some v => v :: ac
                     | _ => ac) []

end Clear.Instr
