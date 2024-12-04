import Mathlib.Data.Finmap
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Intervals
import Clear.Ast
import Clear.Instr
import Clear.UInt256
import Clear.Wheels

set_option linter.setOption false
set_option pp.coercions false

set_option maxHeartbeats 700000
set_option maxRecDepth 800

open Clear Instr UInt256

def Array.extractFill {A : Type} [Zero A] (v₀ size : ℕ) (arr : Array A) : Array A :=
  let return_size := v₀ + size - 1
  if arr.size < return_size
  then
    let zeros := List.toArray (List.replicate (return_size - arr.size - 1) 0)
    let arr1 := zeros.append arr
    arr1.extract v₀ return_size
  else arr.extract v₀ return_size

def ByteArray.extractBytes (v₀ : ℕ) (size : ℕ) (arr : ByteArray) : ByteArray :=
  ByteArray.mk (Array.extractFill v₀ size arr.data)

def ByteArray.byteArrayToUInt256 (μ₀ : UInt256) (size : ℕ) (Id : ByteArray) : UInt256 :=
  open Array in
  let v₀ := μ₀.val
  let arr : ByteArray := extractBytes v₀ size Id
  let arr1 : Array UInt8 := arr.data
  -- converting to big endian
  let step p v := (p.1 - 8, Fin.lor p.2 (Nat.shiftLeft v.val p.1))
  let r : (ℕ × UInt256) := Array.foldl step ((size - 1) * 8, 0) arr1
  r.2


namespace Clear

-- 2^160 https://www.wolframalpha.com/input?i=2%5E160
def Address.size : Nat := 1461501637330902918203684832716283019655932542976

abbrev Address : Type := Fin Address.size

instance : Inhabited Address := ⟨Fin.ofNat 0⟩

def Address.ofNat {n : ℕ} : Address := Fin.ofNat n
def Address.ofUInt256 (v : UInt256) : Address := Fin.ofNat (v.val  % Address.size)
instance {n : Nat} : OfNat Address n := ⟨Fin.ofNat n⟩

instance byteArrayDecEq : DecidableEq ByteArray := λ xs ys => by {
  rcases xs with ⟨ xs1 ⟩ ; rcases ys with ⟨ ys1 ⟩
  simp
  apply decEq
}

-- definition of the account data

structure Account : Type where
  balance   : UInt256
  code      : List Instr
  code_hash : UInt256
  storage   : Finmap (λ _ : UInt256 => UInt256)
deriving DecidableEq

instance : Inhabited Account := ⟨ Account.mk 0 [] 0 default ⟩

def Account.lookupStorage (act : Account) (k : UInt256) : UInt256 :=
  match act.storage.lookup k with
  | .some val => val
  | _ => 0

def Account.updateStorage (act : Account) (k v : UInt256) : Account :=
  if v == 0 then
    { act with storage := act.storage.erase k }
  else
    { act with storage := Finmap.insert k v act.storage}

-- definition of the machine state

abbrev Memory := Finmap (λ _ : UInt256 ↦ UInt8)

structure MachineState : Type where
  memory        : Memory
  max_address   : UInt256
  gas_available : UInt256
  return_data   : List UInt256
deriving DecidableEq

instance : Inhabited MachineState := ⟨ MachineState.mk ∅ 0 0 [] ⟩

-- @langfield: Nit, but definitions should be camelCase.

def UInt256.offsets : List ℕ :=
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
  17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]

lemma UInt256.offsets_def : offsets = List.range 32 := by
  repeat rw [ List.range_succ_eq_map ]
  unfold offsets
  simp

lemma max_of_offsets_lt_32 : offsets.maximum < 32 := by decide
lemma min_of_offsets_eq_0 : offsets.minimum = 0 := by decide

lemma mem_offsets : ∀ {n}, n ∈ offsets ↔ n < 32 := by
  intro n
  rw [offsets_def]
  simp

@[simp]
lemma mem_offsets_of_lt_32 : ∀ {n}, n < 32 → n ∈ offsets :=
  mem_offsets.mpr

lemma lt_32_of_mem_offsets : ∀ {n}, n ∈ offsets → n < 32 :=
  mem_offsets.mp

-- List.Ico not yet in mathlib
lemma UInt256.offsets_eq_Ico : offsets = List.Ico 0 32 := by
  unfold List.Ico
  rw [ List.range'_eq_map_range, offsets_def ]
  simp

-- lemma UInt256.offsets_at_addr :
--   ∀ (addr : UInt256),
--   offsets.map (addr + ↑·) = List.Ico addr.val (addr.val + 32) := by
--   intro addr
--   rw [offsets_eq_Ico, List.Ico.map_add 0 32 addr, zero_add, add_comm]

lemma UInt256.mem_offsets_iff_mem_Ico : ∀ {n}, n ∈ offsets ↔ n ∈ Set.Ico 0 32 := by
  intro n
  apply Iff.intro
  · intro mem
    simp
    exact mem_offsets.mp mem
  · intro mem
    simp at mem
    exact mem_offsets.mpr mem

lemma UInt256.offsetted_addresses (addr : UInt256) : ∀ {n},
  (h : n ∈ offsets) → addr + ↑n ∈ offsets.map (addr + ↑·) := by
  intro n h
  exact List.mem_map_of_mem (addr + ↑·) h

-- lemma UInt256.word_addresses (addr : UInt256) :
--   Set.MapsTo (addr + ↑·) (Set.Ico 0 32) (Set.Ico addr (addr + 32)) := by
--   have : (addr + ↑·) '' (Set.Ico 0 32) = Set.Ico addr (addr + 32) := by
--     dsimp [Set.image]
--     conv => rhs; rw [← Set.Ico_def]

--     sorry

--   rw [← this]
--   exact Set.mapsTo_image (addr + ↑·) (Set.Ico 0 32)


-- lemma UInt256.same_address_of_offsetted_addresses (addr addr': UInt256) {n} :
--   (h : n ∈ offsets) →
--   addr' + ↑n ∈ offsets.map (addr + ↑·) →
--   addr' = addr := by
--   intro h mem
--   simp at mem
--   sorry

-- lemma UInt256.addresses_of (addr : UInt256) {a} :
--   a ∈ offsets.map (addr + ↑·) ↔ a ∈ Set.Ico addr (addr + 32) := by
--   sorry

namespace UInt256

def range' (start : UInt256) (len : ℕ) (step : UInt256 := 1) : List UInt256 :=
  match start, len with
  | _, 0 => []
  | s, n + 1 => s :: range' (s + step) n step

@[simp]
lemma range'_zero {s step : UInt256} : range' s 0 step = [] := by
  unfold range'
  rfl

@[simp]
lemma range'_one {s step : UInt256} : range' s 1 step = [s] := by
  unfold range'
  simp

lemma range'_succ (start : UInt256) (len : ℕ) (step : UInt256) :
  range' start (len + 1) step =
    start :: range' (start + step) len step := by
  conv =>
    lhs
    unfold range'
    simp

-- lemma range'_succ' (start : UInt256) (len : ℕ) (step : UInt256) (k : ℕ) [NeZero k] :
--   range' start (len + k) step =
--     start :: range' (start + step) (len + k - 1) step := by
--   admit

lemma map_add_range' (a) : ∀ s n step,
  List.map (a + ·) (range' s n step) =
    range' (a + s) n step
  | _, 0, _ => by simp
  | s, n+1, step => by
    unfold range'
    simp [map_add_range', add_assoc]

def offsets_at (addr : UInt256) : List UInt256 :=
  range' addr 32 1

def words_at (addr : UInt256) (n : ℕ) : List UInt256 :=
  range' addr n 32

end UInt256

lemma splice_toBytes! (v : UInt256) : toBytes! v =
  [ (toBytes! v)[0],   (toBytes! v)[1],   (toBytes! v)[2],   (toBytes! v)[3]
  , (toBytes! v)[4],   (toBytes! v)[5],   (toBytes! v)[6],   (toBytes! v)[7]
  , (toBytes! v)[8],   (toBytes! v)[9],   (toBytes! v)[10],  (toBytes! v)[11]
  , (toBytes! v)[12],  (toBytes! v)[13],  (toBytes! v)[14],  (toBytes! v)[15]
  , (toBytes! v)[16],  (toBytes! v)[17],  (toBytes! v)[18],  (toBytes! v)[19]
  , (toBytes! v)[20],  (toBytes! v)[21],  (toBytes! v)[22],  (toBytes! v)[23]
  , (toBytes! v)[24],  (toBytes! v)[25],  (toBytes! v)[26],  (toBytes! v)[27]
  , (toBytes! v)[28],  (toBytes! v)[29],  (toBytes! v)[30],  (toBytes! v)[31]
  ] := by
  apply List.ext_get
  · simp
  · intro n h₁ h₂
    simp at h₂
    have h_offset := mem_offsets_of_lt_32 h₂
    fin_cases h_offset
    all_goals aesop

abbrev Entry := UInt256 × UInt8

@[simp]
def memInsert (entry : Entry) (mem : Memory) : Memory :=
  Function.uncurry mem.insert entry

@[simp]
def mkEntries (addr data : UInt256) : List Entry :=
  let addrs := offsets.map (addr + ↑·)
  addrs.zip (UInt256.toBytes! data)

def Memory.maxWords := 3618502788666131106986593281521497120414687020801267626233049500247285301247

def Memory.maxWords_def : Memory.maxWords = (⊤ : UInt256) / 32 := by
  rw [maxWords, Fin.top_eq_last]
  simp

def MachineState.updateMemory (m : MachineState) (addr v : UInt256) : MachineState :=
  {m with memory := List.foldr (init := m.memory) memInsert <| mkEntries addr v
          max_address := max addr m.max_address }

def Memory.lookupByte (m : Memory) (addr : UInt256) : UInt8 :=
  (m.lookup addr).get!

def Memory.lookupWord (m : Memory) (addr : UInt256) : UInt256 :=
--  UInt256.fromBytes! (offsets.map λ i ↦ (m.memory.lookup (addr + i)).get!)
  UInt256.fromBytes! $ offsets.map $ m.lookupByte ∘ (addr + ↑·)

def MachineState.setReturnData (m : MachineState) (r : List UInt256) : MachineState :=
  {m with return_data := r}

def MachineState.msize (m : MachineState) : UInt256 :=
  m.max_address

-- definition of the blocks

structure BlockHeader : Type where
  parent_hash : UInt256
  beneficiary : Address
  timestamp   : UInt256
  number      : UInt256
  difficulty  : UInt256
  gas_limit   : UInt256
  chain_id    : UInt256
deriving DecidableEq

instance : Inhabited BlockHeader :=
  ⟨ BlockHeader.mk 0 default 0 0 0 0 0 ⟩

structure EVMBlock : Type where
  header : BlockHeader
deriving DecidableEq

instance : Inhabited EVMBlock := ⟨ EVMBlock.mk default ⟩

-- definition of the execution environment

structure ExecutionEnv : Type where
  code_owner : Address
  sender     : Address
  source     : Address
  wei_value  : UInt256
  input_data : ByteArray
  code       : List Instr
  gas_price  : ℕ
  header     : BlockHeader
deriving DecidableEq

instance : Inhabited ExecutionEnv :=
  ⟨ ExecutionEnv.mk default default default 0 default [] 0 default ⟩

-- definition of the evm state

structure EVMState : Type where
  -- account map
  account_map : Finmap (λ _ : Address => Account)
  -- machine state
  machine_state : MachineState
  -- execution environment
  execution_env : ExecutionEnv
  -- keccak map
  keccak_map   : Finmap (λ _ : List UInt256 => UInt256)
  keccak_range : List UInt256
  used_range   : Finset UInt256
  -- blocks
  blocks : List EVMBlock
  hash_collision : Bool
deriving DecidableEq

instance : Inhabited EVMState :=
  ⟨ ∅ , default, default , ∅ , default, ∅ , default , False ⟩

abbrev EVM := EVMState

def preserved : EVMState → EVMState → Prop :=
  (Eq on EVMState.account_map) ∩
  (Eq on EVMState.hash_collision) ∩
  (Eq on EVMState.execution_env)

-- functions for querying balance

namespace EVMState

section

open Array ByteArray

-- | Add an error to the EVMState indicating that we hit a hash collision in `keccak256`.
def addHashCollision (σ : EVMState) : EVMState := { σ with hash_collision := true }

-- def hasHashCollision (σ : EVMState) : Prop := σ.hash_collision = true

-- instance : DecidablePred hasHashCollision := λ σ ↦
--   decidable_of_bool σ.hash_collision (by unfold hasHashCollision; simp)

def lookupAccount (σ : EVMState) (addr : Address) : Option Account :=
  σ.account_map.lookup addr

def updateAccount (σ : EVMState) (addr : Address) (act : Account) : EVMState :=
  {σ with account_map := Finmap.insert addr act σ.account_map}

def balanceOf (σ : EVMState) (k : UInt256) : UInt256 :=
  let addr : Address := Address.ofUInt256 k
  match Finmap.lookup addr σ.account_map with
  | .some act => act.balance
  | .none => Fin.ofNat 0

-- functions for accessing memory

def updateMemory (σ : EVMState) (addr v : UInt256) : EVMState :=
  {σ with machine_state := σ.machine_state.updateMemory addr v}

-- functions for manipulating call data

def calldataload (σ : EVMState) (v : UInt256) : UInt256 :=
  byteArrayToUInt256 v 32 σ.execution_env.input_data

def calldatacopy (σ : EVMState) (mstart datastart s : UInt256) : EVMState :=
  let size := s.val
  let arr := extractBytes datastart.val size σ.execution_env.input_data
  let r := arr.foldl (λ (sa , j) i => (EVMState.updateMemory sa j i.val, j + 1)) (σ , mstart)
  r.1

def mkInterval (ms : Memory) (p : UInt256) (n : ℕ) : List UInt256 :=
  (words_at p n).map ms.lookupWord

def mkInterval' (ms : Memory) (start last : UInt256) : List UInt8 :=
  List.map ms.lookupByte <| range' start (last - start)

lemma interval'_eq_interval {ms} {start last} (d : ℕ) :
  (d_ne_zero : d ≠ 0) → (div : (d * 32) * Fin.div (last - start) (Nat.toUInt256 d * 32) = last - start) →
  List.map (Nat.toUInt256 ∘ fromBytes!) (List.toChunks 32 (mkInterval' ms start last)) =
    mkInterval ms start d := by
  sorry

def keccak256 (σ : EVMState) (p n : UInt256) : Option (UInt256 × EVMState) :=
  let interval : List UInt256 := List.map (Nat.toUInt256 ∘ fromBytes!) (List.toChunks 32 (mkInterval' σ.machine_state.memory p n))
  match Finmap.lookup interval σ.keccak_map with
  | .some val => .some (val, σ)
  | .none     =>
    match σ.keccak_range.partition (λ x => x ∈ σ.used_range) with
    | (_,(r :: rs)) =>
      .some (r, {σ with keccak_map := σ.keccak_map.insert interval r,
                        keccak_range := rs,
                        used_range := {r} ∪ σ.used_range })
    | (_, []) => .none

-- code copy

def codeCopy (σ : EVMState) (mstart cstart s : UInt256) : EVMState :=
  let Ib : ByteArray := ByteArray.mk ((σ.execution_env.code.map serializeInstr).toArray)
  let Ib1 := extractBytes cstart.val s.val Ib
  let r := Ib1.foldl (λ (sa, j) i => (EVMState.updateMemory sa j i.toUInt256, j + 1)) (σ, mstart)
  r.1

def extCodeSize (σ : EVMState) (a : UInt256) : UInt256 :=
  let addr := Address.ofUInt256 a
  match σ.lookupAccount addr with
  | .some act => act.code.length
  | .none => 0

def extCodeCopy (σ : EVMState) (act mstart cstart s : UInt256) : EVMState :=
  let addr := Address.ofUInt256 act
  match σ.lookupAccount addr with
  | .some act1 =>
    let Ib : ByteArray := ByteArray.mk ((act1.code.map serializeInstr).toArray)
    let Ib1 := extractBytes cstart.val s.val Ib
    let r := Ib1.foldl (λ (sa , j) i => (EVMState.updateMemory sa j i.toUInt256, j + 1)) (σ, mstart)
    r.1
  | _ =>
    let size := s.val
    let r := size.fold (λ _ (sa , j) => (EVMState.updateMemory sa j 0, j + 1)) (σ, mstart)
    r.1

def extCodeHash (σ : EVMState) (v : UInt256) : UInt256 :=
  let addr := Address.ofUInt256 v
  match σ.lookupAccount addr with
  | .some act => act.code_hash
  | _ => 0

-- blocks

def blockHash (σ : EVMState) (block_number : UInt256) : UInt256 :=
  let v := σ.execution_env.header.number
  if v ≤ block_number ∨ v > block_number + 256 then 0
  else
    let bs := σ.blocks.map (λ b => b.header.parent_hash)
    let pos := v - block_number
    bs.getD pos 0

def coinBase (σ : EVMState) : Address :=
  σ.execution_env.header.beneficiary

def timeStamp (σ : EVMState) : UInt256 :=
  σ.execution_env.header.timestamp

def number (σ : EVMState) : UInt256 :=
  σ.execution_env.header.number

def difficulty (σ : EVMState) : UInt256 :=
  σ.execution_env.header.difficulty

def gasLimit (σ : EVMState) : UInt256 :=
  σ.execution_env.header.gas_limit

def chainId (σ : EVMState) : UInt256 :=
  σ.execution_env.header.chain_id

def selfbalance (σ : EVMState) : UInt256 :=
  let addr := σ.execution_env.code_owner
  match Finmap.lookup addr σ.account_map with
  | .some act => act.balance
  | .none => Fin.ofNat 0

-- memory and storage operations

def mload (σ : EVMState) (spos : UInt256) : UInt256 :=
  σ.machine_state.memory.lookupWord spos

def mstore (σ : EVMState) (spos sval : UInt256) : EVMState :=
  σ.updateMemory spos sval

def mstore8 (σ : EVMState) (spos sval : UInt256) : EVMState :=
  σ.updateMemory spos (Fin.ofNat (sval.val % 256))

def sload (σ : EVMState) (spos : UInt256) : UInt256 :=
  match σ.lookupAccount σ.execution_env.code_owner with
  | .some act => act.lookupStorage spos
  | .none => 0

def sstore (σ : EVMState) (spos sval : UInt256) : EVMState :=
  match σ.lookupAccount σ.execution_env.code_owner with
  | .some act =>
    let σ' := σ.updateAccount σ.execution_env.code_owner (act.updateStorage spos sval)
    {σ' with used_range := {spos} ∪ σ'.used_range}
  | .none => σ

def msize (σ : EVMState) : UInt256 :=
  σ.machine_state.msize

def gas (σ : EVMState) : UInt256 :=
  σ.machine_state.gas_available

def returndatasize (σ : EVMState) : UInt256 :=
  σ.machine_state.return_data.length

def returndataat (σ : EVMState) (pos : UInt256) : UInt256 :=
  σ.machine_state.return_data.getD pos.val 0

def returndatacopy (σ : EVMState) (mstart rstart s : UInt256) : Option EVMState :=
  let pos := rstart.val + s.val
  if pos ≥ UInt256.size ∨ pos ≥ σ.returndatasize.val then .none
  else
    let arr := σ.machine_state.return_data.toArray
    let rdata := arr.extract rstart.val (rstart.val + s.val - 1)
    let s := rdata.data.foldr (λ v (ac,p) => (ac.updateMemory p v, p +1)) (σ , mstart)
    .some s.1

def evm_return (σ : EVMState) (mstart s : UInt256) : EVMState :=
  let arr := σ.machine_state.return_data.toArray
  let vals := extractFill mstart.val s.val arr
  {σ with machine_state := σ.machine_state.setReturnData vals.data}

def evm_revert (σ : EVMState) (mstart s : UInt256) : EVMState :=
  σ.evm_return mstart s

end

section Memory

variable {addr addr' : UInt256}
variable {ms : MachineState}
variable {val val' : UInt256}
variable {entry : Entry}
variable {es es' : List Entry}

@[simp]
lemma frontflip : (λ b a ↦ memInsert a b) = flip memInsert := by
  unfold flip
  ext
  simp

@[simp]
lemma backflip : (λ b a ↦ flip memInsert a b) = memInsert := by
  unfold flip
  ext
  simp

lemma foldr_mem_nil {init : Memory} :
  List.foldr memInsert (List.foldr memInsert init []) [] = init := by
  simp

lemma memInsert_memInsert {m : Memory} {a b : UInt8} :
  memInsert ⟨addr, a⟩ (memInsert ⟨addr, b⟩ m) =
    memInsert ⟨addr, a⟩ m := by
  simp

lemma memInsert_memInsert_of_ne {m : Memory} {a b : UInt8} :
  (h : addr' ≠ addr) →
  memInsert ⟨addr, a⟩ (memInsert ⟨addr', b⟩ m) =
    memInsert ⟨addr', b⟩ (memInsert ⟨addr, a⟩ m) := by
  intro h
  simp
  exact Finmap.insert_insert_of_ne m h

lemma foldr_memInsert_reverse {init : Memory} :
  List.foldr memInsert init (mkEntries addr val) =
    List.foldr memInsert init (mkEntries addr val).reverse := by
  simp only [mkEntries]
  rw [ splice_toBytes! val ]
  unfold offsets

  simp only [List.map, List.zip, List.zipWith, List.reverse, List.reverseAux]
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  rw [List.foldr_cons]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[1]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[2]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[2]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[3]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[3]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[3]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[4]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[4]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[4]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[4]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[5]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[5]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[5]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[5]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[5]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[6]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[6]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[6]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[6]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[6]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[6]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[7]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[7]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[7]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[7]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[7]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[7]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[7]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[8]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[8]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[8]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[8]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[8]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[8]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[8]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[8]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[9]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[9]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[9]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[9]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[9]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[9]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[9]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[9]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[9]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[10]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[10]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[10]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[10]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[10]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[10]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[10]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[10]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[10]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[10]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[11]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[11]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[11]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[11]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[11]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[11]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[11]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[11]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[11]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[11]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[11]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[12]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[12]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[12]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[12]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[12]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[12]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[12]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[12]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[12]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[12]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[12]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[12]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[13]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[14]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[15]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[16]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[17]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[18]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[19]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[20]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[21]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[22]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[23]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[24]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[25]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[26]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[27]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[28]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[29]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[30]) (by simp)
     ]
  rw [ List.foldr_cons
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     , memInsert_memInsert_of_ne (b := (toBytes! val)[31]) (by simp)
     ]
  rw [ ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     , ← List.foldr_cons (f := memInsert), ← List.foldr_cons (f := memInsert)
     ]

lemma foldl_memInsert_reverse {init : Memory} :
  List.foldl (flip memInsert) init (mkEntries addr val) =
    List.foldl (flip memInsert) init (mkEntries addr val).reverse := by
  rw [ List.foldl_reverse, backflip, foldr_memInsert_reverse, List.foldr_reverse, frontflip]

lemma foldr_memInsert_eq_foldl_memInsert {init : Memory} :
  List.foldr memInsert init (mkEntries addr val) =
    List.foldl (flip memInsert) init (mkEntries addr val) := by
  rw [ foldr_memInsert_reverse, List.foldr_reverse, frontflip]

end Memory

section MachineState

variable {addr addr' : UInt256}
variable {ms : MachineState}
variable {val val' : UInt256}
variable {entry : Entry}
variable {es es' : List Entry}

lemma update_update :
  (ms.updateMemory addr val).updateMemory addr val' = ms.updateMemory addr val' := by
  unfold MachineState.updateMemory
  simp

  rw [ ← mkEntries, ← mkEntries ]
  rw [ foldr_memInsert_eq_foldl_memInsert ]

  conv => rhs; rw [ foldr_memInsert_eq_foldl_memInsert, foldl_memInsert_reverse ]
  rw [ mkEntries, mkEntries ]

  rw [ splice_toBytes! val, splice_toBytes! val' ]
  unfold offsets

  unfold flip
  simp only [List.map, List.zip, List.zipWith]
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]

  rw [ List.foldr_cons, List.foldl_cons, memInsert_memInsert]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 2) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 3) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 3) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 4) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 4) (by simp), memInsert_memInsert_of_ne (addr := addr + 4) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 5) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 5) (by simp), memInsert_memInsert_of_ne (addr := addr + 5) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 5) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 6) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 6) (by simp), memInsert_memInsert_of_ne (addr := addr + 6) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 6) (by simp), memInsert_memInsert_of_ne (addr := addr + 6) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 7) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 7) (by simp), memInsert_memInsert_of_ne (addr := addr + 7) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 7) (by simp), memInsert_memInsert_of_ne (addr := addr + 7) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 7) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 8) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 8) (by simp), memInsert_memInsert_of_ne (addr := addr + 8) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 8) (by simp), memInsert_memInsert_of_ne (addr := addr + 8) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 8) (by simp), memInsert_memInsert_of_ne (addr := addr + 8) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 9) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 9) (by simp), memInsert_memInsert_of_ne (addr := addr + 9) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 9) (by simp), memInsert_memInsert_of_ne (addr := addr + 9) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 9) (by simp), memInsert_memInsert_of_ne (addr := addr + 9) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 9) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 10) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 10) (by simp), memInsert_memInsert_of_ne (addr := addr + 10) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 10) (by simp), memInsert_memInsert_of_ne (addr := addr + 10) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 10) (by simp), memInsert_memInsert_of_ne (addr := addr + 10) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 10) (by simp), memInsert_memInsert_of_ne (addr := addr + 10) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 11) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 11) (by simp), memInsert_memInsert_of_ne (addr := addr + 11) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 11) (by simp), memInsert_memInsert_of_ne (addr := addr + 11) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 11) (by simp), memInsert_memInsert_of_ne (addr := addr + 11) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 11) (by simp), memInsert_memInsert_of_ne (addr := addr + 11) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 11) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 12) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 12) (by simp), memInsert_memInsert_of_ne (addr := addr + 12) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 12) (by simp), memInsert_memInsert_of_ne (addr := addr + 12) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 12) (by simp), memInsert_memInsert_of_ne (addr := addr + 12) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 12) (by simp), memInsert_memInsert_of_ne (addr := addr + 12) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 12) (by simp), memInsert_memInsert_of_ne (addr := addr + 12) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 13) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 13) (by simp), memInsert_memInsert_of_ne (addr := addr + 13) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 13) (by simp), memInsert_memInsert_of_ne (addr := addr + 13) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 13) (by simp), memInsert_memInsert_of_ne (addr := addr + 13) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 13) (by simp), memInsert_memInsert_of_ne (addr := addr + 13) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 13) (by simp), memInsert_memInsert_of_ne (addr := addr + 13) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 13) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 14) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 14) (by simp), memInsert_memInsert_of_ne (addr := addr + 14) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 14) (by simp), memInsert_memInsert_of_ne (addr := addr + 14) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 14) (by simp), memInsert_memInsert_of_ne (addr := addr + 14) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 14) (by simp), memInsert_memInsert_of_ne (addr := addr + 14) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 14) (by simp), memInsert_memInsert_of_ne (addr := addr + 14) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 14) (by simp), memInsert_memInsert_of_ne (addr := addr + 14) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 15) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 15) (by simp), memInsert_memInsert_of_ne (addr := addr + 15) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 15) (by simp), memInsert_memInsert_of_ne (addr := addr + 15) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 15) (by simp), memInsert_memInsert_of_ne (addr := addr + 15) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 15) (by simp), memInsert_memInsert_of_ne (addr := addr + 15) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 15) (by simp), memInsert_memInsert_of_ne (addr := addr + 15) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 15) (by simp), memInsert_memInsert_of_ne (addr := addr + 15) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 15) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 16) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 16) (by simp), memInsert_memInsert_of_ne (addr := addr + 16) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 16) (by simp), memInsert_memInsert_of_ne (addr := addr + 16) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 16) (by simp), memInsert_memInsert_of_ne (addr := addr + 16) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 16) (by simp), memInsert_memInsert_of_ne (addr := addr + 16) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 16) (by simp), memInsert_memInsert_of_ne (addr := addr + 16) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 16) (by simp), memInsert_memInsert_of_ne (addr := addr + 16) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 16) (by simp), memInsert_memInsert_of_ne (addr := addr + 16) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 17) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 17) (by simp), memInsert_memInsert_of_ne (addr := addr + 17) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 17) (by simp), memInsert_memInsert_of_ne (addr := addr + 17) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 17) (by simp), memInsert_memInsert_of_ne (addr := addr + 17) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 17) (by simp), memInsert_memInsert_of_ne (addr := addr + 17) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 17) (by simp), memInsert_memInsert_of_ne (addr := addr + 17) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 17) (by simp), memInsert_memInsert_of_ne (addr := addr + 17) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 17) (by simp), memInsert_memInsert_of_ne (addr := addr + 17) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 17) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 18) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 18) (by simp), memInsert_memInsert_of_ne (addr := addr + 18) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 18) (by simp), memInsert_memInsert_of_ne (addr := addr + 18) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 18) (by simp), memInsert_memInsert_of_ne (addr := addr + 18) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 18) (by simp), memInsert_memInsert_of_ne (addr := addr + 18) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 18) (by simp), memInsert_memInsert_of_ne (addr := addr + 18) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 18) (by simp), memInsert_memInsert_of_ne (addr := addr + 18) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 18) (by simp), memInsert_memInsert_of_ne (addr := addr + 18) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 18) (by simp), memInsert_memInsert_of_ne (addr := addr + 18) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 19) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 19) (by simp), memInsert_memInsert_of_ne (addr := addr + 19) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 19) (by simp), memInsert_memInsert_of_ne (addr := addr + 19) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 19) (by simp), memInsert_memInsert_of_ne (addr := addr + 19) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 19) (by simp), memInsert_memInsert_of_ne (addr := addr + 19) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 19) (by simp), memInsert_memInsert_of_ne (addr := addr + 19) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 19) (by simp), memInsert_memInsert_of_ne (addr := addr + 19) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 19) (by simp), memInsert_memInsert_of_ne (addr := addr + 19) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 19) (by simp), memInsert_memInsert_of_ne (addr := addr + 19) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 19) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 20) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 20) (by simp), memInsert_memInsert_of_ne (addr := addr + 20) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 20) (by simp), memInsert_memInsert_of_ne (addr := addr + 20) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 20) (by simp), memInsert_memInsert_of_ne (addr := addr + 20) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 20) (by simp), memInsert_memInsert_of_ne (addr := addr + 20) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 20) (by simp), memInsert_memInsert_of_ne (addr := addr + 20) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 20) (by simp), memInsert_memInsert_of_ne (addr := addr + 20) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 20) (by simp), memInsert_memInsert_of_ne (addr := addr + 20) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 20) (by simp), memInsert_memInsert_of_ne (addr := addr + 20) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 20) (by simp), memInsert_memInsert_of_ne (addr := addr + 20) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 21) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 21) (by simp), memInsert_memInsert_of_ne (addr := addr + 21) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 21) (by simp), memInsert_memInsert_of_ne (addr := addr + 21) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 21) (by simp), memInsert_memInsert_of_ne (addr := addr + 21) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 21) (by simp), memInsert_memInsert_of_ne (addr := addr + 21) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 21) (by simp), memInsert_memInsert_of_ne (addr := addr + 21) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 21) (by simp), memInsert_memInsert_of_ne (addr := addr + 21) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 21) (by simp), memInsert_memInsert_of_ne (addr := addr + 21) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 21) (by simp), memInsert_memInsert_of_ne (addr := addr + 21) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 21) (by simp), memInsert_memInsert_of_ne (addr := addr + 21) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 21) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 22) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 22) (by simp), memInsert_memInsert_of_ne (addr := addr + 22) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 22) (by simp), memInsert_memInsert_of_ne (addr := addr + 22) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 22) (by simp), memInsert_memInsert_of_ne (addr := addr + 22) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 22) (by simp), memInsert_memInsert_of_ne (addr := addr + 22) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 22) (by simp), memInsert_memInsert_of_ne (addr := addr + 22) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 22) (by simp), memInsert_memInsert_of_ne (addr := addr + 22) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 22) (by simp), memInsert_memInsert_of_ne (addr := addr + 22) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 22) (by simp), memInsert_memInsert_of_ne (addr := addr + 22) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 22) (by simp), memInsert_memInsert_of_ne (addr := addr + 22) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 22) (by simp), memInsert_memInsert_of_ne (addr := addr + 22) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 23) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 23) (by simp), memInsert_memInsert_of_ne (addr := addr + 23) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 23) (by simp), memInsert_memInsert_of_ne (addr := addr + 23) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 23) (by simp), memInsert_memInsert_of_ne (addr := addr + 23) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 23) (by simp), memInsert_memInsert_of_ne (addr := addr + 23) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 23) (by simp), memInsert_memInsert_of_ne (addr := addr + 23) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 23) (by simp), memInsert_memInsert_of_ne (addr := addr + 23) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 23) (by simp), memInsert_memInsert_of_ne (addr := addr + 23) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 23) (by simp), memInsert_memInsert_of_ne (addr := addr + 23) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 23) (by simp), memInsert_memInsert_of_ne (addr := addr + 23) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 23) (by simp), memInsert_memInsert_of_ne (addr := addr + 23) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 23) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 24) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 24) (by simp), memInsert_memInsert_of_ne (addr := addr + 24) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 24) (by simp), memInsert_memInsert_of_ne (addr := addr + 24) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 24) (by simp), memInsert_memInsert_of_ne (addr := addr + 24) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 24) (by simp), memInsert_memInsert_of_ne (addr := addr + 24) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 24) (by simp), memInsert_memInsert_of_ne (addr := addr + 24) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 24) (by simp), memInsert_memInsert_of_ne (addr := addr + 24) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 24) (by simp), memInsert_memInsert_of_ne (addr := addr + 24) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 24) (by simp), memInsert_memInsert_of_ne (addr := addr + 24) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 24) (by simp), memInsert_memInsert_of_ne (addr := addr + 24) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 24) (by simp), memInsert_memInsert_of_ne (addr := addr + 24) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 24) (by simp), memInsert_memInsert_of_ne (addr := addr + 24) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 25) (by simp), memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 25) (by simp), memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 25) (by simp), memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 25) (by simp), memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 25) (by simp), memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 25) (by simp), memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 25) (by simp), memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 25) (by simp), memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 25) (by simp), memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 25) (by simp), memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 25) (by simp), memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 25) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 26) (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 26) (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 26) (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 26) (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 26) (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 26) (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 26) (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 26) (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 26) (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 26) (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 26) (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 26) (by simp), memInsert_memInsert_of_ne (addr := addr + 26) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp), memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 27) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 28) (by simp), memInsert_memInsert_of_ne (addr := addr + 28) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp), memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 29) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 30) (by simp), memInsert_memInsert_of_ne (addr := addr + 30) (by simp)
     , memInsert_memInsert ]
  rw [ List.foldr_cons, List.foldl_cons
     , memInsert_memInsert_of_ne (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp), memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert_of_ne (addr := addr + 31) (by simp)
     , memInsert_memInsert ]

  rw [List.foldr_nil]
  repeat rw [← List.foldl_cons]
  simp only [List.reverse, List.reverseAux]

lemma update_update_of_ne :
  (h : ∀ {a}, a ∈ offsets_at addr' → a ∉ offsets_at addr) →
  (ms.updateMemory addr val).updateMemory addr' val' =
    (ms.updateMemory addr' val').updateMemory addr val := by
  intro h
  unfold MachineState.updateMemory
  simp
  apply And.intro

  swap
  rw [← max_assoc, max_comm addr' addr, max_assoc]

  rw [ ← mkEntries, ← mkEntries ]
  sorry

lemma lt_toBytes_length_of_mem_offset :
  ∀ {offset}, (v : UInt256) → (offset ∈ offsets) → offset < (toBytes! v).length := by
  unfold offsets
  simp

lemma lookupBytes_nil :
  ∀ {addr},
  [].map (ms.memory.lookupByte ∘ (addr + ↑·)) = [] := by
  simp

lemma lookupBytes_cons :
  ∀ {addr} {offset : ℕ} {os : List ℕ},
  (offset :: os).map ((ms.updateMemory addr val).memory.lookupByte ∘ (addr + ↑·)) =
    (ms.updateMemory addr val).memory.lookupByte (addr + ↑offset)
    :: os.map ((ms.updateMemory addr val).memory.lookupByte ∘ (addr + ↑·)) := by
  intro addr offset os
  exact List.map_cons
    ((ms.updateMemory addr val).memory.lookupByte ∘ (addr + ↑·))
    offset
    os

-- TODO: in newer mathlib
@[simp] theorem get!_some {α} [Inhabited α] {a : α} : (some a).get! = a := rfl

-- lemma lookupByte_updateMemory :
--   ∀ {addr},
--   (ms.updateMemory addr val).memory.lookupByte addr =
--     (UInt256.toBytes! val)[0] := by
--   intro addr
--   unfold MachineState.updateMemory Memory.lookupByte
--   simp
--   rw [ List.zipWith_foldl_eq_zip_foldl ]
--   conv => lhs; rw [splice_toBytes! val]
--   unfold offsets
--   simp only [List.map, List.zip, List.zipWith, List.foldl, flip, id]
--   norm_cast
--   rw [ Fin.add_zero addr ]
--   simp

lemma lookupByte_update_of_ne :
  ∀ {addr addr' : UInt256},
  (h : addr' ∉ offsets.map (addr + ↑·)) →
  (ms.updateMemory addr val).memory.lookupByte addr' =
    ms.memory.lookupByte addr' := by
  intro addr addr' h
  unfold MachineState.updateMemory Memory.lookupByte
  simp
  rw [splice_toBytes! val]
  unfold offsets
  simp [memInsert, List.foldr]

  unfold offsets at h
  simp at h
  repeat rw [← ne_eq] at h
  let ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := h

  rw [ Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne
     , Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne
     , Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne
     , Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne
     , Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne
     , Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne
     , Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne
     , Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne
     , Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne
     , Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne
     , Finmap.lookup_insert_of_ne, Finmap.lookup_insert_of_ne
     ]

  all_goals assumption

lemma lookupByte_at_offset_update :
  ∀ {addr} {n}, (mem: n ∈ offsets) →
  (ms.updateMemory addr val).memory.lookupByte (addr + ↑n) =
    (UInt256.toBytes! val)[n]'(lt_toBytes_length_of_mem_offset val mem) := by
  intro addr n mem
  unfold MachineState.updateMemory Memory.lookupByte
  simp
  conv => lhs; rw [splice_toBytes! val]
  unfold offsets
  simp only [List.foldr]
  norm_cast
  fin_cases mem
  · rw [ Nat.cast_zero, Fin.add_zero addr ]
    simp
  · rw [ Nat.cast_one ]
    simp
  all_goals simp only [ Nat.cast_ofNat, memInsert, Fin.isValue, List.getElem_eq_get
                      , Function.uncurry_apply_pair, add_zero, ne_eq, add_right_eq_self
                      , Fin.reduceEq, not_false_eq_true, Finmap.lookup_insert_of_ne
                      , add_right_inj, Finmap.lookup_insert, get!_some
                      ]

lemma lookupByte_at_offset_update_of_ne {addr addr' : UInt256} :
  ∀ {n}, (mem: n ∈ offsets) →
  (h : addr' + ↑n ∉ offsets.map (addr + ↑·)) →
  (ms.updateMemory addr val).memory.lookupByte (addr' + ↑n) =
    ms.memory.lookupByte (addr' + ↑n) := by
  intro n _ _
  apply lookupByte_update_of_ne (addr' := addr' + ↑n)
  assumption

lemma lookupWord_update : ∀ {addr},
  (ms.updateMemory addr val).memory.lookupWord addr = val := by
  intro addr
  unfold Memory.lookupWord offsets
  repeat rw [ lookupBytes_cons, lookupByte_at_offset_update (by simp) ]
  rw [ List.map_nil
     , ← splice_toBytes!
     , fromBytes!_toBytes!
     ]

lemma lookupWord_update_of_ne {addr addr' : UInt256} :
  (h : ∀ {n}, (mem: n ∈ offsets) → addr' + ↑n ∉ offsets.map (addr + ↑·)) →
  (ms.updateMemory addr val).memory.lookupWord addr' = ms.memory.lookupWord addr' := by
  intro h

  unfold Memory.lookupWord

  rw [ ← List.map_comp_map
     , Function.comp_apply
     , ← List.map_comp_map
     , Function.comp_apply
     ]
  simp only [List.map]

  rw [ lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     , lookupByte_at_offset_update_of_ne (by simp) (h (by simp))
     ]

lemma lookupWord_update_of_next {addr : UInt256} :
  (ms.updateMemory addr val).memory.lookupWord (addr + 32) = ms.memory.lookupWord (addr + 32) := by
  refine lookupWord_update_of_ne (addr := addr) (addr' := addr + 32) ?h
  intro n mem
  fin_cases mem <;> (norm_cast; simp; intro x x_mem)
  · fin_cases x_mem <;> norm_cast
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)
  · fin_cases x_mem <;> (norm_cast; try rw [add_assoc]; simp)

lemma addr_no_overlap : ∀ {k : ℕ},
  (h : k < Memory.maxWords) →
  addr + (k + 1) * 32 ∉ offsets.map (addr + ↑·) := by
  intro k h
  simp
  intro x x_mem
  apply ne_of_lt
  norm_cast

  apply lt_of_le_of_lt (b := Nat.cast 31)
  · rw [Fin.natCast_le_natCast (by linarith [lt_32_of_mem_offsets x_mem]) (by simp)]
    apply Nat.le_of_lt_succ
    exact lt_32_of_mem_offsets x_mem
  · have succ_k_words_lt_size :
      (k + 1) * 32 ≤ 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by
      trans Memory.maxWords * 32
      · simp
        rw [Nat.succ_le]
        exact h
      · rw [Memory.maxWords]
        simp
    rw [Fin.natCast_lt_natCast (by simp) succ_k_words_lt_size]
    apply Nat.lt_of_lt_of_le
    · show (31 < 32); simp
    · linarith

end MachineState

variable {addr addr' p : UInt256}
variable {evm : EVM}
variable {val val' : UInt256}

lemma mstore_mstore :
  mstore (mstore evm p val) p val' = mstore evm p val' := by
  unfold mstore updateMemory
  simp
  exact update_update

lemma mstore_mstore_of_ne :
  mstore (mstore evm addr val) addr' val' =
    mstore (mstore evm addr' val') addr val := by
  unfold mstore updateMemory
  simp
  refine update_update_of_ne ?_
  sorry

lemma lookup_mstore :
  (mstore evm p val).machine_state.memory.lookupWord p = val := by
  unfold mstore updateMemory
  simp
  rw [lookupWord_update]

lemma lookup_mstore_of_ne {addr addr' : UInt256} :
  (h : ∀ {n}, (mem: n ∈ offsets) → addr' + ↑n ∉ offsets.map (addr + ↑·)) →
  (mstore evm addr val).machine_state.memory.lookupWord addr' =
    evm.machine_state.memory.lookupWord addr' := by
  intro h
  unfold mstore updateMemory
  rw [lookupWord_update_of_ne h]

lemma lookup_mstore_of_next :
  ∀ {k}, (h : k < Memory.maxWords) →
  (mstore evm p val).machine_state.memory.lookupWord (p + (k + 1) * 32) =
    evm.machine_state.memory.lookupWord (p + (k + 1) * 32) := by
  sorry

section Interval

variable {p : UInt256}
variable {n : ℕ}
variable {evm : EVM}
variable {ms : MachineState}
variable {val : UInt256}

lemma interval_of_0_eq_nil :
  mkInterval ms.memory p 0 = [] := by
  unfold mkInterval words_at
  simp

lemma interval_eq_lookup_cons : ∀ {n},
  mkInterval ms.memory p (n + 1) =
    ms.memory.lookupWord p :: mkInterval ms.memory (p + 32) n := by
  intro n
  unfold mkInterval words_at
  rw [range'_succ p n, List.map_cons]

-- theorem List.range'_succ (s n step) :
--   List.range' s (n + 1) step = s :: List.range' (s + step) n step := by
--   simp [List.range', Nat.add_succ, Nat.mul_succ]

-- lemma out_of_range :
--   ∀ {n}, (h : n ≤ Memory.maxWords) →
--   mkInterval (mstore evm p val).machine_state.memory (p + 32) n =
--     mkInterval evm.machine_state.memory (p + 32) n := by
--   intro n h
--   induction n generalizing p with
--   | zero => rw [interval_of_0_eq_nil, interval_of_0_eq_nil]
--   | succ n' ih =>
--     have : (2 : UInt256) * 32 = (1 + 1) * 32 := sorry
--     rw [ interval_eq_lookup_cons
--        , ← one_mul 32, ← zero_add 1, ← Nat.cast_zero
--        , lookup_mstore_of_next (p := p) (k := 0) (by simp [Memory.maxWords])
--        , Nat.cast_zero, zero_add 1, one_mul 32
--        , add_assoc, ← two_mul 32
--        , this ]
--     rw (config := {occs := .pos [1]}) [ ← Nat.cast_one ]
--     rw [
--        ]

lemma interval_of_mstore_eq_val_cons :
  mkInterval (mstore evm p val).machine_state.memory p (n + 1) =
    val :: mkInterval (mstore evm p val).machine_state.memory (p + 32) n := by
  rw [ interval_eq_lookup_cons, lookup_mstore ]

lemma interval_of_mstore_eq_val_cons' :
  ∀ {n}, (h : n < Memory.maxWords) →
  mkInterval (mstore evm p val).machine_state.memory p (n + 1) =
    val :: mkInterval evm.machine_state.memory (p + 32) n := by
  sorry
  -- intro n h
  -- induction n generalizing p with
  -- | zero => admit
  -- | succ n' =>
  --   rw [ interval_eq_lookup_cons, lookup_mstore, out_of_range (le_of_lt h) ]

end Interval

end Clear.EVMState
