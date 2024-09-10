import Mathlib.Data.Finmap
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Intervals
import Clear.Ast
import Clear.Instr
import Clear.UInt256
import Clear.Wheels

set_option linter.setOption false
set_option pp.coercions false

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

def Address.size : Nat := 2 ^ 160
abbrev Address : Type := Fin Address.size

instance : Inhabited Address := ⟨Fin.ofNat 0⟩
instance : NeZero Address.size := ⟨by decide⟩

namespace Address

def top : ℕ := (⊤ : Address).val

lemma top_def : top = 2 ^ 160 - 1 := by
  unfold top
  rw [Fin.top_eq_last]
  simp

lemma top_def' : top = 1461501637330902918203684832716283019655932542975 := by
  rw [top_def]; simp

lemma size_def : size = 1461501637330902918203684832716283019655932542976 := by
  unfold size; simp

def ofNat (n : ℕ) : Address := Fin.ofNat n
def ofUInt256 (u : UInt256) : Address := Fin.ofNat (u.val % size)

instance {n : Nat} : OfNat Address n := ⟨ofNat n⟩
instance : NeZero top := ⟨by decide⟩

lemma zero_lt_top  : 0 < top := by decide
lemma zero_le_top  : 0 ≤ top := le_of_lt zero_lt_top

lemma zero_lt_size : 0 < size := by decide
lemma zero_le_size : 0 ≤ size := le_of_lt zero_lt_size

lemma one_lt_top  : 1 < top := by decide
lemma one_le_top  : 1 ≤ top := le_of_lt one_lt_top

lemma one_lt_size : 1 < size := by decide
lemma one_le_size : 1 ≤ size := le_of_lt one_lt_size

lemma top_eq_pred_size : top = size - 1 := by
  unfold size top
  rw [Fin.top_eq_last]
  simp

lemma top_eq_pred_size_ofUInt256 : top.toUInt256 = size.toUInt256 - 1 := by
  unfold size top
  rw [Fin.top_eq_last]
  simp
  decide

lemma succ_top_eq_size : top + 1 = size := by
  rw [top_eq_pred_size, Nat.sub_add_cancel (le_of_lt one_lt_size)]

lemma top_lt_size : top < size := by
  rw [← succ_top_eq_size]; simp

lemma top_le_size : top ≤ size := le_of_lt top_lt_size

lemma size_lt_UInt256_size : size < UInt256.size := by decide
lemma size_le_UInt256_size : size ≤ UInt256.size := le_of_lt size_lt_UInt256_size

lemma top_lt_UInt256_size : top < UInt256.size := by decide
lemma top_le_UInt256_size : top ≤ UInt256.size := le_of_lt top_lt_UInt256_size

lemma ofUInt256_lt_UInt256_size {u : UInt256} : ↑(ofUInt256 u) < UInt256.size := by
  unfold ofUInt256 Fin.ofNat
  simp; rw [← size_def]; simp
  simp_rw [← UInt256.size_def]
  trans size
  · exact Nat.mod_lt u (LT.lt.gt zero_lt_size)
  · exact size_lt_UInt256_size

lemma ofUInt256_eq_mod (u : UInt256) : ↑(ofUInt256 u) = u.val % size := by
  unfold ofUInt256 Fin.ofNat
  simp_rw [← top_def', succ_top_eq_size]
  simp

lemma and_size_eq_ofUInt256 {u : UInt256}
  : Fin.land u (size.toUInt256 - 1) = ofUInt256 u := by
  rw [ Fin.natCast_def ]
  simp_rw [ Nat.mod_eq_of_lt ofUInt256_lt_UInt256_size ]

  rw [← top_eq_pred_size_ofUInt256]
  unfold Fin.land
  simp [-UInt256.size]; rw [← UInt256.size_def]
  -- this ought to be in mathlib...
  have Nat.land_eq_and (p q : Nat) : p.land q = p &&& q := rfl
  rw [ Nat.land_eq_and u.val
     , Nat.mod_eq_of_lt top_lt_UInt256_size
     , top_def
     , Nat.and_pow_two_is_mod u.val 160
     , ← size
     ]
  have : u.val % size < UInt256.size := by
    trans size
    · apply Nat.mod_lt u.val
      exact LT.lt.gt zero_lt_size
    · exact size_lt_UInt256_size
  simp_rw [Nat.mod_eq_of_lt this]
  symm; exact ofUInt256_eq_mod u

end Address

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
  {act with storage := Finmap.insert k v act.storage}

-- definition of the machine state

structure MachineState : Type where
  memory        : Finmap (λ _ : UInt256 => UInt8)
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
lemma mem_offsets_of_le_32 : ∀ {n}, n < 32 → n ∈ offsets :=
  mem_offsets.mpr

lemma le_32_of_mem_offsets : ∀ {n}, n ∈ offsets → n < 32 :=
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

lemma UInt256.addresses_of (addr : UInt256) {a} :
  a ∈ offsets.map (addr + ↑·) ↔ a ∈ Set.Ico addr (addr + 32) := by
  sorry

namespace UInt256

def range' {n} (start : UInt256) (len : Fin (n + 1)) (step : UInt256 := 1) : List UInt256 :=
  match start, len with
  | _, 0 => []
  | s, ⟨n+1, _⟩ => s :: range' (s + step) ⟨n, by linarith⟩ step

@[simp]
lemma range'_zero {s step : UInt256} : range' (n := 0) s 0 step = [] := by
  unfold range'
  rfl

@[simp]
lemma range'_one {s step : UInt256} : range' (n := 1) s 1 step = [s] := by
  unfold range'
  simp

lemma range'_succ {n} (start : UInt256) (len : Fin (n + 2)) (step : UInt256) [NeZero len] :
  range' start len step =
    start :: range' (start + step) (len.pred NeZero.out) step := by
  have ne : len ≠ 0 := NeZero.out
  obtain ⟨y, y_succ_eq_len⟩ := Fin.exists_succ_eq_of_ne_zero ne
  simp_rw [← y_succ_eq_len]
  conv =>
    lhs
    unfold range'
    simp
    dsimp [Fin.succ]
    
  simp


-- lemma range'_eq_cons_iff
--   {s n a : UInt256} {xs : List UInt256} :
--   range' s n = a :: xs ↔
--     s = a ∧ 0 < n ∧ xs = range' (a + 1) (n - 1) := sorry

lemma map_add_range' (a) : ∀ s n step,
  List.map (λ (x : UInt256) ↦ a + x) (range' s n step) =
    range' (a + s) n step
  | _, 0, _ => by simp
  | s, ⟨n+1, _⟩, step => sorry

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
    have h_offset := mem_offsets_of_le_32 h₂
    fin_cases h_offset
    all_goals aesop

def MachineState.updateMemory (m : MachineState) (addr v : UInt256) : MachineState :=
  {m with memory := let addrs   := offsets.map (addr + ↑·)
                    let inserts := addrs.zipWith Finmap.insert (UInt256.toBytes! v)
                    inserts.foldl (init := m.memory) (flip id)
          max_address := max addr m.max_address }

def MachineState.lookupByte (m : MachineState) (addr : UInt256) : UInt8 :=
  (m.memory.lookup addr).get!

def MachineState.lookupWord (m : MachineState) (addr : UInt256) : UInt256 :=
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

def mkInterval (ms : MachineState) (p n : UInt256) : List UInt256 :=
  let i : ℕ := p.val
  let f : ℕ := n.val
  let m     := (List.range' i f 32).map Fin.ofNat
  m.map ms.lookupWord

def keccak256 (σ : EVMState) (p n : UInt256) : Option (UInt256 × EVMState) :=
  let interval : List UInt256 := mkInterval σ.machine_state p n
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
  σ.machine_state.lookupWord spos

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

section MachineState

variable {p n : UInt256}
variable {ms : MachineState}
variable {val : UInt256}

lemma lt_toBytes_length_of_mem_offset :
  ∀ {offset}, (v : UInt256) → (offset ∈ offsets) → offset < (toBytes! v).length := by
  unfold offsets
  simp
  
lemma lookupBytes_nil :
  ∀ {addr},
  [].map (ms.lookupByte ∘ (addr + ↑·)) = [] := by
  simp

lemma lookupBytes_cons :
  ∀ {addr} {offset : ℕ} {os : List ℕ},
  (offset :: os).map ((ms.updateMemory addr val).lookupByte ∘ (addr + ↑·)) = 
    (ms.updateMemory addr val).lookupByte (addr + ↑offset)
    :: os.map ((ms.updateMemory addr val).lookupByte ∘ (addr + ↑·)) := by
  intro addr offset os
  exact List.map_cons
    ((ms.updateMemory addr val).lookupByte ∘ (addr + ↑·))
    offset
    os

-- TODO: in newer mathlib
@[simp] theorem get!_some {α} [Inhabited α] {a : α} : (some a).get! = a := rfl

lemma lookupByte_updateMemory :
  ∀ {addr},
  (ms.updateMemory addr val).lookupByte addr =
    (UInt256.toBytes! val)[0] := by
  intro addr
  unfold MachineState.updateMemory MachineState.lookupByte
  simp
  rw [ List.zipWith_foldl_eq_zip_foldl ]
  conv => lhs; rw [splice_toBytes! val]
  unfold offsets
  simp only [List.map, List.zip, List.zipWith, List.foldl, flip, id]
  norm_cast
  rw [ Fin.add_zero addr ]
  simp

lemma lookupByte_updateMemory_of_ne :
  ∀ {addr addr' : UInt256},
  (h : addr' ∉ offsets.map (addr + ↑·)) →
  (ms.updateMemory addr val).lookupByte addr' =
    ms.lookupByte addr' := by
  intro addr addr' h
  unfold MachineState.updateMemory MachineState.lookupByte
  simp
  rw [ List.zipWith_foldl_eq_zip_foldl ]
  conv => lhs; rw [splice_toBytes! val]
  unfold offsets
  simp only [List.map, List.zip, List.zipWith, List.foldl, flip, id]
  norm_cast
  rw [ Fin.add_zero addr ]
  
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

lemma lookupByte_at_offset_updateMemory :
  ∀ {addr} {n}, (mem: n ∈ offsets) →
  (ms.updateMemory addr val).lookupByte (addr + ↑n) =
    (UInt256.toBytes! val)[n]'(lt_toBytes_length_of_mem_offset val mem) := by
  intro addr n mem
  unfold MachineState.updateMemory MachineState.lookupByte
  simp
  rw [ List.zipWith_foldl_eq_zip_foldl ]
  conv => lhs; rw [splice_toBytes! val]
  unfold offsets
  simp only [List.map, List.zip, List.zipWith, List.foldl, flip, id]
  norm_cast
  fin_cases mem
  · rw [ Nat.cast_zero, Fin.add_zero addr ]
    simp
  · rw [ Nat.cast_one ]
    simp
  all_goals simp only [ Nat.cast_ofNat, Fin.isValue, List.getElem_eq_get, add_zero, ne_eq
                      , add_right_inj, Fin.reduceEq, not_false_eq_true
                      , Finmap.lookup_insert_of_ne, Finmap.lookup_insert, get!_some
                      ]

lemma lookupByte_at_offset_updateMemory_of_ne {addr addr' : UInt256} :
  ∀ {n}, (mem: n ∈ offsets) →
  (h : addr' + ↑n ∉ offsets.map (addr + ↑·)) →
  (ms.updateMemory addr val).lookupByte (addr' + ↑n) =
    ms.lookupByte (addr' + ↑n) := by
  intro n mem h
  apply lookupByte_updateMemory_of_ne (addr' := addr' + ↑n)
  assumption

lemma lookupWord_updateMemory : ∀ {addr}, (ms.updateMemory addr val).lookupWord addr = val := by
  intro addr
  unfold MachineState.lookupWord offsets
  repeat rw [ lookupBytes_cons, lookupByte_at_offset_updateMemory (by simp) ]
  rw [ List.map_nil
     , ← splice_toBytes!
     , fromBytes!_toBytes!
     ]

-- set_option maxHeartbeats 5000000

lemma lookupWord_updateMemory_of_ne {addr addr' : UInt256} :
  ∀ {n}, (mem: n ∈ offsets) →
  (h : addr' + ↑n ∉ offsets.map (addr + ↑·)) →
  (ms.updateMemory addr val).lookupWord addr' = ms.lookupWord addr' := by
  intro n mem h
    
  unfold MachineState.lookupWord
  
  rw [ ← List.map_comp_map
     , Function.comp_apply
     , ← List.map_comp_map
     , Function.comp_apply
     -- , Function.comp_def
     ]
  sorry

-- lemma updateMemory_updateMemory :
--   ∀ {addr} {val val'},
--   (ms.updateMemory addr val).updateMemory addr val' = ms.updateMemory addr val' := by
--   sorry

end MachineState

section Interval

variable {p n : UInt256}
variable {evm : EVM}
variable {ms : MachineState}
variable {val : UInt256}

  -- mkInterval (mstore evm x v) x = v :: (mkInterval evm (x + 32))

lemma zero_len_eq_nil :
  mkInterval ms p 0 = [] := by
  unfold mkInterval
  simp

theorem List.range'_succ (s n step) :
  List.range' s (n + 1) step = s :: List.range' (s + step) n step := by
  simp [List.range', Nat.add_succ, Nat.mul_succ]

lemma ofNat_of_val (k : UInt256) : (Fin.ofNat k.val : UInt256) = k := by
  dsimp [Fin.ofNat]
  simp_rw [ ← UInt256.size_def, Nat.mod_eq_of_lt k.isLt ]
  rfl

lemma succ_len_eq_cons [NeZero n] :
  mkInterval (mstore evm p val).machine_state p n =
    val :: mkInterval evm.machine_state (p + 1) (n - 1) := by
  -- generalize k_def : n.pred h = k
  -- have k : UInt256 := n.pred h
  have ne : n.val ≠ 0 := Fin.val_ne_of_ne NeZero.out
  have one_le_n : 1 ≤ n.val := Nat.one_le_iff_ne_zero.mpr ne
  have u_def : Σ' u : ℕ, u.succ = ↑n := by
    use (n.pred NeZero.out).val
    simp
    rw [Nat.sub_add_cancel one_le_n]

  let ⟨u, succ_u_eq_n⟩ := u_def
  
  unfold mstore mkInterval updateMemory
  simp
  rw [ ← succ_u_eq_n, List.range'_succ ↑p ↑u 1, List.map_cons ]
  rw [Function.comp_apply] -- dsimp [(· ∘ ·)]

  have u_eq_pred_n : u = n - 1 := by
    rw [← Nat.succ_inj]
    dsimp
    rw [Nat.sub_add_cancel one_le_n]
    exact succ_u_eq_n

  rw [ ofNat_of_val p, @lookupWord_updateMemory evm.machine_state val p ]
  rw [ u_eq_pred_n ]
  simp
  sorry

end Memory.Interval

end Clear.EVMState
