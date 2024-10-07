import Mathlib.Data.Finmap
import Mathlib.Data.Fin.Basic
import Clear.Ast
import Clear.Instr
import Clear.UInt256
import Clear.Wheels

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

def UInt256.offsets : List UInt256 :=
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
  17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]

def MachineState.updateMemory (m : MachineState) (addr v : UInt256) : MachineState :=
  {m with memory := let offsets := List.range 32
                    let addrs   := offsets.map (·+addr)
                    let inserts := addrs.zipWith Finmap.insert (UInt256.toBytes! v)
                    inserts.foldl (init := m.memory) (flip id)
          max_address := max addr m.max_address }

lemma cheeky_proof {a b : Int} : (if a > b then a else b) = max a b := by rw [max_comm, max_def_lt]

def MachineState.lookupMemory (m : MachineState) (addr : UInt256) : UInt256 :=
  UInt256.fromBytes! (List.map (fun i => (m.memory.lookup (addr + i)).get!) UInt256.offsets)

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
  λ a b ↦ (Eq on EVMState.account_map) a b ∧
          (Eq on EVMState.hash_collision) a b ∧
          (Eq on EVMState.execution_env) a b ∧
          (Eq on EVMState.keccak_map) a b

lemma preserved_def {e₀ e₁ : EVM} : preserved e₀ e₁ =
  (e₀.account_map   = e₁.account_map ∧
  e₀.hash_collision = e₁.hash_collision ∧
  e₀.execution_env = e₁.execution_env ∧
  e₀.keccak_map = e₁.keccak_map)  := by
  unfold preserved
  dsimp

def preserves_account_map {evm evm' : EVMState} (h : preserved evm evm') :
  evm.account_map = evm'.account_map := by
  rw [preserved_def] at h
  exact h.1

def preserves_collision {evm evm' : EVMState} (h : preserved evm evm') :
  evm.hash_collision = evm'.hash_collision := by
  rw [preserved_def] at h
  exact h.2.1

def preserves_execution_env {evm evm' : EVMState} (h : preserved evm evm') :
  evm.execution_env = evm'.execution_env := by
  rw [preserved_def] at h
  exact h.2.2.1

def preserves_keccak_map {evm evm' : EVMState} (h : preserved evm evm') :
  evm.keccak_map = evm'.keccak_map := by
  rw [preserved_def] at h
  exact h.2.2.2

@[simp]
lemma preserved_rfl {e : EVM} : preserved e e := by
  rw [preserved_def]
  simp

lemma preserved_symm {e₀ e₁ : EVM} : preserved e₀ e₁ = preserved e₁ e₀ := by
  rw [preserved_def, preserved_def]
  ext
  apply Iff.intro <;> {
    intro ⟨acc, col, env, kec⟩
    symm at acc col env kec
    exact ⟨acc, col, env, kec⟩
  }

@[simp]
lemma preserved_trans {e₀ e₁ e₂ : EVM} :
  preserved e₀ e₁ → preserved e₁ e₂ → preserved e₀ e₂ := by
  rw (config := {occs := .pos [3]}) [preserved_def]
  intro h₀ h₁
  have acc := Eq.trans (preserves_account_map h₀) (preserves_account_map h₁)
  have col := Eq.trans (preserves_collision h₀) (preserves_collision h₁)
  have env := Eq.trans (preserves_execution_env h₀) (preserves_execution_env h₁)
  have kec := Eq.trans (preserves_keccak_map h₀) (preserves_keccak_map h₁)
  constructor; swap; constructor; swap; constructor
  all_goals assumption

-- functions for querying balance

namespace EVMState

section

open Array ByteArray

-- | Add an error to the EVMState indicating that we hit a hash collision in `keccak256`.
def addHashCollision (σ : EVMState) : EVMState := { σ with hash_collision := True }

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
  let m     := (List.range' i f).map Fin.ofNat
  m.map ms.lookupMemory

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
  σ.machine_state.lookupMemory spos

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

lemma mstore_preserves {evm} {pos val} : preserved evm (evm.mstore pos val) := by
  unfold mstore updateMemory
  rw [preserved_def]
  simp

end

end Clear.EVMState
