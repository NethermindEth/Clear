import Clear.Ast
import Clear.EVMState
import Clear.Wheels

namespace Clear

open Ast

-- | A mapping from variable names to literals (`UInt256`s).
abbrev VarStore := Finmap (λ _ : Identifier ↦ Literal)

-- | A jump in control flow containing a checkpoint of the state at jump-time.
inductive Jump where
| Continue : EVM → VarStore → Jump
| Break : EVM → VarStore → Jump
| Leave : EVM → VarStore → Jump
deriving DecidableEq

-- Execution state of a Yul program.
open EVMState in
@[aesop safe 9001 (rule_sets := [Clear.aesop_spec]) [constructors, cases]]
inductive State where
  | Ok : EVM → VarStore → State
  | OutOfFuel : State
  | Checkpoint : Jump → State
deriving DecidableEq

instance : Inhabited State where
  default := .Ok default default

namespace State

def evm : State → EVM
  | Ok evm _ => evm
  | _ => default

def store : State → VarStore
  | Ok _ store => store
  | _ => default

-- ============================================================================
--  STATE PREDICATES (for jumps/errors)
-- ============================================================================

def isOk : State → Prop
  | .Ok _ _ => True
  | _ => False

def isOutOfFuel : State → Prop
  | .OutOfFuel => True
  | _ => False

def isJump (jump : Jump) : State → Prop
  | .Checkpoint jump' => jump = jump'
  | _ => False

def isContinue : State → Prop
  | .Checkpoint (.Continue _ _) => True
  | _ => False

def isBreak : State → Prop
  | .Checkpoint (.Break _ _) => True
  | _ => False

def isLeave : State → Prop
  | .Checkpoint (.Leave _ _) => True
  | _ => False

def allGood (s : State) : Prop := s.isOk ∧ ¬ s.evm.hash_collision

-- ============================================================================
--  STATE TRANSFORMERS
-- ============================================================================

-- | Insert an (identifier, literal) pair into the varstore.
def insert (var : Identifier) (val : Literal) : State → State
  | (Ok evm store) => Ok evm (store.insert var val)
  | s => s

-- | Zip a list of variables with a list of literals and insert right-to-left.
def multifill (vars : List Identifier) (vals : List Literal) : State → State
  | s@(Ok _ _) => (List.zip vars vals).foldr (λ (var, val) s ↦ s.insert var val) s
  | s => s

-- | Overwrite the EVM state of some state.
open EVMState in
def setEvm (evm : EVM) : State → State
  | Ok _ store => Ok evm store
  | s => s

-- | Overwrite the varstore of some state.
def setStore (s s' : State) : State :=
  match s, s' with
    | (Ok evm _), (Ok _ store) => Ok evm store
    | s, _ => s

def setContinue : State → State
  | Ok evm store => Checkpoint (.Continue evm store)
  | s => s

def setBreak : State → State
  | Ok evm store => Checkpoint (.Break evm store)
  | s => s

def setLeave : State → State
  | Ok evm store => Checkpoint (.Leave evm store)
  | s => s

-- | Indicate that we've hit an infinite loop/ran out of fuel.
def diverge : State → State
  | Ok _ _ => .OutOfFuel
  | s => s

-- | Initialize function parameters and return values in varstore.
def initcall (params : List Identifier) (args : List Literal) : State → State
  | s@(Ok _ _) =>
    let s₁ := s.setStore default
    s₁.multifill params args
  | s => s

-- | Since it literally does not matter what happens if the state is non-Ok, we just use the default.
def mkOk : State → State
  | Checkpoint _ => default
  | s => s

-- | Helper function for `reviveJump`.
def revive : Jump → State
  | .Continue evm store => Ok evm store
  | .Break evm store => Ok evm store
  | .Leave evm store => Ok evm store

-- | Revive a saved state (evm, varstore), discarding top-level (evm, varstore).
--
-- Called after we've finished executing:
--    * A loop
--    * A function call
--
-- The compiler disallows top-level `Continue`s or `Break`s in function bodies,
-- thus it is safe to assume the state we're reviving is a checkpoint from the
-- expected flavor of `Jump`.
def reviveJump : State → State
  | Checkpoint c => revive c
  | s => s

-- | If s' is non-Ok, overwrite s with s'.
def overwrite? (s s' : State) : State :=
  match s' with
    | Ok _ _ => s
    | _ => s'

-- ============================================================================
--  STATE QUERIES
-- ============================================================================

-- | Lookup the literal associated with an variable in the varstore, returning 0 if not found.
def lookup! (var : Identifier) : State → Literal
  | Ok _ store => (store.lookup var).get!
  | Checkpoint (.Continue _ store) => (store.lookup var).get!
  | Checkpoint (.Break _ store) => (store.lookup var).get!
  | Checkpoint (.Leave _ store) => (store.lookup var).get!
  | _ => 0

def mload (addr : Literal) : State → Literal
| Ok e _ | Checkpoint (.Continue e _) | Checkpoint (.Break e _) | Checkpoint (.Leave e _) => EVMState.mload e addr
| _ => 0

-- ============================================================================
--  STATE NOTATION
-- ============================================================================

-- | All state-related functions should be prefix operators so they can be read right-to-left.

-- State queries
-- TODO: make this an GetElem instance
notation:65 s:64"[" var "]!!" => State.lookup! var s
notation "❓" => State.isOutOfFuel

-- State transformers
notation:65 s:64 "⟦" var "↦" lit "⟧" => State.insert var lit s
notation:65 "🔁" s:64 => State.setContinue s
notation:65 "💔" s:64 => State.setBreak s
notation:65 "🚪" s:64 => State.setLeave s
notation:65 s:64 "🏪⟦" s' "⟧" => State.setStore s s'
notation:65 s:64 "🇪⟦" evm "⟧" => State.setEvm evm s
notation:65 "🪫" s:64 => State.diverge s
notation:65 "👌" s:64 => State.mkOk s
notation:65 s:64 "☎️⟦" params "," args "⟧" => State.initcall params args s
notation:65 s:64 "✏️⟦" s' "⟧?"  => State.overwrite? s s'
notation:64 (priority := high) "🧟" s:max => State.reviveJump s

-- ============================================================================
--  STATE TRANSFORMER LEMMAS
-- ============================================================================

section

variable {s s' s'' : State}
         {var var' va vb vc vd ve : Identifier}
         {vars params rets : List Identifier}
         {x val val' a b c d e : Literal}
         {vals args : List Literal}
         {j : Jump}
         {evm evm' : EVM}
         {store store' : VarStore}

@[simp] lemma evm_insert : State.evm (insert var val s) = State.evm s := by unfold State.evm insert; rcases s <;> simp only

@[simp] lemma isOk_Ok : isOk (Ok evm store) := by simp [isOk]
@[simp] lemma isOk_OutOfFuel : ¬ isOk OutOfFuel := by simp [isOk]
@[simp] lemma isOk_Checkpoint : ¬ isOk (Checkpoint j) := by simp [isOk]
@[simp] lemma isOutOfFuel_Ok : ¬ isOutOfFuel (Ok evm store) := by simp [isOutOfFuel]
@[simp] lemma isOutOfFuel_OutOfFuel : isOutOfFuel OutOfFuel := by simp [isOutOfFuel]
@[simp] lemma isOutOfFuel_Checkpoint : ¬ isOutOfFuel (Checkpoint j) := by simp [isOutOfFuel]
@[simp] lemma isJump_Ok : ¬ isJump j (Ok evm store) := by simp [isJump]
@[simp] lemma isJump_OutOfFuel : ¬ isJump j OutOfFuel := by simp [isJump]
@[simp] lemma isJump_Checkpoint : isJump j (Checkpoint j) := by simp [isJump]
@[simp] lemma isContinue_Ok : ¬ isContinue (Ok evm store) := by simp [isContinue]
@[simp] lemma isContinue_OutOfFuel : ¬ isContinue OutOfFuel := by simp [isContinue]
@[simp] lemma isContinue_Continue : isContinue (Checkpoint (.Continue evm store)) := by simp [isContinue]
@[simp] lemma isContinue_Break : ¬ isContinue (Checkpoint (.Break evm store)) := by simp [isContinue]
@[simp] lemma isContinue_Leave : ¬ isContinue (Checkpoint (.Leave evm store)) := by simp [isContinue]
@[simp] lemma isBreak_Ok : ¬ isBreak (Ok evm store) := by simp [isBreak]
@[simp] lemma isBreak_OutOfFuel : ¬ isBreak OutOfFuel := by simp [isBreak]
@[simp] lemma isBreak_Continue : ¬ isBreak (Checkpoint (.Continue evm store)) := by simp [isBreak]
@[simp] lemma isBreak_Break : isBreak (Checkpoint (.Break evm store)) := by simp [isBreak]
@[simp] lemma isBreak_Leave : ¬ isBreak (Checkpoint (.Leave evm store)) := by simp [isBreak]
@[simp] lemma isLeave_Ok : ¬ isLeave (Ok evm store) := by simp [isLeave]
@[simp] lemma isLeave_OutOfFuel : ¬ isLeave OutOfFuel := by simp [isLeave]
@[simp] lemma isLeave_Continue : ¬ isLeave (Checkpoint (.Continue evm store)) := by simp [isLeave]
@[simp] lemma isLeave_Break : ¬ isLeave (Checkpoint (.Break evm store)) := by simp [isLeave]
@[simp] lemma isLeave_Leave : isLeave (Checkpoint (.Leave evm store)) := by simp [isLeave]

@[simp] lemma insert_Continue : insert var val (setContinue s) = setContinue s := by unfold insert setContinue; rcases s <;> simp only
@[simp] lemma insert_Break : insert var val (setBreak s) = setBreak s := by unfold insert setBreak; rcases s <;> simp only
@[simp] lemma insert_Leave : insert var val (setLeave s) = setLeave s := by unfold insert setLeave; rcases s <;> simp only

@[simp] lemma isOk_setContinue : ¬ isOk (setContinue s) := by unfold isOk setContinue; rcases s <;> simp
@[simp] lemma isOk_setBreak : ¬ isOk (setBreak s) := by unfold isOk setBreak; rcases s <;> simp
@[simp] lemma isOk_setLeave : ¬ isOk (setLeave s) := by unfold isOk setLeave; rcases s <;> simp

@[simp] lemma isContinue_insert : isContinue (insert var val s) = isContinue s := by unfold isContinue insert; rcases s <;> simp
@[simp] lemma isBreak_insert : isBreak (insert var val s) = isBreak s := by unfold isBreak insert; rcases s <;> simp
@[simp] lemma isLeave_insert : isLeave (insert var val s) = isLeave s := by unfold isLeave insert; rcases s <;> simp

@[simp] lemma isContinue_setBreak : isContinue (setBreak s) = isContinue s := by unfold isContinue setBreak; rcases s <;> simp
@[simp] lemma isContinue_setLeave : isContinue (setLeave s) = isContinue s := by unfold isContinue setLeave; rcases s <;> simp

@[simp] lemma isBreak_setContinue : isBreak (setContinue s) = isBreak s := by unfold isBreak setContinue; rcases s <;> simp
@[simp] lemma isBreak_setLeave : isBreak (setLeave s) = isBreak s := by unfold isBreak setLeave; rcases s <;> simp

@[simp] lemma isLeave_setContinue : isLeave (setContinue s) = isLeave s := by unfold isLeave setContinue; rcases s <;> simp
@[simp] lemma isLeave_setBreak : isLeave (setBreak s) = isLeave s := by unfold isLeave setBreak; rcases s <;> simp

@[aesop unsafe 10% apply] lemma isContinue_setContinue (h : isOk s) : isContinue (setContinue s) := by unfold isContinue setContinue; rcases s <;> simp at *
@[aesop unsafe 10% apply] lemma isBreak_setBreak (h : isOk s) : isBreak (setBreak s) := by unfold isBreak setBreak; rcases s <;> simp at *
@[aesop unsafe 10% apply] lemma isLeave_setLeave (h : isOk s) : isLeave (setLeave s) := by unfold isLeave setLeave; rcases s <;> simp at *

@[simp] lemma isOk_and_isOutOfFuel : ¬ (isOk s ∧ isOutOfFuel s) := by unfold isOk isOutOfFuel; rcases s <;> simp
@[simp] lemma isOk_and_isJump : ¬ (isOk s ∧ isJump j s) := by unfold isOk isJump; rcases s <;> simp
@[simp] lemma isOk_and_isContinue : ¬ (isOk s ∧ isContinue s) := by unfold isOk isContinue; rcases s <;> simp
@[simp] lemma isOk_and_isBreak : ¬ (isOk s ∧ isBreak s) := by unfold isOk isBreak; rcases s <;> simp
@[simp] lemma isOk_and_isLeave : ¬ (isOk s ∧ isLeave s) := by unfold isOk isLeave; rcases s <;> simp

@[simp] lemma reviveJump_setContinue : 🧟(setContinue s) = 🧟s := by unfold reviveJump setContinue revive; rcases s <;> simp
@[simp] lemma reviveJump_setBreak : 🧟(setBreak s) = 🧟s := by unfold reviveJump setBreak revive; rcases s <;> simp
@[simp] lemma reviveJump_setLeave : 🧟(setLeave s) = 🧟s := by unfold reviveJump setLeave revive; rcases s <;> simp
@[simp] lemma reviveJump_outOfFuel : 🧟(OutOfFuel) = OutOfFuel := by unfold reviveJump; simp only

@[simp] lemma isOk_setEvm : isOk (setEvm evm s) = isOk s := by unfold isOk setEvm; rcases s <;> simp

-- | If a state is Ok, we can write it as `Ok _ _`.
-- @[aesop norm 0 simp (rule_sets := [Clear.aesop_spec])]
lemma State_of_isOk (h : isOk s) : ∃ evm store, s = Ok evm store
:= by
  unfold isOk at h
  rcases s <;> simp at *

-- | We can unpack an infinite loop state.
lemma State_of_isOutOfFuel (h : isOutOfFuel s) : s = OutOfFuel
:= by
  unfold isOutOfFuel at h
  aesop

-- | Inserts are transparent to `isOk`.
@[simp]
lemma isOk_insert : isOk (s⟦var ↦ x⟧) = isOk s
:= by
  unfold isOk insert
  rcases s <;> simp at *

@[aesop unsafe 10% apply]
lemma isOk_mkOk_of_isOk (h : isOk s) : isOk (mkOk s) := by unfold mkOk; aesop

lemma Prod.zip_map {α β : Type} {ys : List (α × β)} : List.zip (List.map Prod.fst ys) (List.map Prod.snd ys) = ys
:= by
  induction ys with
    | nil => simp
    | cons z zs ih =>
      simp
      apply ih

@[aesop unsafe 10% apply]
lemma isOk_multifill (h : isOk s) : isOk (multifill vars args s)
:= by
  unfold multifill
  rcases s <;> simp at *
  generalize hpairs : List.zip vars args = xs
  induction xs generalizing vars args with
    | nil =>
      simp
    | cons y ys ih =>
      simp
      apply @ih (List.map Prod.fst ys) (List.map Prod.snd ys)
      rw [Prod.zip_map]

@[aesop unsafe 10% apply]
lemma isOk_setStore_of_isOk (h : isOk s) : isOk (s.setStore s')
:= by
  unfold setStore
  rcases s <;> simp at *
  rcases s' <;> simp at *

@[aesop unsafe 10% apply]
lemma isOk_initcall_of_isOk (h : isOk s) : isOk (initcall vars args s)
:= by
  unfold initcall
  rcases s <;> simp at *
  aesop

@[aesop unsafe 5% apply]
lemma isOk_mkOk_of_isJump (h : isJump j s) : isOk (mkOk s)
:= by
  unfold mkOk
  rcases s <;> simp at *
  · unfold default instInhabitedState
    simp

-- | Diverge is idempotent.
@[simp]
lemma diverge_diverge : diverge (diverge s) = diverge s
:= by
  unfold diverge
  rcases s <;> simp only

-- | Diverge is the identity on infinite loop states.
@[simp]
lemma diverge_OutOfFuel : diverge OutOfFuel = OutOfFuel
:= rfl

@[simp]
lemma diverge_isOutOfFuel_of_isOk : s.isOk → isOutOfFuel (diverge s) := by
  intros h
  unfold diverge isOutOfFuel
  unfold isOk at h
  aesop

-- | Inserting with empty lists is the identity on states.
@[simp]
lemma multifill_nil : multifill [] vals s = s
:= by
  unfold multifill
  rcases s <;> simp

-- | Inserting with empty lists is the identity on states.
@[simp]
lemma multifill_nil' : multifill vars [] s = s
:= by
  unfold multifill
  rcases s <;> simp

-- | Multifilling x:xs and y:ys is the same as inserting into a multifill of the tails.
@[simp]
lemma multifill_cons
: multifill (var :: vars) (val :: vals) s = (multifill vars vals s).insert var val
:= by
  unfold insert multifill
  rcases s with ⟨evm, store⟩ | _ | _ | _ <;> simp
  · unfold insert; simp only

-- | Setting the checkpoint of an 👌 state to its old checkpoint is the identity.
@[simp]
lemma overwrite?_mkOk : (mkOk s).overwrite? s = s
:= by
  unfold mkOk overwrite?
  rcases s <;> dsimp only

-- | Inserts are transparent when passed as arguments to `overwrite?`.
@[simp]
lemma overwrite?_insert : (s.overwrite? (s'.insert var x)) = s.overwrite? s'
:= by
  unfold insert overwrite?
  rcases s' <;> simp

lemma insert_of_ok : (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val)
:= by
  rfl

-- | Looking up a variable you've just inserted gives you the value you inserted.
@[simp]
lemma lookup_insert : (Ok evm store)⟦var ↦ x⟧[var]!! = x
:= by
  unfold insert lookup!
  aesop

@[aesop norm simp]
lemma lookup_insert' (h : isOk s) : s⟦var ↦ x⟧[var]!! = x
:= by
  unfold insert lookup!
  rcases s <;> simp at *

-- | Inserting with the same key twice overwrites.
@[simp]
lemma insert_insert : insert var val (insert var val' s) = insert var val s
:= by
  unfold insert
  aesop

-- | Looking up a variable in a default state returns 0.
@[simp]
lemma lookup_default : default[var]!! = 0 := by aesop

-- | Inserts preserve lookups when the variable you're looking up is different from the one you inserted.
-- @[aesop unsafe 3% apply (rule_sets := [Clear.aesop_varstore])]
lemma lookup_insert_of_ne (h : var' ≠ var) : s⟦var ↦ x⟧[var']!! = s[var']!!
:= by
  unfold State.lookup! insert
  rcases s with ⟨evm, store⟩ | _ | _ | _ <;> simp
  aesop

open Lean Meta Elab Tactic Parser.Tactic in
@[aesop safe 0 tactic (rule_sets := [Clear.aesop_varstore])]
def lookup_insert_of_ne_aux : TacticM Unit := do
  evalTactic <| ← `(tactic|
    rw [lookup_insert_of_ne (by decide)] at *
  )

-- | Revive is the identity if the state is Ok.
@[simp]
lemma revive_of_ok (h : isOk s) : 🧟s = s
:= by
  unfold reviveJump
  rcases s with _ | _ | _ <;> simp
  · unfold isOk at h
    simp only at h

-- | Revives are transparent to lookups when the state being revived is Ok.
lemma lookup_revive_of_ok (h : isOk s) : (🧟s)[var]!! = s[var]!!
:= by
  rw [revive_of_ok]
  assumption

@[simp]
lemma lookup_setContinue : (setContinue s)[var]!! = s[var]!!
:= by
  unfold lookup! setContinue
  rcases s <;> simp

@[simp]
lemma lookup_setBreak : (setBreak s)[var]!! = s[var]!!
:= by
  unfold lookup! setBreak
  rcases s <;> simp

@[simp]
lemma lookup_setLeave : (setLeave s)[var]!! = s[var]!!
:= by
  unfold lookup! setLeave
  rcases s <;> simp

@[aesop unsafe 10% apply]
lemma not_isOk_of_isContinue (h : isContinue s) : ¬ isOk s
:= by
  unfold isOk
  unfold isContinue at h
  rcases s <;> simp
  obtain ⟨evm, store, h⟩ := h

@[aesop unsafe 10% apply]
lemma not_isOk_of_isBreak (h : isBreak s) : ¬ isOk s
:= by
  unfold isOk
  unfold isBreak at h
  rcases s <;> simp
  obtain ⟨evm, store, h⟩ := h

@[aesop unsafe 10% apply]
lemma not_isOk_of_isLeave (h : isLeave s) : ¬ isOk s
:= by
  unfold isOk
  unfold isLeave at h
  rcases s <;> simp
  obtain ⟨evm, store, h⟩ := h

-- | Setting the status conditionally is the identity when state we're conditioned on is Ok.
lemma overwrite?_of_isOk (h : isOk s') : s.overwrite? s' = s
:= by
  unfold overwrite?
  rcases s' <;> simp <;> try contradiction

@[simp]
lemma overwrite?_of_Ok : s.overwrite? (Ok evm store) = s := rfl

@[simp]
lemma mkOk_of_isOk (h : isOk s) : mkOk s = s
:= by
  unfold mkOk
  rcases s <;> simp at *

@[simp]
lemma mkOk_initcall_Ok : mkOk (initcall vars args (Ok evm store)) = initcall vars args (Ok evm store)
:= by
  have : isOk (initcall vars args (Ok evm store)) := by apply isOk_initcall_of_isOk; simp
  have ⟨evm, store, hh⟩ := State_of_isOk this
  rw [hh]
  unfold mkOk
  simp

@[simp]
lemma reviveJump_insert (h : isOk s) : 🧟(insert var val s) = insert var val s
:= by
  unfold reviveJump insert revive isOk at *
  rcases s <;> simp at *

@[simp]
lemma initcall_insert : initcall params args (insert var val s) = initcall params args s
:= by
  unfold initcall insert
  rcases s <;> simp only at *
  unfold multifill setStore
  simp only

@[simp]
lemma initcall_setStore : initcall params args (setStore s s') = initcall params args s
:= by
  unfold initcall setStore
  rcases s <;> simp only at *
  rcases s' <;> simp only at *

@[simp]
lemma setStore_insert : (insert var val s).setStore (Ok evm store) = s.setStore (Ok evm store)
:= by
  unfold setStore insert
  rcases s <;> simp

@[simp]
lemma setStore_ok {e e' σ σ'} : (Ok e σ).setStore (Ok e' σ') = Ok e σ' := by
  unfold setStore
  aesop

@[simp]
lemma evm_multifill : (multifill vars vals s).evm = s.evm
:= by
  unfold multifill
  rcases s with _ | _ | _ <;> simp at *
  generalize hpairs : List.zip vars vals = xs
  induction xs generalizing vars vals with
    | nil =>
      simp
    | cons y ys ih =>
      simp
      apply @ih (List.map Prod.fst ys) (List.map Prod.snd ys)
      rw [Prod.zip_map]

@[simp]
lemma evm_setStore : (s.setStore s').evm = s.evm
:= by
  unfold evm setStore
  rcases s' <;> rcases s <;> simp

@[simp]
lemma setStore_initcall : (initcall vars vals s).setStore (Ok evm store) = s.setStore (Ok evm store)
:= by
  unfold setStore initcall
  rcases s with ⟨evm', store'⟩ | _ | _ <;> simp
  · generalize h : multifill _ _ _ = s'
    have : isOk s' := by subst h; aesop
    have := State_of_isOk this
    obtain ⟨evm'', store'', hh⟩ := this
    rw [hh]
    dsimp only
    simp
    have : s'.evm = evm'' := by subst hh; unfold evm; simp
    subst this
    subst h
    simp
    unfold evm
    simp only

@[simp]
lemma setStore_same : s.setStore s = s
:= by
  unfold setStore
  rcases s <;> simp

@[simp]
lemma lookup_initcall_1 : (initcall (va :: vars) (a :: vals) (Ok evm store))[va]!! = a
:= by
  unfold initcall
  simp
  rw [lookup_insert']
  aesop

lemma lookup_initcall_2 (ha : vb ≠ va) : (initcall (va :: vb :: vars) (a :: b :: vals) (Ok evm store))[vb]!! = b
:= by
  unfold initcall
  simp
  rw [lookup_insert_of_ne ha]
  rw [lookup_insert']
  aesop

lemma lookup_initcall_3 (ha : vc ≠ va) (hb : vc ≠ vb) : (initcall (va :: vb :: vc :: vars) (a :: b :: c :: vals) (Ok evm store))[vc]!! = c
:= by
  unfold initcall
  simp
  rw [lookup_insert_of_ne ha]
  rw [lookup_insert_of_ne hb]
  rw [lookup_insert']
  aesop

lemma lookup_initcall_4 (ha : vd ≠ va) (hb : vd ≠ vb) (hc : vd ≠ vc) : (initcall (va :: vb :: vc :: vd :: vars) (a :: b :: c :: d :: vals) (Ok evm store))[vd]!! = d
:= by
  unfold initcall
  simp
  rw [lookup_insert_of_ne ha]
  rw [lookup_insert_of_ne hb]
  rw [lookup_insert_of_ne hc]
  rw [lookup_insert']
  aesop

lemma lookup_initcall_5 (ha : ve ≠ va) (hb : ve ≠ vb) (hc : ve ≠ vc) (hd : ve ≠ vd) : (initcall (va :: vb :: vc :: vd :: ve :: vars) (a :: b :: c :: d :: e :: vals) (Ok evm store))[ve]!! = e
:= by
  unfold initcall
  simp
  rw [lookup_insert_of_ne ha]
  rw [lookup_insert_of_ne hb]
  rw [lookup_insert_of_ne hc]
  rw [lookup_insert_of_ne hd]
  rw [lookup_insert']
  aesop

@[simp]
lemma get_evm_of_ok : (Ok evm store).evm = evm
:= by
  unfold evm
  simp

lemma get_evm_of_isOk (h : isOk s) : ∃ evm, s.evm = evm
:= by
  let ⟨evm, store, h'⟩ := State_of_isOk h
  exists evm
  rw [h']
  simp

@[simp]
lemma evm_get_set_of_ok : ((Ok evm store).setEvm evm').evm = evm'
:= by
  unfold setEvm evm
  simp

@[simp]
lemma evm_get_set_of_isOk (h : isOk s) : (s.setEvm evm').evm = evm'
:= by
  unfold setEvm evm
  rcases s <;> simp <;> try contradiction

@[simp]
lemma setEvm_insert_comm : s⟦var ↦ val⟧.setEvm evm' = (s.setEvm evm')⟦var ↦ val⟧
:= by
  rcases s <;> [(try simp only); aesop_spec; aesop_spec]
  rfl

-- @[simp]
lemma insert_setEvm_insert : (s.setEvm evm')⟦var ↦ val⟧ = s⟦var ↦ val⟧.setEvm evm'
:= by
  rcases s <;> [(try simp only); aesop_spec; aesop_spec]
  rfl

end

end State
