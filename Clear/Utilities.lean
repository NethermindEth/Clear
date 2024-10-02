import Clear.Abstraction
import Clear.Wheels

namespace Clear.Utilities

open Clear
open Clear.Abstraction
open Clear.State

@[aesop safe apply (rule_sets := [Clear.aesop_spec])]
lemma spec_eq {P P' : State → State  → Prop} {s₀ s₉ : State} :
    (¬❓ s₉ → P s₀ s₉ →  P' s₀ s₉) → Spec P s₀ s₉ → Spec P' s₀ s₉ := by
  intros P'_of_P h
  match s₀ with
  | .Ok e σ =>
    unfold Spec at *
    simp only at h
    simp only
    intros h'
    exact (P'_of_P h' ∘ h) h'
  | .Checkpoint j =>
    unfold Spec at *
    simp only at h
    simp only
    exact h
  | .OutOfFuel =>
    unfold Spec at *
    simp only at h
    simp only
    exact h

@[aesop safe apply (rule_sets := [Clear.aesop_spec])]
lemma collision_spec_eq {P P' : State → State  → Prop} {s₀ s₉ : State} :
  (¬ s₉.evm.hash_collision → Spec P s₀ s₉ → Spec P' s₀ s₉) → CollidingSpec P s₀ s₉ → CollidingSpec P' s₀ s₉ := by
  unfold CollidingSpec
  intro S'_of_S
  split
  simp
  intro Spec_of_c c
  exact S'_of_S c (Spec_of_c c) 

@[aesop safe apply (rule_sets := [Clear.aesop_spec])]
lemma collision_spec_eq' {P P' : State → State  → Prop} {s₀ s₉ : State} :
  (¬ s₉.evm.hash_collision → ¬❓ s₉ → P s₀ s₉ →  P' s₀ s₉) → CollidingSpec P s₀ s₉ → CollidingSpec P' s₀ s₉ := by
  intro P'_of_P
  apply collision_spec_eq
  intro c
  apply spec_eq
  exact P'_of_P c

@[simp]
lemma checkpt_insert_elim {var} {val} {j} : (.Checkpoint j)⟦var ↦ val⟧ = .Checkpoint j := by
  simp only [State.insert]

@[simp]
lemma checkpt_setBreak_elim {j} : 💔Checkpoint j = Checkpoint j := by
  simp only [State.setBreak]

def isPure (s₀ : State) (s₁ : State) : Prop :=
  match s₀, s₁ with
  | .Ok e₀ _, .Ok e₁ _ => e₀ = e₁
  | _, _ => True

@[simp]
lemma isPure_insert {s : State} {var val} : isPure s (s⟦var↦val⟧) := by
  unfold State.insert isPure
  aesop

@[simp]
lemma isPure_trans {s₀ s₁ s₂ : State} : isOk s₁ → isPure s₀ s₁ → isPure s₁ s₂ → isPure s₀ s₂ := by
  unfold isPure
  match s₀ with
  | .OutOfFuel | .Checkpoint _ => simp
  | .Ok e₀ σ₀ =>
    match s₂ with
    | .OutOfFuel | .Checkpoint _ => simp
    | .Ok e₂ σ₂ =>
      match s₁ with
      | .Ok e₁ σ₁ | .OutOfFuel | .Checkpoint _ => aesop

@[simp]
lemma isPure_rfl {s : State} : isPure s s := by
  unfold isPure; aesop

@[simp]
lemma mload_eq_of_isPure {s s' : State} {a : UInt256} : isOk s → isOk s' → isPure s s' → State.mload a s = State.mload a s' := by
  unfold mload isOk isPure
  cases s <;> cases s' <;> aesop

@[aesop safe norm (rule_sets := [Clear.aesop_spec])]
lemma isPure_ok_insert_of_ok_ok {s s'} {var} {val}
  (h : s.isOk) :
  isPure (s⟦var↦val⟧) s' ↔ isPure s s' := by aesop_spec

@[aesop unsafe 5% (rule_sets := [Clear.aesop_spec])]
lemma evm_eq_of_isPure_ok_ok {evm evm'} {vs vs'} (h : isPure (Ok evm vs) (Ok evm' vs')) : evm = evm' := by
  aesop_spec

@[aesop unsafe 5% (rule_sets := [Clear.aesop_spec])]
lemma evm_eq_symm_of_isPure_ok_ok {evm evm'} {vs vs'} (h : isPure (Ok evm vs) (Ok evm' vs')) : evm' = evm := by
  symm
  aesop_spec

def preservesEvm (s₀ : State) (s₁ : State) : Prop :=
  match s₀, s₁ with
  | .Ok e₀ _, .Ok e₁ _ => preserved e₀ e₁
  | _, _ => True

lemma preservesEvm_eq (s₀ : State) (s₁ : State) : preserved s₀.evm s₁.evm → preservesEvm s₀ s₁ := by
  unfold preservesEvm
  cases s₀ <;> cases s₁ <;> simp

lemma preservesEvm_of_isOk {s₀ s₁ : State} :
  s₀.isOk → s₁.isOk → preservesEvm s₀ s₁ →
  (s₀.evm.account_map = s₁.evm.account_map ∧
  s₀.evm.hash_collision = s₁.evm.hash_collision ∧
  s₀.evm.execution_env = s₁.evm.execution_env) := by
  unfold isOk preservesEvm
  cases s₀ <;> cases s₁ <;> simp
  rw [preserved_def]
  intro _; assumption

@[simp]
lemma preservesEvm_rfl {s : State} : preservesEvm s s := by
  unfold preservesEvm preserved
  dsimp [(· ∩ ·)]
  cases s <;> simp

@[simp]
lemma preservesEvm_trans {s₀ s₁ s₂} :
  isOk s₁ → preservesEvm s₀ s₁ → preservesEvm s₁ s₂ → preservesEvm s₀ s₂ := by
  unfold preservesEvm
  match s₀ with
  | .OutOfFuel | .Checkpoint _ => simp
  | .Ok e₀ σ₀ =>
    match s₂ with
    | .OutOfFuel | .Checkpoint _ => simp
    | .Ok e₂ σ₂ =>
      match s₁ with
      | .OutOfFuel | .Checkpoint _ => simp
      | .Ok e₁ σ₁ =>
        simp
        exact preserved_trans

@[simp]
lemma sload_eq_of_preservesEvm {s s' : State} {a : UInt256} :
  isOk s → isOk s' → preservesEvm s s' →
  s.evm.sload a = s'.evm.sload a := by
  unfold isOk preservesEvm
  cases s <;> cases s' <;> simp
  intro h
  unfold EVMState.sload EVMState.lookupAccount
  rw [ preserves_account_map h
     , preserves_execution_env h
     ]

end Clear.Utilities
