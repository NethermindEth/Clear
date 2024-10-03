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

@[simp]
lemma preservesEvm_rfl {s : State} : preservesEvm s s := by
  unfold preservesEvm
  cases s <;> simp

@[simp]
lemma preservesEvm_trans {s₀ s₁ s₂} (h : s₁.isOk) :
  preservesEvm s₀ s₁ → preservesEvm s₁ s₂ → preservesEvm s₀ s₂ := by
  unfold preservesEvm
  cases s₀ <;> cases s₁ <;> cases s₂ <;> simp_all
  exact preserved_trans

lemma sload_eq_of_preservesEvm
  {s s' : State} {a : UInt256} (h : s.isOk) (h' : s'.isOk) (hss : preservesEvm s s') :
  s.evm.sload a = s'.evm.sload a := by
  cases s <;> cases s' <;> simp_all
  simp only [evm]
  unfold EVMState.sload EVMState.lookupAccount
  rw [ preserves_account_map hss
     , preserves_execution_env hss
     ]

end Clear.Utilities
