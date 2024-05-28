import Clear.Interpreter
import Clear.ExecLemmas
import Clear.OutOfFuelLemmas
import Clear.JumpLemmas
import Clear.YulNotation

namespace Clear.Abstraction

section

open Clear Ast EVMState State Interpreter PrimOps ExecLemmas

variable {s s₀ s₁ sEnd : State}
         {rest : List Stmt}
         {stmt : Stmt}
         {n : ℕ}
         {R : State → State → Prop}

-- | General form for relational specs (concrete and abstract).
@[aesop safe 0 unfold (rule_sets := [Clear.aesop_spec])]
def Spec (R : State → State → Prop) (s₀ s₁ : State) : Prop :=
  match s₀ with
    | OutOfFuel => ❓ s₁
    | Checkpoint c => s₁.isJump c
    | Ok _ _ => ¬ ❓ s₁ → R s₀ s₁

@[simp]
lemma Spec_ok_unfold {P : State → State → Prop} :
  ∀ {s s' : State}, s.isOk → ¬ ❓ s' → Spec P s s' → P s s' := by
    intros s s' h h'
    unfold Spec
    aesop

open Lean Elab Tactic in
elab "clr_spec" "at" h:ident : tactic => do
  evalTactic <| ← `(tactic| (
    apply Spec_ok_unfold (by aesop_spec) (by aesop_spec) at $h
  ))

-- | Specs preserve infinite loops.
lemma isOutOfFuel_Spec (spec : Spec R s₀ s₁) (h : isOutOfFuel s₀) : isOutOfFuel s₁ := by
  aesop_spec

-- | Non-divergentness propagates backwards through specs.
lemma not_isOutOfFuel_Spec (spec : Spec R s₀ s₁) (h : ¬ isOutOfFuel s₁) : ¬ isOutOfFuel s₀ := by
  intros hs₀
  aesop_spec

-- ============================================================================
--  TACTICS
-- ============================================================================

open Lean Elab Parser Tactic in
/--
Abstract a statement given a lemma (code → abs) and an abstract spec.
-/
elab "abstract " hcodeabs:ident stmt:ident " with " sname₁:ident hname:ident : tactic =>
  withMainContext do
    evalTactic <| ← `(tactic|
      -- Find the end-of-abstraction state.
      rw [←$stmt]; generalize hs₁ : exec _ $stmt _ = $sname₁;

      -- Specialize the (code → abs) lemma with the aforementioned state.
      have $hname := $hcodeabs $sname₁ hs₁;
    )

end

section

open Lean Elab Tactic Conv

syntax (name := let_unfold) " let_unfold " ident : conv

def letUnfold (e : Expr) (id : Name) : Expr :=
  e.replace λ e =>
    if e.isLet && e.letName! = id then
      some (e.letBody!.instantiate1 e.letValue!)
    else
      none

@[tactic let_unfold]
def convLetUnfold : Tactic
  | `(conv| let_unfold $id:ident) => do
    (← getMainGoal).withContext do
      let lhs ← getLhs

      changeLhs (letUnfold lhs id.getId)
  | _ => Lean.Elab.throwUnsupportedSyntax

macro " let_unfold " id:ident : tactic => `(tactic| conv => let_unfold $id)

end


end Clear.Abstraction

namespace Clear

open Abstraction State

lemma spec_of_ok {s₀ s₉ : State} {S₁ S₂ : State → State → Prop}
  (h : ¬❓ s₀ → (↑S₁ : State → State → Prop) s₀ s₉ → S₂ s₀ s₉) :
  Spec S₁ s₀ s₉ → Spec S₂ s₀ s₉ := by unfold Spec; aesop

@[aesop norm 100 simp (rule_sets := [Clear.aesop_spec])]
lemma isOutOfFuel_iff_s_eq_OutOfFuel {s : State} : ❓ s ↔ (s = OutOfFuel) := by unfold isOutOfFuel; aesop

@[simp]
lemma setBreak_OutOfFuel_eq_OutOfFuel : 💔OutOfFuel = OutOfFuel := rfl  

@[aesop norm 100 simp (rule_sets := [Clear.aesop_spec])]
lemma setBreak_ok_eq_checkpoint {evm : EVM} {varstore : VarStore} :
  💔Ok evm varstore = Checkpoint (.Break evm varstore) := rfl

@[aesop norm 100 simp (rule_sets := [Clear.aesop_spec])]
lemma isJump_jump_eq {s : State} {jmp : Jump} :
  isJump jmp s ↔ Checkpoint jmp = s := by
  unfold isJump; aesop

@[aesop safe 0 apply (rule_sets := [Clear.aesop_spec])]
lemma isOk_of_insert {s} (h : isOk s) {k} {v} :
  isOk (s⟦k↦v⟧) := by unfold isOk State.insert at *; aesop

-- @[aesop norm 0 simp (rule_sets := [Clear.aesop_varstore])]
-- lemma lookup_of_ok {var} {evm} {varstore} :
--   State.lookup! var (.Ok evm varstore) = (varstore.lookup var).get! := rfl

-- @[aesop safe apply (rule_sets := [Clear.aesop_spec])]
-- lemma isPure_of_isPure_ok {s} {evm} {vs} (h : isPure (Ok evm vs) s) : isPure s := by
--   done

open Lean Elab Tactic in
elab "clr_funargs" : tactic => do
  evalTactic <| ← `(tactic| (
    unfold State.initcall
    try unfold State.insert
    unfold State.setStore
    simp only [multifill_cons, multifill_nil', isOk_insert, isOk_Ok, isOutOfFuel_Ok,
      not_false_eq_true, imp_false, Ok.injEq, and_imp, forall_apply_eq_imp_iff₂,
      forall_apply_eq_imp_iff]
    repeat (rw [←State.insert])
  ))

open Lean Elab Tactic in
elab "clr_funargs" "at" h:ident : tactic => do
  evalTactic <| ← `(tactic| (
    unfold State.initcall at $h:ident
    try unfold State.insert at $h:ident
    unfold State.setStore at $h:ident
    simp only [multifill_cons, multifill_nil', isOk_insert, isOk_Ok, isOutOfFuel_Ok,
      not_false_eq_true, imp_false, Ok.injEq, and_imp, forall_apply_eq_imp_iff₂,
      forall_apply_eq_imp_iff] at $h:ident
    repeat (rw [←State.insert] at $h:ident)    
  ))

end Clear
