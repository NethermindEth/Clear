import Clear.ExecLemmas
import Clear.SizeLemmas

/--
  A nonempty list can be represented as an "init" and a last element.
-/
lemma List.exists_append_singleton_of_nonempty {α : Type} {xs : List α}
  (h : 1 ≤ xs.length) : ∃ init last, xs = init ++ [last] := by
  have h₁ := @List.exists_of_length_succ α (xs.reverse.length - 1) (xs.reverse)
  simp at h₁
  rcases xs with _ | ⟨hd, tl⟩
  · simp at h
  · norm_num at h₁
    rcases h₁ with ⟨last, init, hrev⟩
    rw [←List.reverse_inj] at hrev
    aesop
    
@[simp]
lemma List.mapAccumr_nil {α β σ : Type} {f : α → σ → σ × β} {s : σ} :
  List.mapAccumr f [] s = (s, []) := by
  conv_lhs => unfold List.mapAccumr

@[simp]
lemma List.mapAccumr_cons {α β σ : Type} {f : α → σ → σ × β} {x : α} {xs : List α} {s : σ} :
  List.mapAccumr f (x :: xs) s =
  let r := List.mapAccumr f xs s
  let z := f x r.1
  (z.1, z.2 :: r.2) := by
  conv_lhs => unfold List.mapAccumr

/--
  P holds for all m ≤ k' if and only if it holds for all m < 1 + k'.
-/
lemma forall_le_iff_forall_lt_succ {k' : ℕ} {P : ℕ → Prop} : (∀ m ≤ k', P m) ↔ (∀ m < (.succ k'), P m) := by
  simp_arith

namespace Clear.OutOfFuelLemmas

open Clear Ast Expr Stmt State EVMState PrimOps Interpreter SizeLemmas ExecLemmas

section

variable {s s₁ s₂ : State}
         {expr rhs cond arg : Expr}
         {args : List Expr}
         {evm : EVM}
         {store : VarStore}
         {stmt : Stmt}
         {stmts stmts₁ stmts₂ post body default' : List Stmt}
         {cases' : List (Literal × List Stmt)}
         {fuel m n k : ℕ}
         {var fname : String}
         {vars params rets : List String}
         {r t u v w x y z : Literal}
         {vals xs rest : List Literal}
         {f : FunctionDefinition}
         {prim : PrimOp}
         {fdef : FunctionDefinition}
         {c : Jump}

/--
  Running out of fuel from `Ok _ _` is an infinite loop.
-/
@[simp]
lemma isOutOfFuel_diverge_Ok : isOutOfFuel (diverge (Ok evm store)) := by
  simp [isOutOfFuel, diverge]
  
/--
  Varstore inserts preserve infinite loops.
-/
@[simp]
lemma isOutOfFuel_insert' : isOutOfFuel (s⟦var↦x⟧) = isOutOfFuel s := by
  unfold isOutOfFuel State.insert; aesop

/--
  Setting the EVM state preserves infinite loops.
-/
@[simp]
lemma isOutOfFuel_setEvm' : isOutOfFuel (s🇪⟦evm⟧) = isOutOfFuel s := by
  unfold setEvm isOutOfFuel; aesop

/--
  Reviving an old checkpoint (saved jump state) preserves infinite loops.
-/
@[simp]
lemma isOutOfFuel_reviveJump' : isOutOfFuel (reviveJump s) = isOutOfFuel s := by
  unfold reviveJump revive; aesop

/--
  Continues preserves infinite loops.
-/
@[simp]
lemma isOutOfFuel_setContinue' : isOutOfFuel s.setContinue = isOutOfFuel s := by
  unfold setContinue; aesop

/--
  Breaks preserves infinite loops.
-/
@[simp]
lemma isOutOfFuel_setBreak' : isOutOfFuel s.setBreak = isOutOfFuel s := by
  unfold setBreak; aesop

/--
  Leaves preserves infinite loops.
-/
@[simp]
lemma isOutOfFuel_setLeave' : isOutOfFuel s.setLeave = isOutOfFuel s := by
  unfold setLeave; aesop

/--
  Making a state `Ok` preserves infinite loops (because it only throws away checkpoints).
-/
@[simp]
lemma isOutOfFuel_mkOk' : isOutOfFuel (mkOk s) = isOutOfFuel s := by
  unfold isOutOfFuel at *; unfold mkOk
  aesop

/--
  Setting the variable store preserves infinite loops.
-/
@[simp]
lemma isOutOfFuel_setStore' : isOutOfFuel (s.setStore s₁) = isOutOfFuel s := by
  unfold isOutOfFuel setStore; aesop

/--
  Multifills preserve infinite loops.
-/
@[simp]
lemma isOutOfFuel_multifill' : isOutOfFuel (multifill vars vals s) = isOutOfFuel s := by
  unfold multifill
  induction List.zip vars vals <;> aesop

/--
  Call initialization preserves infinite loops.
-/
@[simp]
lemma isOutOfFuel_initcall' : isOutOfFuel (initcall params xs s) = isOutOfFuel s := by
  unfold initcall; aesop

/--
  Running out of fuel preserves infinite loops.
-/
@[aesop unsafe 10% apply]
lemma isOutOfFuel_diverge (h : isOutOfFuel s) : isOutOfFuel (diverge s) := by
  unfold isOutOfFuel at *; unfold diverge
  aesop

/--
  A diverged state is an infinite loop if the original state is Ok.
-/
@[aesop unsafe 20% apply]
lemma isOutOfFuel_diverge_of_Ok (h : isOk s) : isOutOfFuel (diverge s) := by
  unfold isOutOfFuel at *; unfold diverge; unfold isOk at h
  aesop

@[aesop unsafe 10% apply]
lemma isOutOfFuel_mkOk (h : isOutOfFuel s) : isOutOfFuel (mkOk s) := by
  unfold isOutOfFuel at *; unfold mkOk
  aesop

@[aesop unsafe 10% apply]
lemma isOutOfFuel_insert (h : isOutOfFuel s) : isOutOfFuel (s⟦var↦x⟧) := by
  unfold State.insert isOutOfFuel
  rcases s <;> simp at *

@[aesop unsafe 10% apply]
lemma isOutOfFuel_setEvm (h : isOutOfFuel s) : isOutOfFuel (setEvm evm s) := by
  unfold isOutOfFuel setEvm
  rcases s <;> simp at *

@[aesop unsafe 10% apply]
lemma isOutOfFuel_setContinue (h : isOutOfFuel s) : isOutOfFuel (setContinue s) := by
  unfold isOutOfFuel setContinue
  rcases s <;> simp at *

@[aesop unsafe 10% apply]
lemma isOutOfFuel_setBreak (h : isOutOfFuel s) : isOutOfFuel (setBreak s) := by
  unfold isOutOfFuel setBreak
  rcases s <;> simp only [isOutOfFuel] at *

@[aesop unsafe 10% apply]
lemma isOutOfFuel_setLeave (h : isOutOfFuel s) : isOutOfFuel (setLeave s) := by
  unfold isOutOfFuel setLeave
  rcases s <;> simp only [isOutOfFuel] at *

@[aesop unsafe 10% apply]
lemma isOutOfFuel_setStore (h : isOutOfFuel s) : isOutOfFuel (s.setStore s₁) := by
  unfold isOutOfFuel setStore
  rcases s <;> simp only [isOutOfFuel] at *

@[aesop unsafe 10% apply]
lemma isOutOfFuel_reviveJump (h : isOutOfFuel s) : isOutOfFuel (reviveJump s) := by
  rw [isOutOfFuel_reviveJump']
  exact h

@[aesop unsafe 10% apply]
lemma isOutOfFuel_multifill (h : isOutOfFuel s) : isOutOfFuel (multifill vars vals s) := by
  rw [isOutOfFuel_multifill']; assumption

@[aesop unsafe 10% apply]
lemma isOutOfFuel_initcall (h : isOutOfFuel s) : isOutOfFuel (initcall params xs s) := by
  rw [isOutOfFuel_initcall']; assumption

-- | If we overwrite the status in `s` with the status in `s₁` when the status
-- in `s₁` is non-Ok, then infinite loops propagate from `s₁` to the resulting
-- state.
@[aesop unsafe 10% apply]
lemma isOutOfFuel_overwrite? (h₁ : isOutOfFuel s₁) : isOutOfFuel (s.overwrite? s₁)
:= by
  unfold overwrite?; unfold isOutOfFuel at *
  aesop

@[aesop unsafe 10% apply]
lemma isOutOfFuel_overwrite?' (h₁ : isOk s₁) (h : isOutOfFuel s) : isOutOfFuel (s.overwrite? s₁) := by
  unfold overwrite?; unfold isOutOfFuel at *
  rcases s₁ <;> aesop

@[aesop unsafe 10% apply]
lemma isOutOfFuel_diverge_mkOk : isOutOfFuel (diverge (mkOk s)) := by
  unfold mkOk diverge isOutOfFuel
  rcases s <;> aesop

/-- 
  Helper lemma to show that `keccak256` primop preserves infinite loops.
-/
lemma isOutOfFuel_keccak256 (h : isOutOfFuel s) :
  isOutOfFuel <|
    (match s.evm.keccak256 x y with
    | .some (val, evm') => (s.setEvm evm', [val])
    | _ => (s.setEvm s.evm.addHashCollision, [0])).1 := by aesop

/--
  Helper lemma to show that `returndatacopy` primop preserves infinite loops.
-/
lemma isOutOfFuel_returndatacopy (h : isOutOfFuel s) :
  isOutOfFuel <|
    (match returndatacopy s.evm x y z with
      | some evm' => (s🇪⟦evm'⟧, ([] : List Literal))
      | none => (s.setEvm (s.evm.evm_revert x z), [])).1 := by aesop

-- ============================================================================
--  PRIMCALL INFINITE LOOP PRESERVATION LEMMAS BY FUNCTION ARITY
-- ============================================================================

lemma isOutOfFuel_execPrimCall0 (h : isOutOfFuel s) : isOutOfFuel (primCall s prim []).1 := by
  unfold primCall
  cases prim <;> aesop

lemma isOutOfFuel_execPrimCall1 (h : isOutOfFuel s) : isOutOfFuel (primCall s prim [x]).1 := by
  unfold primCall
  cases prim <;> aesop

lemma isOutOfFuel_execPrimCall2 (h : isOutOfFuel s) : isOutOfFuel (primCall s prim [x, y]).1 := by
  unfold primCall
  cases prim <;> aesop

lemma isOutOfFuel_execPrimCall3 (h : isOutOfFuel s) : isOutOfFuel (primCall s prim [x, y, z]).1 := by
  unfold primCall
  cases prim <;> aesop

lemma isOutOfFuel_execPrimCall4 (h : isOutOfFuel s) : isOutOfFuel (primCall s prim [w, x, y, z]).1 := by
  unfold primCall
  cases prim <;> aesop

lemma isOutOfFuel_execPrimCall5 (h : isOutOfFuel s) : isOutOfFuel (primCall s prim [v, w, x, y, z]).1 := by
  unfold primCall
  cases prim <;> aesop

lemma isOutOfFuel_execPrimCall6 (h : isOutOfFuel s) : isOutOfFuel (primCall s prim [u, v, w, x, y, z]).1 := by
  unfold primCall
  cases prim <;> aesop

lemma isOutOfFuel_execPrimCall7 (h : isOutOfFuel s) : isOutOfFuel (primCall s prim [t, u, v, w, x, y, z]).1 := by
  unfold primCall
  cases prim <;> aesop

lemma isOutOfFuel_execPrimCall8 (h : isOutOfFuel s) : isOutOfFuel (primCall s prim (r :: t :: u :: v :: w :: x :: y :: z :: rest)).1 := by
  unfold primCall
  cases prim <;> aesop

-- ============================================================================
--  INTERPRETER-FUNCTIONS-PRESERVE-INFINITE-LOOPS LEMMAS
-- ============================================================================

/--
  An `execPrimCall` preserves error states.
-/
@[aesop unsafe 10% apply]
lemma execPrimCall_Inf (h : isOutOfFuel s) : isOutOfFuel (primCall s prim xs).1 := by
  -- Performance issues, need to break some abstraction by creating
  -- 'equivalence classes' on function arity, among other scary things.
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨i, rest⟩⟩⟩⟩⟩⟩⟩⟩
  · exact isOutOfFuel_execPrimCall0 h
  · exact isOutOfFuel_execPrimCall1 h
  · exact isOutOfFuel_execPrimCall2 h
  · exact isOutOfFuel_execPrimCall3 h
  · exact isOutOfFuel_execPrimCall4 h
  · exact isOutOfFuel_execPrimCall5 h
  · exact isOutOfFuel_execPrimCall6 h
  · exact isOutOfFuel_execPrimCall7 h
  · exact isOutOfFuel_execPrimCall8 h

/--
  Evaluating arguments preserves infinite loops given inductive
-/
lemma mapAccumr_Inf_ih
  (h : isOutOfFuel s)
  (exec_ih : (∀ k ≤ fuel, ∀ {s : State} {stmt : Stmt}, isOutOfFuel s → isOutOfFuel (exec k stmt s)))
  (eval_ih :
    ∀ m ≤ fuel,
    ∀ {s : State} {expr : Expr},
      isOutOfFuel s
      → (∀ k ≤ m, ∀ {s : State} {stmt : Stmt}, isOutOfFuel s → isOutOfFuel (exec k stmt s))
      → isOutOfFuel (eval m expr s).1) :
    isOutOfFuel (List.mapAccumr (eval fuel) args s).1 := by
  induction args generalizing s <;> aesop

/--
  Evaluating arguments preserves infinite loops given inductive hypotheses that `eval` does so.
-/
lemma mapAccumr_Inf_ih'
  (h : isOutOfFuel s)
  (eval_ih : (∀ k ≤ fuel, ∀ {s : State} {expr : Expr}, isOutOfFuel s → isOutOfFuel (eval k expr s).1)) :
  isOutOfFuel (List.mapAccumr (eval fuel) args s).1 := by
  induction args generalizing s <;> aesop

lemma cons'_Inf {inputs : State × List Literal}
  (h : isOutOfFuel inputs.1) : isOutOfFuel (cons' x inputs).1 := by aesop

lemma evalTail_Inf_ih
  {inputs : State × Literal}
  (h : isOutOfFuel inputs.1)
  (hsize : sizeOf args < sizeOf expr)
  (ih : ∀ {s : State}, isOutOfFuel s → sizeOf args < sizeOf expr → isOutOfFuel (evalArgs fuel args s).1) :
  isOutOfFuel (evalTail fuel args inputs).1 := by unfold evalTail; aesop

lemma evalArgs_Inf_ih
  (h : isOutOfFuel s)
  (hsize : sizeOf args < sizeOf expr)
  (eval_ih : ∀ {s} {expr'}, isOutOfFuel s → sizeOf expr' < sizeOf expr → isOutOfFuel (eval fuel expr' s).1) :
  isOutOfFuel (evalArgs fuel args s).1 := by
  induction args generalizing s with
    | nil => exact h
    | cons x xs ih =>
      unfold evalArgs evalTail
      have : sizeOf x < sizeOf expr := by simp at hsize; linarith
      have : sizeOf xs < sizeOf expr := by simp at hsize; linarith
      aesop

/--
  The `call` helper function for user-defined function calls preserves infinite loops.
-/
@[aesop unsafe 10% apply]
lemma call_Inf (h : isOutOfFuel s) : isOutOfFuel (call fuel xs fdef s).1 := by
  unfold call
  apply isOutOfFuel_setStore
  apply isOutOfFuel_overwrite?
  assumption

/--
  The `evalCall` helper function for user-defined function calls preserves infinite loops.
-/
@[aesop unsafe 10% apply]
lemma evalCall_Inf {inputs : State × List Literal}
  (h : isOutOfFuel inputs.1) : isOutOfFuel (evalCall fuel fdef inputs).1 := by
  unfold evalCall
  exact call_Inf h

/--
  The `execCall` helper function for user-defined function calls preserves infinite loops.
-/
@[aesop unsafe 10% apply]
lemma execCall_Inf {inputs : State × List Literal} (h : isOutOfFuel inputs.1) :
  isOutOfFuel (execCall fuel fdef vars inputs) := by
  unfold execCall
  exact isOutOfFuel_multifill (call_Inf h)

/--
  Apply transitivity to obtain a nicer form for an `eval` inductive hypothesis.
-/
lemma eval_ih_trans
  {P : Expr → State → Prop}
  (ih : ∀ m < sizeOf expr, ∀ {s : State} {expr' : Expr}, isOutOfFuel s → sizeOf expr' = m → P expr' s) :
  ∀ {s} {expr'}, isOutOfFuel s → sizeOf expr' < sizeOf expr → P expr' s := by
  intros _ expr' hs hsize
  exact ih (sizeOf expr') hsize hs rfl

/--
  Apply transitivity to obtain a nicer form for an `exec` inductive hypothesis.
-/
lemma exec_ih_trans
  {P : Stmt → State → Prop}
  (ih : ∀ m < sizeOf stmt, ∀ {s} {stmt'}, isOutOfFuel s → sizeOf stmt' = m → P stmt' s) :
  ∀ {s} {stmt'}, isOutOfFuel s → sizeOf stmt' < sizeOf stmt → P stmt' s := by
  intros _ stmt' hs hsize
  exact ih (sizeOf stmt') hsize hs rfl

lemma execPrimCall_evalArgs_Inf_ih
  (h : isOutOfFuel s)
  (hsize : sizeOf args < sizeOf expr)
  (eval_ih : ∀ {s} {expr'}, isOutOfFuel s → sizeOf expr' < sizeOf expr → isOutOfFuel (eval fuel expr' s).1) :
  isOutOfFuel (primCall (evalArgs fuel args s).1 prim (evalArgs fuel args s).2.reverse).1 :=
  execPrimCall_Inf (@evalArgs_Inf_ih _ expr _ _ h hsize eval_ih)

/--
  An `eval` preserves infinite loops.
-/
lemma eval_Inf (h : isOutOfFuel s) : isOutOfFuel (eval fuel expr s).1 := by
  generalize hk : sizeOf expr = k
  rename' expr => expr'
  induction k using Nat.case_strong_induction_on generalizing s expr' with
    | hz =>
        have : 0 < sizeOf expr' := Expr.zero_lt_sizeOf
        aesop
    | hi k' ih =>
        rw [forall_le_iff_forall_lt_succ] at ih
        rw [← hk] at ih
        clear hk
        unfold eval
        have ih₁ := @eval_ih_trans _ _ ih
        clear ih
        rcases expr' with ⟨prim, args⟩ | ⟨f, args⟩ | var | val <;> simp only [Nat.add_eq, add_zero]
        · generalize hexpr : (PrimCall prim args) = expr at *
          unfold evalPrimCall reverse' head'
          simp only
          apply @execPrimCall_evalArgs_Inf_ih _ expr _ _ _ h
          rw [← hexpr]
          simp
          assumption
        · generalize hexpr : (Call f args) = expr at *
          apply evalCall_Inf
          apply @evalArgs_Inf_ih _ expr args.reverse _ h
          rw [← hexpr]
          simp
          assumption
        · assumption
        · assumption

lemma evalTail_Inf_ih'
  {inputs : State × Literal}
  (h : isOutOfFuel inputs.1)
  (ih : ∀ {s : State}, isOutOfFuel s → isOutOfFuel (evalArgs fuel args s).1)
: isOutOfFuel (evalTail fuel args inputs).1
:= by
  unfold evalTail
  apply cons'_Inf
  apply ih h

lemma evalArgs_Inf
  (h : isOutOfFuel s)
: isOutOfFuel (evalArgs fuel args s).1
:= by
  induction args generalizing s with
    | nil => exact h
    | cons x xs ih =>
      unfold evalArgs
      apply evalTail_Inf_ih'
      apply eval_Inf h
      assumption

-- | Executing a call directly from `exec` preserves infinite loops.
lemma Call_Inf
  (h : isOutOfFuel s)
: isOutOfFuel (exec fuel (LetCall vars f args) s)
:= by
  rw [LetCall']
  apply execCall_Inf
  apply evalArgs_Inf h

-- | Executing a call directly from `exec` preserves infinite loops.
lemma AssignCall_Inf
  (h : isOutOfFuel s)
: isOutOfFuel (exec fuel (AssignCall vars f args) s)
:= by
  rw [AssignCall']
  apply execCall_Inf
  apply evalArgs_Inf h

-- | Executing a primop call directly from `exec` preserves infinite loops.
lemma PrimCall_Inf
  (h : isOutOfFuel s)
: isOutOfFuel (exec fuel (LetPrimCall vars prim args) s)
:= by
  rw [LetPrimCall']
  apply isOutOfFuel_multifill
  apply execPrimCall_Inf
  apply evalArgs_Inf h

-- | Executing a primop call directly from `exec` preserves infinite loops.
lemma AssignPrimCall_Inf
  (h : isOutOfFuel s)
: isOutOfFuel (exec fuel (AssignPrimCall vars prim args) s)
:= by
  rw [AssignPrimCall']
  apply isOutOfFuel_multifill
  apply execPrimCall_Inf
  apply evalArgs_Inf h

-- | Lets preserve infinite loops.
lemma Let_Inf (h : isOutOfFuel s) : isOutOfFuel (exec fuel (Let vars) s)
:= by
  rw [Let']
  induction vars with
  | nil =>
    rw [List.foldr_nil]
    assumption
  | cons x xs ih =>
    rw [List.foldr_cons]
    apply isOutOfFuel_insert
    exact ih

-- | LetEqs preserve infinite loops.
lemma LetEq_Inf
  (h : isOutOfFuel s)
: isOutOfFuel (exec fuel (LetEq var rhs) s)
:= by
  rw [LetEq']
  apply isOutOfFuel_insert
  apply eval_Inf h

-- | Assigns preserve infinite loops.
lemma Assign_Inf
  (h : isOutOfFuel s)
: isOutOfFuel (exec fuel (Assign var rhs) s)
:= by
  rw [Assign']
  apply isOutOfFuel_insert
  apply eval_Inf h

lemma ExprStmtCall_Inf
  (h : isOutOfFuel s)
: isOutOfFuel (exec fuel (ExprStmtCall f args) s)
:= by
  rw [ExprStmtCall']
  apply execCall_Inf
  apply evalArgs_Inf
  assumption

lemma ExprStmtPrimCall_Inf
  (h : isOutOfFuel s)
: isOutOfFuel (exec fuel (ExprStmtPrimCall prim args) s)
:= by
  rw [ExprStmtPrimCall']
  apply isOutOfFuel_multifill
  apply execPrimCall_Inf
  apply evalArgs_Inf h

lemma Block_Inf_ih
  (h : isOutOfFuel s)
  (exec_ih : ∀ {s : State} {stmt' : Stmt}, isOutOfFuel s → sizeOf stmt' < sizeOf (Block stmts) → isOutOfFuel (exec fuel stmt' s))
: isOutOfFuel (exec fuel (Block stmts) s)
:= by
  induction stmts generalizing s with
    | nil =>
      rw [nil]
      assumption
    | cons x xs ih =>
      rw [cons]
      apply @ih (exec fuel x s)
      apply exec_ih h (Stmt.sizeOf_head_lt_sizeOf)
      intros s stmt hs hsize
      apply exec_ih hs
      transitivity sizeOf (Stmt.Block xs)
      exact hsize
      exact Stmt.sizeOf_head_lt_sizeOf_tail

-- | Switch statements preserve infinite loops.
lemma Switch_Inf
  (h : isOutOfFuel s)
  (hcases : sizeOf cases' < sizeOf stmt)
  (hdefault : sizeOf (Block default') < sizeOf stmt)
  (exec_ih : ∀ {s : State} {stmt' : Stmt}, isOutOfFuel s → sizeOf stmt' < sizeOf stmt → isOutOfFuel (exec fuel stmt' s))
: isOutOfFuel (exec fuel (Switch cond cases' default') s)
:= by
  rw [Switch']
  simp only
  unfold execSwitchCases
  induction cases' generalizing s with
  | nil =>
    simp
    apply Block_Inf_ih
    apply eval_Inf
    assumption
    intros s stmt₁ hs hsize
    apply exec_ih hs
    transitivity sizeOf (Block default')
    assumption
    assumption
  | cons x xs ih =>
    simp
    split_ifs with hif
    apply Block_Inf_ih
    apply eval_Inf
    assumption
    intros s stmt₁ hs hsize
    apply exec_ih hs
    transitivity sizeOf (x :: xs)
    transitivity sizeOf (Block x.2)
    assumption
    rcases x with ⟨val, branch⟩
    simp_arith
    assumption
    unfold execSwitchCases
    apply ih h
    transitivity sizeOf (x :: xs)
    · rcases xs with _ | _ <;> simp_arith
    · assumption

-- | If statements preserve infinite loops.
lemma If_Inf_ih
  (h : isOutOfFuel s)
  (hbody : sizeOf (Block body) < sizeOf stmt)
  (exec_ih : ∀ {s : State} {stmt' : Stmt}, isOutOfFuel s → sizeOf stmt' < sizeOf stmt → isOutOfFuel (exec fuel stmt' s))
: isOutOfFuel (exec fuel (Stmt.If cond body) s)
:= by
  rw [If']
  dsimp only
  split_ifs
  · apply exec_ih _ hbody
    apply eval_Inf h
  · apply eval_Inf h

-- | For loops preserve infinite loops.
lemma For_Inf
  (h : isOutOfFuel s)
: isOutOfFuel (exec fuel (Stmt.For cond post body) s)
:= by
  rw [For']
  rcases fuel with _ | _ | fuel <;> dsimp (config := {zeta := false}) only
  · apply isOutOfFuel_diverge h
  · apply isOutOfFuel_diverge h
  · generalize hres : eval fuel cond (mkOk s) = res at *
    rcases res with ⟨s₁, x⟩
    have hres' : (eval fuel cond (mkOk s)).1 = s₁ ∧ (eval fuel cond (mkOk s)).2 = x := by aesop
    have hs₁ := hres'.1
    dsimp (config := {zeta := false}) only
    by_cases hcond : x = 0
    · rw [if_pos]
      apply isOutOfFuel_overwrite?
      assumption
      assumption
    · rw [if_neg hcond]
      dsimp only
      rcases fuel with _ | fuel
      · generalize hs₂ : exec Nat.zero (Block body) s₁ = s₂ at *
        rcases s₂ with _ | _ | c
        · simp only [Nat.zero_eq, Option.isNone_none, ite_true]
          apply isOutOfFuel_overwrite?
          assumption
        · simp only [Nat.zero_eq, Option.isNone_none, ite_true]
          apply isOutOfFuel_overwrite?
          assumption
        · rcases c with _ | _ | _ <;> simp only
          · apply isOutOfFuel_overwrite?
            assumption
          · apply isOutOfFuel_overwrite?
            assumption
          · apply isOutOfFuel_overwrite?
            assumption
      · generalize hs₂ : exec (.succ fuel) (Block body) s₁ = s₂ at *
        rcases s₂ with _ | _ | c <;> try simp only
        · rw [← hs₂]
          apply isOutOfFuel_overwrite?
          assumption
        · rw [← hs₂]
          apply isOutOfFuel_overwrite?
          assumption
        · rcases c with _ | _ | _ <;> simp only <;> rw [←hs₂]
          · apply isOutOfFuel_overwrite?
            assumption
          · apply isOutOfFuel_overwrite?
            assumption
          · apply isOutOfFuel_overwrite?
            assumption

-- | An `exec` preserves infinite loops.
@[aesop unsafe 10% apply]
lemma exec_Inf (h : isOutOfFuel s) : isOutOfFuel (exec fuel stmt s)
:= by
  generalize hk : sizeOf stmt = k
  rename' stmt => stmt'
  induction k using Nat.case_strong_induction_on generalizing s stmt' with
  | hz =>
    rename' stmt' => stmt
    have : 0 < sizeOf stmt := Stmt.zero_lt_sizeOf
    rw [hk] at this
    linarith
  | hi k' ih =>
    rename' stmt' => stmt
    rw [forall_le_iff_forall_lt_succ] at ih
    rw [← hk] at ih
    clear hk
    have ih₁ := @exec_ih_trans _ _ ih
    clear ih
    rcases stmt with
        stmts                       -- Block
      | var                         -- Let
      | ⟨var, rhs⟩                  -- LetEq
      | ⟨vars, f, args⟩             -- LetCall
      | ⟨vars, prim, args⟩          -- LetPrimCall
      | ⟨var, rhs⟩                  -- Assign
      | ⟨vars, f, args⟩             -- AssignCall
      | ⟨vars, prim, args⟩          -- AssignPrimCall
      | ⟨f, args⟩
      | ⟨prim, args⟩
      | ⟨cond, cases', default'⟩
      | ⟨cond, post, body⟩
      | ⟨cond, body⟩
    · exact Block_Inf_ih h ih₁
    · exact Let_Inf h
    · exact LetEq_Inf h
    · exact Call_Inf h
    · exact PrimCall_Inf h
    · exact Assign_Inf h
    · exact AssignCall_Inf h
    · exact AssignPrimCall_Inf h
    · exact ExprStmtCall_Inf h
    · exact ExprStmtPrimCall_Inf h
    · apply @Switch_Inf _ _ (Switch cond cases' default') _ _ _ h
      simp_arith
      simp_arith
      rcases cases'
      simp_arith
      apply le_add_right
      apply Expr.zero_lt_sizeOf
      apply ih₁
    · apply For_Inf h
    · apply @If_Inf_ih _ _ (If cond body) _ _ h
      simp_arith
      rcases cond <;> exact ih₁
    · exact isOutOfFuel_setContinue h
    · exact isOutOfFuel_setBreak h
    · exact isOutOfFuel_setLeave h

-- ============================================================================
--  TACTICS
-- ============================================================================

open Lean Parser Elab Tactic in
elab "preprocess_zero_case" hfuel:ident : tactic => do
  evalTactic <| ← `(tactic|
    intros h;
    revert $hfuel;
    rw [←h];
    intros hfuel;
    exfalso;
    apply hfuel;
    clear h hfuel;
  )

-- | Handle the out-of-fuel case (infinite loop).
open Lean Parser Elab Tactic in
elab "refuel" fuel:ident hfuel:ident : tactic => do
  evalTactic <| ← `(tactic|
    rcases $fuel:ident with _ | $fuel;
    preprocess_zero_case $hfuel;
    (try rw [cons]);
    (try rw [exec_zero]);
    (try rw [eval_zero']);
    (try rw [eval_zero]);
    (try apply traverse_Inf);
    (try apply exec_Inf);
    (try apply eval_Inf);
    {
      first
        | aesop
        | split_ifs <;> simp only <;> aesop
    };
    swap;
    rw [Nat.succ_eq_add_one] at *;
  )

open Lean Parser Elab Tactic in
elab "post_abstraction_refuel" fuel:ident hfuel:ident hjump:ident s:casesTarget : tactic => do
  evalTactic <| ← `(tactic|
    rcases $fuel:ident with _ | $fuel;
    rcases $s with ⟨evm, store⟩ | _ | c | c;
    preprocess_zero_case $hfuel;
    aesop; swap;
    preprocess_zero_case $hfuel;
    aesop; rotate_left 2;
    preprocess_zero_case $hjump;
    aesop; swap;
    preprocess_zero_case $hjump;
    aesop; rotate_left 2;
    rw [Nat.succ_eq_add_one] at *;
  )

end

end Clear.OutOfFuelLemmas
