import Clear.OutOfFuelLemmas

-- TODO(chore): Tag with appropriate aesops, not the general ones.

namespace Clear.JumpLemmas

open Clear Ast Expr Stmt State EVMState PrimOps Interpreter SizeLemmas ExecLemmas OutOfFuelLemmas

section

variable {s s₁ s₂ : State}
         {expr rhs cond : Expr}
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
  Varstore inserts preserve jumps.
-/
@[simp]
lemma isJump_insert' : isJump c (s⟦var↦x⟧) = isJump c s := by unfold isJump State.insert; aesop

/--
  Setting the EVM state preserves jumps.
-/
@[simp]
lemma isJump_setEvm' : isJump c (s🇪⟦evm⟧) = isJump c s := by unfold setEvm isJump; aesop

/--
  Setting the variable store preserves jumps.
-/
@[simp]
lemma isJump_setStore' : isJump c (s.setStore s₁) = isJump c s := by unfold isJump setStore; aesop

/--
  Multifills preserve jumps.
-/
@[simp]
lemma isJump_multifill' : isJump c (multifill vars vals s) = isJump c s := by
  unfold multifill
  rcases s <;> simp only
  induction List.zip vars vals with
  | nil => simp only [isJump, State.insert, List.foldr_nil]
  | cons var' vars' ih =>
    unfold List.foldr
    rw [isJump_insert']
    rw [←ih]

/--
  Call initialization preserves jumps.
-/
@[simp]
lemma isJump_initcall' : isJump c (initcall params xs s) = isJump c s := by unfold initcall; aesop

/--
  Running out of fuel preserves jumps.
-/
@[aesop unsafe 10% apply]
lemma isJump_diverge (h : isJump c s) : isJump c (diverge s) := by unfold isJump diverge at *; aesop

@[aesop unsafe 10% apply]
lemma isJump_insert (h : isJump c s) : isJump c (s⟦var↦x⟧) := by
  unfold State.insert isJump
  rcases s with _ | _ | c' | c' <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_setEvm (h : isJump c s) : isJump c (setEvm evm s) := by
  unfold isJump setEvm
  rcases s with _ | _ | c' | c' <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_setContinue (h : isJump c s) : isJump c (setContinue s) := by
  unfold isJump setContinue
  rcases s with _ | _ | c' <;> dsimp only at * <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_setBreak (h : isJump c s) : isJump c (setBreak s) := by
  unfold isJump setBreak
  rcases s with _ | _ | c' <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_setLeave (h : isJump c s) : isJump c (setLeave s) := by
  unfold isJump setLeave
  rcases s with _ | _ | c' <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_setStore (h : isJump c s) : isJump c (s.setStore s₁) := by
  unfold isJump setStore
  rcases s <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_multifill (h : isJump c s) : isJump c (multifill vars vals s) :=
  isJump_multifill'.symm ▸ h

@[aesop unsafe 10% apply]
lemma isJump_initcall (h : isJump c s) : isJump c (initcall params xs s) :=
  isJump_initcall'.symm ▸ h

/--
  If we overwrite the status in `s` with the status in `s₁` when the status
  in `s₁` is non-Ok, then jumps propagate from `s₁` to the resulting
  state.
-/
@[aesop unsafe 10% apply]
lemma isJump_overwrite? (h₁ : isJump c s₁) : isJump c (s.overwrite? s₁) := by
  unfold overwrite? isJump at *; aesop

@[aesop unsafe 10% apply]
lemma isJump_overwrite?' (h₁ : isOk s₁) (h : isJump c s) : isJump c (s.overwrite? s₁) := by
  unfold overwrite? isJump at *
  rcases s₁ <;> aesop

/--
  Helper lemma to show that `keccak256` primop preserves jumps.
-/
@[aesop unsafe 10% apply]
lemma isJump_keccak256 (h : isJump c s) :
  isJump c <|
    (match s.evm.keccak256 x y with
    | .some (val, evm') => (s.setEvm evm', [val])
    | _ => (s.setEvm s.evm.addHashCollision, [0])).1 := by
  generalize eq : keccak256 s.evm x y = k
  rcases k with _ | ⟨val, evm'⟩ <;> aesop

/--
  Helper lemma to show that `returndatacopy` primop preserves jumps.
-/
@[aesop unsafe 10% apply]
lemma isJump_returndatacopy (h : isJump c s) :
  isJump c <|
    (match returndatacopy s.evm x y z with
      | some evm' => (s🇪⟦evm'⟧, ([] : List Literal))
      | none => (s.setEvm (s.evm.evm_revert x z), [])).1 := by
  generalize eq : returndatacopy s.evm x y z = r
  rcases r with _ | ⟨val, evm'⟩ <;> aesop

-- ============================================================================
--  PRIMCALL INFINITE LOOP PRESERVATION LEMMAS BY FUNCTION ARITY
-- ============================================================================

@[aesop unsafe 10% apply]
lemma isJump_execPrimCall0 (h : isJump c s) : isJump c (primCall s prim []).1 := by
  unfold primCall
  cases prim <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_execPrimCall1 (h : isJump c s) : isJump c (primCall s prim [x]).1 := by
  unfold primCall
  cases prim <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_execPrimCall2 (h : isJump c s) : isJump c (primCall s prim [x, y]).1 := by
  unfold primCall
  cases prim <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_execPrimCall3
  (h : isJump c s) : isJump c (primCall s prim [x, y, z]).1 := by
  unfold primCall
  cases prim <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_execPrimCall4 (h : isJump c s) : isJump c (primCall s prim [w, x, y, z]).1 := by
  unfold primCall
  cases prim <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_execPrimCall5 (h : isJump c s) : isJump c (primCall s prim [v, w, x, y, z]).1 := by
  unfold primCall
  cases prim <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_execPrimCall6 (h : isJump c s) : isJump c (primCall s prim [u, v, w, x, y, z]).1 := by
  unfold primCall
  cases prim <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_execPrimCall7 (h : isJump c s) : isJump c (primCall s prim [t, u, v, w, x, y, z]).1 := by
  unfold primCall
  cases prim <;> aesop

@[aesop unsafe 10% apply]
lemma isJump_execPrimCall8 (h : isJump c s) : isJump c (primCall s prim (r :: t :: u :: v :: w :: x :: y :: z :: rest)).1 := by
  unfold primCall
  cases prim <;> aesop

-- ============================================================================
--  INTERPRETER-FUNCTIONS-PRESERVE-INFINITE-LOOPS LEMMAS
-- ============================================================================

/--
  An `execPrimCall` preserves error states.
-/
@[aesop unsafe 10% apply]
lemma execPrimCall_Jump
  (h : isJump c s) : isJump c (primCall s prim xs).1 := by
  -- Performance issues, need to break some abstraction by creating
  -- 'equivalence classes' on function arity, among other scary things.
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨i, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
  aesop

/--
  Evaluating arguments preserves jumps given inductive
  hypotheses that `exec` does so and `eval` does so.
-/ 
@[aesop unsafe 10% apply]
lemma mapAccumr_Jump_ih
  (h : isJump c s)
  (exec_ih : (∀ k ≤ fuel, ∀ {s : State} {stmt : Stmt}, isJump c s → isJump c (exec k stmt s)))
  (eval_ih :
    ∀ m ≤ fuel,
    ∀ {s : State} {expr : Expr},
      isJump c s
      → (∀ k ≤ m, ∀ {s : State} {stmt : Stmt}, isJump c s → isJump c (exec k stmt s))
      → isJump c (eval m expr s).1) :
      isJump c (List.mapAccumr (eval fuel) args s).1 := by
  induction args generalizing s <;> aesop

/--
  Evaluating arguments preserves jumps given inductive hypotheses that `eval` does so.
-/
lemma mapAccumr_Jump_ih'
  (h : isJump c s)
  (eval_ih : (∀ k ≤ fuel, ∀ {s : State} {expr : Expr}, isJump c s → isJump c (eval k expr s).1)) :
  isJump c (List.mapAccumr (eval fuel) args s).1 := by
  induction args generalizing s <;> aesop

lemma cons'_Jump
  {inputs : State × List Literal}
  (h : isJump c inputs.1) : isJump c (cons' x inputs).1 := by
  unfold cons'; rcases inputs with ⟨s, xs⟩ ; aesop

lemma evalTail_Jump_ih
  {inputs : State × Literal}
  (h : isJump c inputs.1)
  (hsize : sizeOf args < sizeOf expr)
  (ih : ∀ {s : State}, isJump c s → sizeOf args < sizeOf expr → isJump c (evalArgs fuel args s).1) :
  isJump c (evalTail fuel args inputs).1 := by unfold evalTail; aesop

lemma evalArgs_Jump_ih
  (h : isJump c s)
  (hsize : sizeOf args < sizeOf expr)
  (eval_ih : ∀ {s} {expr'}, isJump c s → sizeOf expr' < sizeOf expr → isJump c (eval fuel expr' s).1) :
  isJump c (evalArgs fuel args s).1 := by
  induction args generalizing s with
    | nil => exact h
    | cons x xs ih =>
      unfold evalArgs
      simp at hsize
      apply @evalTail_Jump_ih expr xs fuel _ _ (eval_ih h ?_) (by linarith) (by assumption)
      linarith

/--
  The `call` helper function for user-defined function calls preserves jumps.
-/
@[aesop unsafe 10% apply]
lemma call_Jump (h : isJump c s) : isJump c (call fuel xs fdef s).1 := by unfold call; aesop

/--
  The `evalCall` helper function for user-defined function calls preserves jumps.
-/
@[aesop unsafe 10% apply]
lemma evalCall_Jump {inputs : State × List Literal}
  (h : isJump c inputs.1) : isJump c (evalCall fuel fdef inputs).1 := by
  unfold evalCall; exact call_Jump h

/--
  The `execCall` helper function for user-defined function calls preserves jumps.
-/
@[aesop unsafe 10% apply]
lemma execCall_Jump {inputs : State × List Literal}
  (h : isJump c inputs.1) : isJump c (execCall fuel fdef vars inputs) := by
  unfold execCall; exact isJump_multifill (call_Jump h)

/--
  Apply transitivity to obtain a nicer form for an `eval` inductive hypothesis.
-/
@[aesop unsafe 10% apply]
lemma eval_ih_trans {P : Expr → State → Prop}
  (ih : ∀ m < sizeOf expr, ∀ {s : State} {expr' : Expr}, isJump c s → sizeOf expr' = m → P expr' s) :
  ∀ {s} {expr'}, isJump c s → sizeOf expr' < sizeOf expr → P expr' s := by aesop

/--
  Apply transitivity to obtain a nicer form for an `exec` inductive hypothesis.
-/
@[aesop unsafe 10% apply]
lemma exec_ih_trans {P : Stmt → State → Prop}
  (ih : ∀ m < sizeOf stmt, ∀ {s} {stmt'}, isJump c s → sizeOf stmt' = m → P stmt' s) :
  ∀ {s} {stmt'}, isJump c s → sizeOf stmt' < sizeOf stmt → P stmt' s := by aesop

@[aesop unsafe 10% apply]
lemma execPrimCall_evalArgs_Jump_ih
  (h : isJump c s)
  (hsize : sizeOf args < sizeOf expr)
  (eval_ih : ∀ {s} {expr'}, isJump c s → sizeOf expr' < sizeOf expr → isJump c (eval fuel expr' s).1) :
  isJump c (primCall (evalArgs fuel args s).1 prim (evalArgs fuel args s).2.reverse).1 := by
  apply execPrimCall_Jump (evalArgs_Jump_ih _ _ _) <;> aesop

/-- 
  An `eval` preserves infinite loops.
-/
@[aesop unsafe 10% apply]
lemma eval_Jump (h : isJump c s) : isJump c (eval fuel expr s).1 := by
  generalize hk : sizeOf expr = k
  rename' expr => expr'
  induction k using Nat.case_strong_induction_on generalizing s expr' with
  | hz =>
    rename' expr' => expr
    have : 0 < sizeOf expr := Expr.zero_lt_sizeOf
    rw [hk] at this
    linarith
  | hi k' ih =>
    rename' expr' => expr
    rw [forall_le_iff_forall_lt_succ] at ih
    rw [← hk] at ih
    clear hk
    unfold eval
    have ih₁ := @eval_ih_trans _ _ _ ih
    clear ih
    rcases expr with ⟨prim, args⟩ | ⟨f, args⟩ | var | val <;> simp only [Nat.add_eq, add_zero] <;> try aesop (config := { warnOnNonterminal := false})
    · unfold evalPrimCall
      apply execPrimCall_evalArgs_Jump_ih (expr := PrimCall prim args) <;> aesop
    · apply evalCall_Jump
      apply evalArgs_Jump_ih (expr := Call f args) <;> aesop

@[aesop unsafe 10% apply]
lemma evalTail_Jump_ih'
  {inputs : State × Literal}
  (h : isJump c inputs.1)
  (ih : ∀ {s : State}, isJump c s → isJump c (evalArgs fuel args s).1) :
  isJump c (evalTail fuel args inputs).1 := by unfold evalTail; aesop

@[aesop unsafe 10% apply]
lemma evalArgs_Jump
  (h : isJump c s) : isJump c (evalArgs fuel args s).1 := by
  induction args generalizing s with
    | nil => exact h
    | cons x xs ih => unfold evalArgs; aesop

/--
  Executing a call directly from `exec` preserves infinite loops.
-/
@[aesop unsafe 10% apply]
lemma Call_Jump (h : isJump c s) : isJump c (exec fuel (LetCall vars f args) s) :=
  LetCall'.symm ▸ execCall_Jump (evalArgs_Jump h)

/--
  Executing a call directly from `exec` preserves infinite loops.
-/
@[aesop unsafe 10% apply]
lemma AssignCall_Jump (h : isJump c s) : isJump c (exec fuel (AssignCall vars f args) s) :=
  AssignCall'.symm ▸ execCall_Jump (evalArgs_Jump h)

/--
  Executing a primop call directly from `exec` preserves infinite loops.
-/
@[aesop unsafe 10% apply]
lemma PrimCall_Jump (h : isJump c s) : isJump c (exec fuel (LetPrimCall vars prim args) s) := by
  rw [LetPrimCall']
  exact isJump_multifill (execPrimCall_Jump (evalArgs_Jump h))

/--
  Executing a primop call directly from `exec` preserves infinite loops.
-/
@[aesop unsafe 10% apply]
lemma AssignPrimCall_Jump (h : isJump c s) : isJump c (exec fuel (AssignPrimCall vars prim args) s) := by
  rw [AssignPrimCall']
  exact isJump_multifill (execPrimCall_Jump (evalArgs_Jump h))

/--
  Lets preserve infinite loops.
-/
@[aesop unsafe 10% apply]
lemma Let_Jump (h : isJump c s) : isJump c (exec fuel (Let vars) s) := by
  rw [Let']; induction vars <;> aesop

/--
  LetEqs preserve infinite loops.
-/
@[aesop unsafe 10% apply]
lemma LetEq_Jump (h : isJump c s) : isJump c (exec fuel (LetEq var rhs) s) := by rw [LetEq']; aesop

/--
  Assigns preserve infinite loops.
-/
@[aesop unsafe 10% apply]
lemma Assign_Jump (h : isJump c s) : isJump c (exec fuel (Assign var rhs) s) := by rw [Assign']; aesop

@[aesop unsafe 10% apply]
lemma ExprStmtCall_Jump (h : isJump c s) : isJump c (exec fuel (ExprStmtCall f args) s) :=
  ExprStmtCall'.symm ▸ execCall_Jump (evalArgs_Jump h)

@[aesop unsafe 10% apply]
lemma ExprStmtPrimCall_Jump (h : isJump c s) : isJump c (exec fuel (ExprStmtPrimCall prim args) s) := by
  rw [ExprStmtPrimCall']
  exact isJump_multifill (execPrimCall_Jump (evalArgs_Jump h))

@[aesop unsafe 10% apply]
lemma Block_Jump_ih
  (h : isJump c s)
  (exec_ih : ∀ {s : State} {stmt' : Stmt}, isJump c s → sizeOf stmt' < sizeOf (Block stmts) → isJump c (exec fuel stmt' s)) :
  isJump c (exec fuel (Block stmts) s) := by
  induction stmts generalizing s with
    | nil => aesop
    | cons x xs ih =>
      rw [cons]
      apply @ih (exec fuel x s) (exec_ih h Stmt.sizeOf_head_lt_sizeOf)
      intros s stmt hs hsize
      apply exec_ih hs
      aesop (config := { warnOnNonterminal := false}); linarith

/--
  Switch statements preserve infinite loops.
-/
@[aesop unsafe 10% apply]
lemma Switch_Jump
  (h : isJump c s)
  (hcases : sizeOf cases' < sizeOf stmt)
  (hdefault : sizeOf (Block default') < sizeOf stmt)
  (exec_ih : ∀ {s : State} {stmt' : Stmt}, isJump c s → sizeOf stmt' < sizeOf stmt → isJump c (exec fuel stmt' s)) :
  isJump c (exec fuel (Switch cond cases' default') s) := by
  rw [Switch']
  simp only
  unfold execSwitchCases
  induction cases' generalizing s with
  | nil =>
    aesop
  | cons x xs ih =>
    simp
    split_ifs with hif
    · refine' Block_Jump_ih (eval_Jump h) (λ {s stmt₁} hs hsize ↦ exec_ih hs _)
      rcases x with ⟨val, branch⟩
      simp at *
      linarith
    · unfold execSwitchCases
      apply ih h
      simp at *
      linarith

/--
  If statements preserve infinite loops.
-/
@[aesop unsafe 10% apply]
lemma If_Jump_ih
  (h : isJump c s)
  (hbody : sizeOf (Block body) < sizeOf stmt)
  (exec_ih : ∀ {s : State} {stmt' : Stmt}, isJump c s → sizeOf stmt' < sizeOf stmt → isJump c (exec fuel stmt' s)) :
  isJump c (exec fuel (Stmt.If cond body) s) := by rw [If']; aesop

/--
  For loops preserve infinite loops.
-/
@[aesop unsafe 10% apply]
lemma For_Jump (h : isJump c s) :
  isJump c (exec fuel (Stmt.For cond post body) s) := by rw [For']; aesop

/--
  An `exec` preserves infinite loops.
-/
@[aesop unsafe 10% apply]
lemma exec_Jump (h : isJump c s) : isJump c (exec fuel stmt s)
:= by
  generalize hk : sizeOf stmt = k
  rename' stmt => stmt'
  induction k using Nat.case_strong_induction_on generalizing s stmt' with
  | hz =>
    aesop
  | hi k' ih =>
    rename' stmt' => stmt
    rw [forall_le_iff_forall_lt_succ] at ih
    rw [← hk] at ih
    clear hk
    have ih₁ := @exec_ih_trans _ _ _ ih
    clear ih
    rcases stmt with
        stmts
      | var
      | ⟨var, rhs⟩
      | ⟨vars, f, args⟩
      | ⟨vars, prim, args⟩
      | ⟨var, rhs⟩
      | ⟨vars, f, args⟩
      | ⟨vars, prim, args⟩
      | ⟨f, args⟩
      | ⟨prim, args⟩
      | ⟨cond, cases', default'⟩
      | ⟨cond, post, body⟩
      | ⟨cond, body⟩ <;> try aesop (config := { warnOnNonterminal := false})
    · apply Switch_Jump (stmt := Switch cond cases' default') h (by simp_arith) _ (by aesop)
      rcases cases' <;> [aesop; (aesop (config := { warnOnNonterminal := false}); linarith)]
    · exact If_Jump_ih (stmt := If cond body) h (by simp_arith) (by rcases cond <;> aesop)
    · exact isJump_setContinue h
    · exact isJump_setBreak h
    · exact isJump_setLeave h

end

end Clear.JumpLemmas
