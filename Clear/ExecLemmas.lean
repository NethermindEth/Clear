import Clear.Interpreter

namespace Clear.ExecLemmas

open Clear Ast EVMState State Interpreter PrimOps

section

variable {s s' : State}
         {expr rhs cond : Expr}
         {args : List Expr}
         {prim : PrimOp}
         {stmt : Stmt}
         {stmts pre post body default': List Stmt}
         {fuel : ℕ}
         {var : String}
         {vars : List String}
         {fname : Identifier}
         {cases' : List (Literal × List Stmt)}
         {f : FunctionDefinition}

-- ============================================================================
--  EXEC LEMMAS
-- ============================================================================

section
unseal exec

-- | Executing a continue is the same as setting the `jump` field to `Continue`.
lemma Continue' : exec fuel .Continue s = 🔁 s := by rfl

-- | Executing a break is the same as setting the `jump` field to `Break`.
lemma Break' : exec fuel .Break s = 💔 s := by rfl

-- | Executing a `Leave` is the same as setting the `jump` field to `Leave`.
lemma Leave' : exec fuel .Leave s = 🚪 s := by rfl

end

-- | Executing a `Let` binds the given variable names with value 0.
lemma Let' : exec fuel (.Let vars) s = List.foldr (λ var s ↦ s.insert var 0) s vars := by unfold exec; rfl

-- | Executing a `LetEq` evaluates the RHS and binds the given variable name to the resulting literal.
lemma LetEq' : exec fuel (.LetEq var rhs) s =
  let (s', x) := eval fuel rhs s
  s'⟦var↦x⟧ := by unfold exec; rfl

-- | Executing an `Assign` evaluates the RHS and binds the given variable name to the resulting literal.
lemma Assign' : exec fuel (.Assign var rhs) s =
  let (s', x) := eval fuel rhs s
  s'⟦var↦x⟧ := by unfold exec; rfl

-- | Executing an `If` evaluates the condition and traverses the body if its nonzero (is the identity on states otherwise).
lemma If' : exec fuel (.If cond body) s =
  let (s, cond) := eval fuel cond s
  if cond ≠ 0
    then exec fuel (.Block body) s
    else s := by conv => lhs; unfold exec

-- | Executing a function call as a statement is the same as an assignment to an empty list of variables.
lemma ExprStmtCall' : exec fuel (.ExprStmtCall f args) s =
  execCall fuel f [] (reverse' (evalArgs fuel args.reverse s)) := by unfold exec; rfl

-- | Executing a primop call as a statement is the same as an assignment to an empty list of variables.
lemma ExprStmtPrimCall' : exec fuel (.ExprStmtPrimCall prim args) s =
  execPrimCall prim [] (reverse' (evalArgs fuel args.reverse s)) := by unfold exec; rfl

-- | Executing a `LetPrimCall` evaluates the arguments and calls the function, multifilling the return values.
lemma LetPrimCall' : exec fuel (.LetPrimCall vars prim args) s =
  execPrimCall prim vars (reverse' (evalArgs fuel args.reverse s)) := by unfold exec; rfl

-- | Executing a `AssignPrimCall` evaluates the arguments and calls the function, multifilling the return values.
lemma AssignPrimCall' : exec fuel (.AssignPrimCall vars prim args) s =
  execPrimCall prim vars (reverse' (evalArgs fuel args.reverse s)) := by unfold exec; rfl

-- | Executing a `LetCall` evaluates the arguments and calls the function, multifilling the return values.
lemma LetCall' : exec fuel (.LetCall vars f args) s =
  execCall fuel f vars (reverse' (evalArgs fuel args.reverse s)) := by unfold exec; rfl

-- | Executing an `AssignCall` evaluates the arguments and calls the function, multifilling the return values.
lemma AssignCall' : exec fuel (.AssignCall vars f args) s =
  execCall fuel f vars (reverse' (evalArgs fuel args.reverse s)) := by unfold exec; rfl

-- | Executing a `For` evaluates the condition, short-circuiting if its zero, and recursing otherwise.
lemma For' : exec fuel (.For cond post body) s =
  match fuel with
    | 0 => diverge s
    | 1 => diverge s
    | fuel + 1 + 1 =>
      let (s₁, x) := eval fuel cond (👌s)
      if x = 0
        then s₁✏️⟦s⟧?
        else
          let s₂ := exec fuel (.Block body) s₁
          match s₂ with
            | .OutOfFuel                      => s₂✏️⟦s⟧?
            | .Checkpoint (.Break _ _)      => 🧟s₂✏️⟦s⟧?
            | .Checkpoint (.Leave _ _)      => s₂✏️⟦s⟧?
            | .Checkpoint (.Continue _ _)
            | _ =>
              let s₃ := exec fuel (.Block post) (🧟 s₂)
              let s₄ := s₃✏️⟦s⟧?
              let s₅ := exec fuel (.For cond post body) s₄
              let s₆ := s₅✏️⟦s⟧?
              s₆ := by
  conv_lhs => unfold exec loop
  try rfl -- TODO(update Lean version): rfl is necessary in 4.8.0 because conv no longer does it

-- | Executing a `Switch` evaluates the condition, short-circuiting if its zero, and recursing otherwise.
lemma Switch' : exec fuel (.Switch cond cases' default') s =
      let (s₁, cond) := eval fuel cond s
      let branches := execSwitchCases fuel s₁ cases'
      let s₂ := exec fuel (.Block default') s₁
      List.foldr (λ (valᵢ, sᵢ) s ↦ if valᵢ = cond then sᵢ else s) s₂ branches
:= by conv => lhs; unfold exec; rfl

end

namespace Clear.ExecLemmas
