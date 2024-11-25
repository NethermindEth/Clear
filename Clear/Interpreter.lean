import Mathlib.Data.Finmap
import Mathlib.Init.Data.List.Lemmas

import Clear.Ast
import Clear.State
import Clear.PrimOps
import Clear.EVMState
import Clear.SizeLemmas

namespace Clear.Interpreter

open Clear Ast State PrimOps SizeLemmas

-- ============================================================================
--  INTERPRETER
-- ============================================================================

def head' : State × List Literal → State × Literal
  | (s, rets) => (s, List.head! rets)

def cons' (arg : Literal) : State × List Literal → State × List Literal
  | (s, args) => (s, arg :: args)

def reverse' : State × List Literal → State × List Literal
  | (s, args) => (s, args.reverse)

def multifill' (vars : List Identifier) : State × List Literal → State
  | (s, rets) => s.multifill vars rets

mutual
  def evalTail (fuel : Nat) (args : List Expr) : State × Literal → State × List Literal
    | (s, arg) => cons' arg (evalArgs fuel args s)
  termination_by _ => 1 + fuel + sizeOf args

  /--
    `evalArgs` evaluates a list of arguments.
  -/
  def evalArgs (fuel : Nat) (args : List Expr) (s : State) : State × List Literal :=
    match args with
      | [] => (s, [])
      | arg :: args =>
        evalTail fuel args (eval fuel arg s)
  termination_by fuel + sizeOf args
  decreasing_by
    all_goals simp_wf; try simp_arith
    try apply Expr.zero_lt_sizeOf

  /--
    `call` executes a call of a user-defined function.
  -/
  def call (fuel : Nat) (args : List Literal) (f : FunctionDefinition) (s : State) : State × List Literal :=
    let s₁ := 👌 initcall f.params args s
    let s₂ := exec fuel (.Block f.body) s₁
    let s₃ := reviveJump s₂ |>.overwrite? s |>.setStore s
    (s₃, List.map s₂.lookup! f.rets)
  termination_by fuel + sizeOf f
  decreasing_by
    all_goals simp_wf
    simp_arith
    apply FunctionDefinition.sizeOf_body_succ_lt_sizeOf

  -- Safe to call `List.head!` on return values, because the compiler throws an
  -- error when coarity is > 0 in (1) and when coarity is > 1 in all other
  -- cases.

  def evalPrimCall (prim : PrimOp) : State × List Literal → State × Literal
    | (s, args) => head' (primCall s prim args)

  def evalCall (fuel : Nat) (f : FunctionDefinition) : State × List Literal → State × Literal
    | (s, args) => head' (call fuel args f s)
  termination_by _ => 1 + fuel + sizeOf f

  def execPrimCall (prim : PrimOp) (vars : List Identifier) : State × List Literal → State
    | (s, args) => multifill' vars (primCall s prim args)

  def execCall (fuel : Nat) (f : FunctionDefinition) (vars : List Identifier) : State × List Literal → State
    | (s, args) => multifill' vars (call fuel args f s)
  termination_by _ => 1 + fuel + sizeOf f

  /--
    `execSwitchCases` executes each case of a `switch` statement.
  -/
  def execSwitchCases (fuel : Nat) (s : State) : List (Literal × List Stmt) → List (Literal × State)
    | [] => []
    | ((val, stmts) :: cases') => (val, exec fuel (.Block stmts) s) :: execSwitchCases fuel s cases'
  termination_by x => fuel + sizeOf x

  /--
    `eval` evaluates an expression.

    - calls evaluated here are assumed to have coarity 1
  -/
  def eval (fuel : Nat) (expr : Expr) (s : State) : State × Literal :=
    match expr with

      -- We hit these two cases (`PrimCall` and `Call`) when evaluating:
      --
      --  1. f()                 (expression statements)
      --  2. g(f())              (calls in function arguments)
      --  3. if f() {...}        (if conditions)
      --  4. for {...} f() ...   (for conditions)
      --  5. switch f() ...      (switch conditions)

      | .PrimCall prim args => evalPrimCall prim (reverse' (evalArgs fuel args.reverse s))
      | .Call f args        => evalCall fuel f (reverse' (evalArgs fuel args.reverse s))
      | .Var id             => (s, s[id]!!)
      | .Lit val            => (s, val)
  termination_by fuel + sizeOf expr
  decreasing_by
    all_goals
    simp_wf
    try simp_arith
    try apply Expr.zero_lt_sizeOf_List

  /--
    `exec` executs a single statement.
  -/
  def exec (fuel : Nat) (stmt : Stmt) (s : State) : State :=
    match stmt with
      | .Block [] => s
      | .Block (stmt :: stmts) =>
        let s₁ := exec fuel stmt s
        exec fuel (.Block stmts) s₁

      | .Let vars => List.foldr (λ var s ↦ s.insert var 0) s vars

      | .LetEq var rhs =>
        let (s, val) := eval fuel rhs s
        s.insert var val

      | .LetCall vars f args => execCall fuel f vars (reverse' (evalArgs fuel args.reverse s))

      | .LetPrimCall vars prim args => execPrimCall prim vars (reverse' (evalArgs fuel args.reverse s))

      | .Assign var rhs =>
        let (s, x) := eval fuel rhs s
        s.insert var x

      | .AssignCall vars f args => execCall fuel f vars (reverse' (evalArgs fuel args.reverse s))

      | .AssignPrimCall vars prim args => execPrimCall prim vars (reverse' (evalArgs fuel args.reverse s))

      | .If cond body =>
        let (s, cond) := eval fuel cond s
        if cond ≠ 0 then exec fuel (.Block body) s else s

      -- "Expressions that are also statements (i.e. at the block level) have
      -- to evaluate to zero values."
      --
      -- (https://docs.soliditylang.org/en/latest/yul.html#restrictions-on-the-grammar)
      --
      -- Thus, we cannot have literals or variables on the RHS.
      | .ExprStmtCall f args => execCall fuel f [] (reverse' (evalArgs fuel args.reverse s))
      | .ExprStmtPrimCall prim args => execPrimCall prim [] (reverse' (evalArgs fuel args.reverse s))

      | .Switch cond cases' default' =>

        let (s₁, cond) := eval fuel cond s
        let branches := execSwitchCases fuel s₁ cases'
        let s₂ := exec fuel (.Block default') s₁
        List.foldr (λ (valᵢ, sᵢ) s ↦ if valᵢ = cond then sᵢ else s) s₂ branches

      -- A `Break` or `Continue` in the pre or post is a compiler error,
      -- so we assume it can't happen and don't modify the state in these
      -- cases. (https://docs.soliditylang.org/en/v0.8.23/yul.html#loops)
      | .For cond post body => loop fuel cond post body s
      | .Continue => 🔁 s
      | .Break => 💔 s
      | .Leave => 🚪 s
  termination_by fuel + sizeOf stmt
  decreasing_by
    all_goals
    simp_wf
    try simp_arith
    try apply le_add_right
    try apply List.zero_lt_sizeOf
    try apply Expr.zero_lt_sizeOf
    try apply Expr.zero_lt_sizeOf_List

  /--
    `loop` executes a for-loop.
  -/
  def loop (fuel : Nat) (cond : Expr) (post body : List Stmt) (s : State) : State :=
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
                s₆
  termination_by fuel + sizeOf cond + sizeOf post + sizeOf body
  decreasing_by
    all_goals
    simp_wf
    simp_arith

end

notation "🍄" => exec
notation "🌸" => eval

section EXPERIMENTAL

inductive EvalOutcome where
  | EvO : EState -> Literal -> EvalOutcome
  | EvOutOfFuel : EvalOutcome
  | EvMalformed : EvalOutcome

inductive ExecOutcome where
  | ExO : EState -> ExecOutcome
  | ExB : EState -> ExecOutcome
  | ExC : EState -> ExecOutcome
  | ExL : EState -> ExecOutcome
  | ExOutOfFuel : ExecOutcome
  | ExMalformed : ExecOutcome

mutual

  def eEval (fuel : ℕ) (σ : EState) (e : Expr) : EvalOutcome :=
    match e with
    | .Lit v  => .EvO σ v
    | .Var id => .EvO σ (eLookup! σ id)
    | .Call f args =>
        eEvaleL fuel σ args
        (fun σ vals => eCalle fuel f σ vals)
    | _ => .EvMalformed
    termination_by (fuel + sizeOf e, 0)
    decreasing_by
      all_goals (
        simp_wf
        try simp_arith
      )
      apply Prod.Lex.left
      simp_arith
      apply Prod.Lex.left
      simp_arith



  -- def eEvalL (fuel : ℕ) (σ : EState) (es : List Expr) : EState × List Literal × EvalOutcome :=
  --   match es with
  --   | [] => (σ, [], .EvO default default)
  --   | e :: es₁ =>
  --     let oe := eEval fuel σ e
  --     match oe with
  --     | .EvO σ₁ v =>
  --       let (σf, vs, oes) := eEvalL fuel σ₁ es₁
  --       match oes with
  --       | .EvO _ _ => (σf, v :: vs, .EvO default default)
  --       | _ => (σ₁, v :: vs, oes)
  --     | _ => (σ, [], oe)
  --   termination_by fuel + sizeOf es
  --   decreasing_by
  --     all_goals
  --     simp_wf
  --     try simp_arith

  def eEvalL (fuel : ℕ) (σ : EState) (es : List Expr) : EState × List Literal × EvalOutcome :=
    match es with
    | [] => (σ, [], .EvO default default)
    | e :: es₁ =>
      let oe := eEval fuel σ e
      match oe with
      | .EvO σ₁ v =>
        let (σf, vs, oes) := eEvalL fuel σ₁ es₁
        match oes with
        | .EvO _ _ => (σf, v :: vs, .EvO default default)
        | _ => (σ₁, v :: vs, oes)
      | _ => (σ, [], oe)
    termination_by (fuel + sizeOf es, 0)
    decreasing_by
      all_goals
      simp_wf
      try simp_arith
      apply Prod.Lex.left
      simp_arith

  def eEvaleL (fuel : ℕ) (σ : EState) (es : List Expr) (f : EState → List Literal → EvalOutcome) : EvalOutcome :=
    let (σ, vs, o) := eEvalL fuel σ es
    match o with
    | .EvO _ _ => f σ vs
    | _ => o
  termination_by (fuel + sizeOf es, 1)

  -- def eEvaleL (fuel : ℕ) (σ : EState) (es : List Expr) (f : EState → List Literal → EvalOutcome) : EvalOutcome :=
  --   match fuel with
  --   | 0 => .EvOutOfFuel
  --   | fuel + 1 =>
  --     let (σ, vs, o) := eEvalL fuel σ es
  --     match o with
  --     | .EvO _ _ => f σ vs
  --     | _ => o
  --   termination_by fuel + sizeOf es

  def eEvalx (fuel : ℕ) (σ : EState) (e : Expr) (f : EState → Literal → ExecOutcome) : ExecOutcome :=
    match fuel with
    | 0 => .ExOutOfFuel
    | fuel + 1 =>
      match eEval fuel σ e with
      | .EvO σ v => f σ v
      | .EvOutOfFuel => .ExOutOfFuel
      | .EvMalformed => .ExMalformed
    termination_by (fuel + sizeOf e, 0)

  def eEvalxL (fuel : ℕ) (σ : EState) (es : List Expr) (f : EState → List Literal → ExecOutcome) : ExecOutcome :=
    match fuel with
    | 0 => .ExOutOfFuel
    | fuel + 1 =>
      let (σ, vs, o) := eEvalL fuel σ es
      match o with
      | .EvO _ _ => f σ vs
      | .EvOutOfFuel => .ExOutOfFuel
      | .EvMalformed => .ExMalformed
    termination_by (fuel + sizeOf es, 0)

  def eCalle
    (fuel : Nat)
    (f : FunctionDefinition)
    (σ : EState)
    (args : List Literal) : EvalOutcome :=
      let store := σ.2
      let σ₁ := eInitCall σ f.params args
      let ob := eExec fuel σ₁ (.Block f.body)
      match ob with
      | .ExO σ₂ | .ExL σ₂ =>
          let rets : List Literal := List.map (eLookup! σ₂) f.rets
          let σ₃ := eSetStore σ₂ store
          .EvO σ₃ (List.head! rets)
      | .ExOutOfFuel => .EvOutOfFuel
      | _ => .EvMalformed
    termination_by (fuel + sizeOf f, 0)
    decreasing_by
      all_goals simp_wf
      simp_arith
      simp_wf
      apply Prod.Lex.left
      simp_arith
      apply FunctionDefinition.sizeOf_body_succ_lt_sizeOf

  def eCallx
    (fuel : Nat)
    (f : FunctionDefinition)
    (σ : EState)
    (vars : List Identifier)
    (args : List Literal) : ExecOutcome :=
      let store := σ.2
      let σ₁ := eInitCall σ f.params args
      let ob := eExec fuel σ₁ (.Block f.body)
      match ob with
      | .ExO σ₂ | .ExL σ₂ =>
          let rets : List Literal := List.map (eLookup! σ₂) f.rets
          let σ₃ := eSetStore σ₂ store
          .ExO (eMultiFill σ₃ vars rets)
      | .ExOutOfFuel => .ExOutOfFuel
      | _ => .ExMalformed
    termination_by (fuel + sizeOf f, 0)
    decreasing_by
      all_goals simp_wf
      simp_arith
      apply Prod.Lex.left
      simp_arith
      apply FunctionDefinition.sizeOf_body_succ_lt_sizeOf

  def eExec (fuel : ℕ) (σ : EState) (s : Stmt) : ExecOutcome :=
    match s with
      -- break, continue, and leave simply set the appropriate outcome type
      | .Break => .ExB σ
      | .Continue => .ExC σ
      | .Leave => .ExL σ

      | .Block [] => .ExO σ
      | .Block (s :: stmts) =>
          let os := eExec fuel σ s
          -- sequence shortcuts everything except ok
          match os with
          | .ExO σ => eExec fuel σ (.Block stmts)
          | _ => os

      | .Let vars =>
        .ExO (List.foldl (λ σ var ↦ eInsert σ var 0) σ vars)

      | .LetEq var e
      | .Assign var e =>
        eEvalx fuel σ e
        (fun σ v => .ExO (eInsert σ var v))

      | .If cond body =>
        eEvalx fuel σ cond
        (fun σ v => if v ≠ 0 then eExec fuel σ (.Block body) else .ExO σ)

      | .Switch cond cases dflt =>
        eEvalx fuel σ cond
        (fun σ case =>
          let stmts : List Stmt :=
            List.foldl (λ s (caseᵢ, stmtsᵢ) ↦ if caseᵢ = case then stmtsᵢ else s) dflt cases
          eExec fuel σ (.Block stmts))

      | .LetCall    vars f args
      | .AssignCall vars f args =>
        eEvalxL fuel σ args
        (fun σ vals => eCallx fuel f σ vars vals)

      | .ExprStmtCall f args =>
        eEvalxL fuel σ args
        (fun σ vals => eCallx fuel f σ [] vals)

      | .For cond post body =>
        match fuel with
          -- out of fuel
          | 0 => .ExOutOfFuel
          -- there still is fuel
          | fuel + 1 =>
            eEvalx fuel σ cond
            (fun σ v =>
              if v = 0
                -- loop condition false, exit loop
                then .ExO σ
                else
                  -- loop condition true, execute body
                  let ob := eExec fuel σ (.Block body)
                  match ob with
                  -- ok and continue proceed to the next iteration
                  | .ExO σ | .ExC σ =>
                    -- execute post
                    let op := eExec fuel σ (.Block post)
                    match op with
                    -- execute next iteration
                    | .ExO σ => eExec fuel σ (.For cond post body)
                    -- out of fuel propagates
                    | .ExOutOfFuel => .ExOutOfFuel
                    -- everything else (break, continue, leave, malformed) is malformed
                    | _ => .ExMalformed
                  -- break changes to ok and shortcuts
                  | .ExB σ => .ExO σ
                  -- everything else shortcuts
                  | _ => ob)

      | _ => .ExMalformed
      termination_by (fuel + sizeOf s, 0)
      decreasing_by
        all_goals (simp_wf; try simp_arith)
        all_goals (apply Prod.Lex.left; simp_arith)
        rcases cond <;> simp_arith        

end

end EXPERIMENTAL

section

open EVMState

variable {s s₀ s₁ : State}
         {arg expr rhs cond : Expr}
         {args : List Expr}
         {evm : EVM}
         {store : VarStore}
         {stmt : Stmt}
         {stmts pre body post rest : List Stmt}
         {fuel m n k : ℕ}
         {var var' fname : String}
         {x : Literal}
         {xs : List Literal}
         {f : FunctionDefinition}
         {prim : PrimOp}

-- ============================================================================
--  TRAVERSE LEMMAS
-- ============================================================================

section
unseal exec

/-
  Traversing an empty list is the identity on states.
-/
@[simp]
lemma nil : exec fuel (.Block []) s = s := by rfl

/--
  Traversing a nonempty list is the same traversing the tail from the state yielded from executing the head.
-/
lemma cons : exec fuel (.Block (stmt :: stmts)) s = exec fuel (.Block stmts) (exec fuel stmt s) := by
  conv_lhs => unfold exec

end

-- ============================================================================
--  EVAL LEMMAS
-- ============================================================================

section
unseal eval

/--
  Evaluating a literal gives you back that literal and the state you started in.
-/
lemma Lit' : eval fuel (.Lit x) s = (s, x) := by rfl

/--
  Evaluating a variable does a varstore lookup.
-/
lemma Var' : eval fuel (.Var var) s = (s, s[var]!!) := by rfl

end

/--
  A call in an expression.
-/
lemma Call' : eval fuel (.Call f args) s = evalCall fuel f (reverse' (evalArgs fuel args.reverse s)) := by unfold eval; rfl

/--
  Evaluating an EVM builtin evaluates the arguments, calls the builtin on
the resulting literals, and then returns the resulting state and the first
literal return value.
-/
lemma PrimCall' : eval fuel (.PrimCall prim args) s = evalPrimCall prim (reverse' (evalArgs fuel args.reverse s)) := by unfold eval; rfl

-- ============================================================================
--  HELPER FUNCTION LEMMAS
-- ============================================================================

/--
  Executing a user-defined function with the `call` interpreter helper
  function loads all the arguments and return variables into the varstore,
  traverses the body, restores the saved checkpoint to the top-level.
-/
lemma call_def : call fuel xs f s =
  let s₁ := 👌 initcall f.params xs s
  let s₂ := exec fuel (.Block f.body) s₁
  let s₃ := reviveJump s₂ |>.overwrite? s |>.setStore s
  (s₃, List.map s₂.lookup! f.rets) := by unfold call; rfl

@[simp]
lemma evalTail_nil : evalTail fuel [] (s, x) = (s, [x]) := by
  conv_lhs => unfold evalTail cons' evalArgs

@[simp]
lemma evalTail_cons : evalTail fuel (arg :: args) (s, x) =
  match evalTail fuel args (🌸 fuel arg s) with
    | (s, args) => (s, x :: args) := by conv_lhs => unfold evalTail cons' evalArgs

end

end Clear.Interpreter
