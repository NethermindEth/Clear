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
  | O (σ : EState) (v : Literal)
  | OutOfFuel
  | Malformed

inductive EvalLOutcome where
  | O (σ : EState) (l : List Literal)
  | OutOfFuel
  | Malformed

inductive ExecOutcome where
  | O (σ : EState)
  | B (σ : EState)
  | C (σ : EState)
  | L (σ : EState)
  | OutOfFuel
  | Malformed

namespace EvalOutcome

def mapD { T : Type } (o : EvalOutcome) (defOOF : T) (defM : T) (f : EState -> Literal -> T) : T :=
  match o with
  | .O σ v => f σ v
  | .OutOfFuel => defOOF
  | .Malformed => defM

def map := mapD (defOOF := EvalOutcome.OutOfFuel) (defM := .Malformed)
def mapExecOutcome := mapD (defOOF := ExecOutcome.OutOfFuel) (defM := .Malformed)
def mapEvalLOutcome := mapD (defOOF := EvalLOutcome.OutOfFuel) (defM := .Malformed)

end EvalOutcome

namespace EvalLOutcome

def mapD { T : Type } (o : EvalLOutcome) (defOOF : T) (defM : T) (f : EState -> List Literal -> T) : T :=
  match o with
  | .O σ vs => f σ vs
  | .OutOfFuel => defOOF
  | .Malformed => defM

def map := mapD (defOOF := EvalLOutcome.OutOfFuel) (defM := .Malformed)
def mapEvalOutcome := mapD (defOOF := EvalOutcome.OutOfFuel) (defM := .Malformed)
def mapExecOutcome := mapD (defOOF := ExecOutcome.OutOfFuel) (defM := .Malformed)

end EvalLOutcome

def lookup (σ : EState) (var : Identifier) : EvalOutcome :=
  ((σ.eLookup var).map (EvalOutcome.O σ ·)).getD .Malformed

def lookupL (σ : EState) (vars : List Identifier) : EvalLOutcome :=
    match vars with
    | [] => .O σ []
    | var :: vars =>
      (lookup σ var).mapEvalLOutcome
      (λ σ v => (lookupL σ vars).map (λ σ vs => .O σ (v :: vs)))

mutual

  def eEval (fuel : ℕ) (σ : EState) (e : Expr) : EvalOutcome :=
    match e with
    | .Lit v  => .O σ v
    | .Var id => lookup σ id
    | .Call f args =>
        -- expression function calls must return precisely one value
        if (f.rets.length = 1) then
          -- Yul semantics evaluates arguments right-to-left
          (eEvalL fuel σ args.reverse).mapEvalOutcome
          (eCalle fuel f · ·.reverse)
        else
          .Malformed
    -- Not implemented
    | _ => .Malformed
    termination_by (fuel + sizeOf e, 0)
    decreasing_by
      all_goals
      simp_wf
      apply Prod.Lex.left
      simp_arith

  def eEvalL (fuel : ℕ) (σ : EState) (es : List Expr) : EvalLOutcome :=
    match es with
    | [] => .O σ []
    | e :: es =>
      (eEval fuel σ e).mapEvalLOutcome
      (λ σ v => (eEvalL fuel σ es).map (λ σ vs => .O σ (v :: vs)))
    termination_by (fuel + sizeOf es, 0)
    decreasing_by
      all_goals
      simp_wf
      apply Prod.Lex.left
      simp_arith

  def eCall
    { T : Type }
    (fuel : Nat)
    (funDef : FunctionDefinition)
    (σ : EState)
    (args : List Literal)
    (defOOF : T)
    (defM : T)
    (f : EState -> T) : T :=
      let σ₁ := σ.eInitCall funDef.params args
      let ob := eExec fuel σ₁ (.Block funDef.body)
      match ob with
      -- Ok and Leave outcomes are ok for function calls
      | .O σ₂ | .L σ₂ => f σ₂
      | .OutOfFuel => defOOF
      -- Break, Continue, and Malformed outcomes are malformed
      | .B .. | .C .. | .Malformed => defM
    termination_by (fuel + sizeOf funDef, 0)
    decreasing_by
      all_goals simp_wf
      simp_arith
      apply Prod.Lex.left
      simp_arith
      apply FunctionDefinition.sizeOf_body_succ_lt_sizeOf

  def eCalle
    (fuel : Nat)
    (f : FunctionDefinition)
    (σ : EState)
    (args : List Literal) : EvalOutcome :=
      let store := σ.store
      eCall fuel f σ args .OutOfFuel .Malformed
      (λ σ₁ =>
        -- expression function calls must return precisely one value
        match f.rets with
        | [] => .Malformed
        | [ ret ] =>
          (lookup σ₁ ret).map
          (λ σ₂ v =>
            let σ₃ := σ₂.eSetStore store
            .O σ₃ v)
        | _ :: _ => .Malformed)
    termination_by (fuel + sizeOf f, 1)

  def eCallx
    (fuel : Nat)
    (f : FunctionDefinition)
    (σ : EState)
    (vars : List Identifier)
    (args : List Literal) : ExecOutcome :=
      let store := σ.store
      eCall fuel f σ args .OutOfFuel .Malformed
      (λ σ₁ =>
        (lookupL σ₁ f.rets).mapExecOutcome
        (λ σ₂ rets =>
          let σ₃ := σ₂.eSetStore store
          .O <| σ₃.eMultiFill vars rets))
    termination_by (fuel + sizeOf f, 1)

  def eExec (fuel : ℕ) (σ : EState) (s : Stmt) : ExecOutcome :=
    match s with
      -- break, continue, and leave simply set the appropriate outcome type
      | .Break => .B σ
      | .Continue => .C σ
      | .Leave => .L σ

      | .Block [] => .O σ
      | .Block (s :: stmts) =>
          let os := eExec fuel σ s
          -- sequence shortcuts everything except ok
          match os with
          | .O σ => eExec fuel σ (.Block stmts)
          | .B .. | .C .. | .L .. | .OutOfFuel | .Malformed => os

      | .Let vars =>
        .O <| vars.foldl (init := σ) (EState.eInsert · · 0)

      | .LetEq var e
      | .Assign var e =>
        (eEval fuel σ e).mapExecOutcome
        (λ σ v => .O (EState.eInsert σ var v))

      | .If cond body =>
        (eEval fuel σ cond).mapExecOutcome
        (λ σ v => if v ≠ 0 then eExec fuel σ (.Block body) else .O σ)

      | .Switch cond cases dflt =>
        (eEval fuel σ cond).mapExecOutcome
        (λ σ case =>
          let stmts := cases.foldl (init := dflt)
                       (λ s (caseᵢ, stmtsᵢ) ↦ if caseᵢ = case then stmtsᵢ else s)
          eExec fuel σ (.Block stmts))

      | .LetCall    vars f args
      | .AssignCall vars f args =>
        if vars.length = f.rets.length then
          (eEvalL fuel σ args.reverse).mapExecOutcome
          (λ σ vals => eCallx fuel f σ vars vals.reverse)
        else
          .Malformed

      | .ExprStmtCall f args =>
        if f.rets.length = 0 then
          (eEvalL fuel σ args.reverse).mapExecOutcome
          (λ σ vals => eCallx fuel f σ [] vals.reverse)
        else
          .Malformed

      | .For cond post body =>
        match fuel with
          -- out of fuel
          | 0 => .OutOfFuel
          -- there still is fuel
          | fuel + 1 =>
            (eEval fuel σ cond).mapExecOutcome
            (λ σ v =>
              if v = 0
                -- loop condition false, exit loop
                then .O σ
                else
                  -- loop condition true, execute body
                  let ob := eExec fuel σ (.Block body)
                  match ob with
                  -- ok and continue proceed to the next iteration
                  | .O σ | .C σ =>
                    -- execute post
                    let op := eExec fuel σ (.Block post)
                    match op with
                    -- execute next iteration
                    | .O σ => eExec fuel σ (.For cond post body)
                    -- out of fuel propagates
                    | .OutOfFuel => .OutOfFuel
                    -- everything else (break, continue, leave, malformed) is malformed
                    | .B .. | .C .. | .L .. | .Malformed => .Malformed
                  -- break changes to ok and shortcuts
                  | .B σ => .O σ
                  -- everything else shortcuts
                  | .L .. | .OutOfFuel | .Malformed => ob)
      -- Not implemented
      | _ => .Malformed
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
