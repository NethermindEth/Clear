import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.panic_error_0x41


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def if_9222169807163418225 := <s
  if _8 
{panic_error_0x41()}
>

set_option maxRecDepth 5000
set_option maxHeartbeats 400000

def if_9222169807163418225_concrete_of_code : {
    C : State → State → Prop
    // ∀ {s₀ s₉ fuel}
    , exec fuel if_9222169807163418225 s₀ = s₉
    → Spec C s₀ s₉
  } := by
  constructor
  intros s₀ s₉ fuel

  unfold Spec if_9222169807163418225
  rcases s₀ with ⟨evm₀, store₀⟩ | _ | c <;> dsimp only
  rotate_left 1
  · generalize If _ _ = f; aesop
  · generalize If _ _ = f; aesop
  swap
  generalize hok : Ok evm₀ store₀ = s₀
  intros h _
  revert h

  rw [If']

  -- AST-specific tactics

  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  -- simp [Var']
  rw [cons, ExprStmtCall']; try simp only
  (try (simp only [Fin.isValue])); (try (rw [List.foldr_cons])); (try (rw [List.foldr_nil])); simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]; (try (rewrite [List.foldr_nil]))
  try simp
  
  generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs
  intros h
  try intros h'
  refine' Exists.intro s (And.intro (panic_error_0x41_abs_of_code hs) ?_)
  swap; clear hs
  try revert h'
  revert h
  
  
  
  -- tacticsOfStmt offsetting
  try rw [nil]
  try simp [Bool.toUInt256, UInt256.size]
  intros h
  exact h


end

end ERC20Shim.Common
